/***************************************************************************
 *                                  _   _ ____  _
 *  Project                     ___| | | |  _ \| |
 *                             / __| | | | |_) | |
 *                            | (__| |_| |  _ <| |___
 *                             \___|\___/|_| \_\_____|
 *
 * Copyright (C) Daniel Stenberg, <daniel@haxx.se>, et al.
 *
 * This software is licensed as described in the file COPYING, which
 * you should have received as part of this distribution. The terms
 * are also available at https://curl.se/docs/copyright.html.
 *
 * You may opt to use, copy, modify, merge, publish, distribute and/or sell
 * copies of the Software, and permit persons to whom the Software is
 * furnished to do so, under the terms of the COPYING file.
 *
 * This software is distributed on an "AS IS" basis, WITHOUT WARRANTY OF ANY
 * KIND, either express or implied.
 *
 * SPDX-License-Identifier: curl
 *
 ***************************************************************************/

#include "curl_setup.h"

#if defined(USE_LINUX_QUIC) && defined(USE_NGHTTP3)
#include <nghttp3/nghttp3.h>

#include "urldata.h"
#include "hash.h"
#include "sendf.h"
#include "strdup.h"
#include "rand.h"
#include "multiif.h"
#include "strcase.h"
#include "cfilters.h"
#include "cf-socket.h"
#include "connect.h"
#include "progress.h"
#include "strerror.h"
#include "dynbuf.h"
#include "http1.h"
#include "select.h"
#include "inet_pton.h"
#include "transfer.h"
#include "vquic.h"
#include "vquic_int.h"
#include "vquic-tls.h"
#include "vtls/keylog.h"
#include "vtls/vtls.h"
#include "curl_ngtcp2.h"

#include "warnless.h"

/* The last 3 #include files should be in this order */
#include "curl_printf.h"
#include "curl_memory.h"
#include "memdebug.h"

struct cf_linuxq_ctx {
  struct cf_quic_ctx q;
  struct ssl_peer peer;
  struct curl_tls_ctx tls;
  int qconn;
  uint32_t version;
  struct cf_call_data call_data;
  nghttp3_conn *h3conn;
  nghttp3_settings h3settings;
  struct curltime started_at;        /* time the current attempt started */
  struct curltime handshake_at;      /* time connect handshake finished */
  struct curltime reconnect_at;      /* time the next attempt should start */
  struct bufc_pool stream_bufcp;     /* chunk pool for streams */
  struct dynbuf scratch;             /* temp buffer for header construction */
  struct Curl_hash streams;          /* hash `data->id` to `h3_stream_ctx` */
  size_t max_stream_window;          /* max flow window for one stream */
  uint64_t max_idle_ms;              /* max idle time for QUIC connection */
  uint64_t used_bidi_streams;        /* bidi streams we have opened */
  uint64_t max_bidi_streams;         /* max bidi streams we can open */
  int qlogfd;
  BIT(shutdown_started);             /* queued shutdown packets */
};

/**
 * All about the H3 internals of a stream
 */
struct h3_stream_ctx {
  curl_int64_t id; /* HTTP/3 protocol identifier */
  struct bufq sendbuf;   /* h3 request body */
  struct h1_req_parser h1; /* h1 request parsing */
  size_t sendbuf_len_in_flight; /* sendbuf amount "in flight" */
  size_t upload_blocked_len; /* the amount written last and EGAINed */
  curl_uint64_t error3; /* HTTP/3 stream error code */
  curl_off_t upload_left; /* number of request bytes left to upload */
  int status_code; /* HTTP status code */
  CURLcode xfer_result; /* result from xfer_resp_write(_hd) */
  bool resp_hds_complete; /* we have a complete, final response */
  bool closed; /* TRUE on stream close */
  bool reset;  /* TRUE on stream reset */
  bool send_closed; /* stream is local closed */
  BIT(quic_flow_blocked); /* stream is blocked by QUIC flow control */
};

#define H3_STREAM_CTX(ctx,data)   ((struct h3_stream_ctx *)(\
            data? Curl_hash_offt_get(&(ctx)->streams, (data)->id) : NULL))
#define H3_STREAM_CTX_ID(ctx,id)  ((struct h3_stream_ctx *)(\
            Curl_hash_offt_get(&(ctx)->streams, (id))))

static void h3_stream_ctx_free(struct h3_stream_ctx *stream)
{
  Curl_bufq_free(&stream->sendbuf);
  Curl_h1_req_parse_free(&stream->h1);
  free(stream);
}

static void h3_stream_hash_free(void *stream)
{
  DEBUGASSERT(stream);
  h3_stream_ctx_free((struct h3_stream_ctx *)stream);
}

static CURLcode h3_data_setup(struct Curl_cfilter *cf,
                              struct Curl_easy *data)
{
  struct cf_linuxq_ctx *ctx = cf->ctx;
  struct h3_stream_ctx *stream = H3_STREAM_CTX(ctx, data);

  if(!data) {
    failf(data, "initialization failure, transfer not http initialized");
    return CURLE_FAILED_INIT;
  }

  if(stream)
    return CURLE_OK;

  stream = calloc(1, sizeof(*stream));
  if(!stream)
    return CURLE_OUT_OF_MEMORY;

  stream->id = -1;
  /* on send, we control how much we put into the buffer */
  Curl_bufq_initp(&stream->sendbuf, &ctx->stream_bufcp,
                  H3_STREAM_SEND_CHUNKS, BUFQ_OPT_NONE);
  stream->sendbuf_len_in_flight = 0;
  Curl_h1_req_parse_init(&stream->h1, H1_PARSE_DEFAULT_MAX_LINE_LEN);

  if(!Curl_hash_offt_set(&ctx->streams, data->id, stream)) {
    h3_stream_ctx_free(stream);
    return CURLE_OUT_OF_MEMORY;
  }

  return CURLE_OK;
}

static void h3_data_done(struct Curl_cfilter *cf, struct Curl_easy *data)
{
  struct cf_linuxq_ctx *ctx = cf->ctx;
  struct h3_stream_ctx *stream = H3_STREAM_CTX(ctx, data);
  (void)cf;
  if(stream) {
    CURL_TRC_CF(data, cf, "[%" CURL_PRId64 "] easy handle is done",
                stream->id);
    //cf_ngtcp2_stream_close(cf, data, stream);
    Curl_hash_offt_remove(&ctx->streams, data->id);
  }
}

static struct Curl_easy *get_stream_easy(struct Curl_cfilter *cf,
                                         struct Curl_easy *data,
                                         int64_t stream_id,
                                         struct h3_stream_ctx **pstream)
{
  struct cf_linuxq_ctx *ctx = cf->ctx;
  struct Curl_easy *sdata;
  struct h3_stream_ctx *stream;

  (void)cf;
  stream = H3_STREAM_CTX(ctx, data);
  if(stream && stream->id == stream_id) {
    *pstream = stream;
    return data;
  }
  else {
    DEBUGASSERT(data->multi);
    for(sdata = data->multi->easyp; sdata; sdata = sdata->next) {
      if(sdata->conn != data->conn)
        continue;
      stream = H3_STREAM_CTX(ctx, sdata);
      if(stream && stream->id == stream_id) {
        *pstream = stream;
        return sdata;
      }
    }
  }
  *pstream = NULL;
  return NULL;
}

static void h3_drain_stream(struct Curl_cfilter *cf,
                            struct Curl_easy *data)
{
  struct cf_linuxq_ctx *ctx = cf->ctx;
  struct h3_stream_ctx *stream = H3_STREAM_CTX(ctx, data);
  unsigned char bits;

  (void)cf;
  bits = CURL_CSELECT_IN;
  if(stream && stream->upload_left && !stream->send_closed)
    bits |= CURL_CSELECT_OUT;
  if(data->state.select_bits != bits) {
    data->state.select_bits = bits;
    Curl_expire(data, 0, EXPIRE_RUN_NOW);
  }
}

static int cb_h3_stream_close(nghttp3_conn *conn, int64_t sid,
                              uint64_t app_error_code, void *user_data,
                              void *stream_user_data)
{
  struct Curl_cfilter *cf = user_data;
  struct cf_linuxq_ctx *ctx = cf->ctx;
  struct Curl_easy *data = stream_user_data;
  curl_int64_t stream_id = (curl_int64_t)sid;
  struct h3_stream_ctx *stream = H3_STREAM_CTX(ctx, data);
  (void)conn;
  (void)stream_id;

  /* we might be called by nghttp3 after we already cleaned up */
  if(!stream)
    return 0;

  stream->closed = TRUE;
  stream->error3 = (curl_uint64_t)app_error_code;
  if(stream->error3 != NGHTTP3_H3_NO_ERROR) {
    stream->reset = TRUE;
    stream->send_closed = TRUE;
    CURL_TRC_CF(data, cf, "[%" CURL_PRId64 "] RESET: error %" CURL_PRIu64,
                stream->id, stream->error3);
  }
  else {
    CURL_TRC_CF(data, cf, "[%" CURL_PRId64 "] CLOSED", stream->id);
  }
  h3_drain_stream(cf, data);
  return 0;
}

static void h3_xfer_write_resp_hd(struct Curl_cfilter *cf,
                                  struct Curl_easy *data,
                                  struct h3_stream_ctx *stream,
                                  const char *buf, size_t blen, bool eos)
{

  /* If we already encountered an error, skip further writes */
  if(!stream->xfer_result) {
    stream->xfer_result = Curl_xfer_write_resp_hd(data, buf, blen, eos);
    if(stream->xfer_result)
      CURL_TRC_CF(data, cf, "[%"CURL_PRId64"] error %d writing %zu "
                  "bytes of headers", stream->id, stream->xfer_result, blen);
  }
}

static void h3_xfer_write_resp(struct Curl_cfilter *cf,
                               struct Curl_easy *data,
                               struct h3_stream_ctx *stream,
                               const char *buf, size_t blen, bool eos)
{

  /* If we already encountered an error, skip further writes */
  if(!stream->xfer_result) {
    stream->xfer_result = Curl_xfer_write_resp(data, buf, blen, eos);
    /* If the transfer write is errored, we do not want any more data */
    if(stream->xfer_result) {
      CURL_TRC_CF(data, cf, "[%"CURL_PRId64"] error %d writing %zu bytes "
                  "of data", stream->id, stream->xfer_result, blen);
    }
  }
}

static int cb_h3_recv_data(nghttp3_conn *conn, int64_t stream3_id,
                           const uint8_t *buf, size_t blen,
                           void *user_data, void *stream_user_data)
{
  struct Curl_cfilter *cf = user_data;
  struct cf_linuxq_ctx *ctx = cf->ctx;
  struct Curl_easy *data = stream_user_data;
  struct h3_stream_ctx *stream = H3_STREAM_CTX(ctx, data);

  (void)conn;
  (void)stream3_id;

  if(!stream)
    return NGHTTP3_ERR_CALLBACK_FAILURE;

  h3_xfer_write_resp(cf, data, stream, (char *)buf, blen, FALSE);
  if(blen) {
    CURL_TRC_CF(data, cf, "[%" CURL_PRId64 "] ACK %zu bytes of DATA",
                stream->id, blen);
    //ngtcp2_conn_extend_max_stream_offset(ctx->qconn, stream->id, blen);
    //ngtcp2_conn_extend_max_offset(ctx->qconn, blen);
  }
  CURL_TRC_CF(data, cf, "[%" CURL_PRId64 "] DATA len=%zu", stream->id, blen);
  return 0;
}

static int cb_h3_deferred_consume(nghttp3_conn *conn, int64_t stream3_id,
                                  size_t consumed, void *user_data,
                                  void *stream_user_data)
{
  struct Curl_cfilter *cf = user_data;
  struct cf_linuxq_ctx *ctx = cf->ctx;
  (void)conn;
  (void)stream_user_data;

  /* nghttp3 has consumed bytes on the QUIC stream and we need to
   * tell the QUIC connection to increase its flow control */
  //ngtcp2_conn_extend_max_stream_offset(ctx->qconn, stream3_id, consumed);
  //ngtcp2_conn_extend_max_offset(ctx->qconn, consumed);
  return 0;
}

static int cb_h3_end_headers(nghttp3_conn *conn, int64_t sid,
                             int fin, void *user_data, void *stream_user_data)
{
  struct Curl_cfilter *cf = user_data;
  struct cf_linuxq_ctx *ctx = cf->ctx;
  struct Curl_easy *data = stream_user_data;
  curl_int64_t stream_id = (curl_int64_t)sid;
  struct h3_stream_ctx *stream = H3_STREAM_CTX(ctx, data);
  (void)conn;
  (void)stream_id;
  (void)fin;
  (void)cf;

  if(!stream)
    return 0;
  /* add a CRLF only if we have received some headers */
  h3_xfer_write_resp_hd(cf, data, stream, STRCONST("\r\n"), stream->closed);

  CURL_TRC_CF(data, cf, "[%" CURL_PRId64 "] end_headers, status=%d",
              stream_id, stream->status_code);
  if(stream->status_code / 100 != 1) {
    stream->resp_hds_complete = TRUE;
  }
  h3_drain_stream(cf, data);
  return 0;
}

static int cb_h3_recv_header(nghttp3_conn *conn, int64_t sid,
                             int32_t token, nghttp3_rcbuf *name,
                             nghttp3_rcbuf *value, uint8_t flags,
                             void *user_data, void *stream_user_data)
{
  struct Curl_cfilter *cf = user_data;
  struct cf_linuxq_ctx *ctx = cf->ctx;
  curl_int64_t stream_id = (curl_int64_t)sid;
  nghttp3_vec h3name = nghttp3_rcbuf_get_buf(name);
  nghttp3_vec h3val = nghttp3_rcbuf_get_buf(value);
  struct Curl_easy *data = stream_user_data;
  struct h3_stream_ctx *stream = H3_STREAM_CTX(ctx, data);
  CURLcode result = CURLE_OK;
  (void)conn;
  (void)stream_id;
  (void)token;
  (void)flags;
  (void)cf;

  /* we might have cleaned up this transfer already */
  if(!stream)
    return 0;

  if(token == NGHTTP3_QPACK_TOKEN__STATUS) {

    result = Curl_http_decode_status(&stream->status_code,
                                     (const char *)h3val.base, h3val.len);
    if(result)
      return -1;
    Curl_dyn_reset(&ctx->scratch);
    result = Curl_dyn_addn(&ctx->scratch, STRCONST("HTTP/3 "));
    if(!result)
      result = Curl_dyn_addn(&ctx->scratch,
                             (const char *)h3val.base, h3val.len);
    if(!result)
      result = Curl_dyn_addn(&ctx->scratch, STRCONST(" \r\n"));
    if(!result)
      h3_xfer_write_resp_hd(cf, data, stream, Curl_dyn_ptr(&ctx->scratch),
                            Curl_dyn_len(&ctx->scratch), FALSE);
    CURL_TRC_CF(data, cf, "[%" CURL_PRId64 "] status: %s",
                stream_id, Curl_dyn_ptr(&ctx->scratch));
    if(result) {
      return -1;
    }
  }
  else {
    /* store as an HTTP1-style header */
    CURL_TRC_CF(data, cf, "[%" CURL_PRId64 "] header: %.*s: %.*s",
                stream_id, (int)h3name.len, h3name.base,
                (int)h3val.len, h3val.base);
    Curl_dyn_reset(&ctx->scratch);
    result = Curl_dyn_addn(&ctx->scratch,
                           (const char *)h3name.base, h3name.len);
    if(!result)
      result = Curl_dyn_addn(&ctx->scratch, STRCONST(": "));
    if(!result)
      result = Curl_dyn_addn(&ctx->scratch,
                             (const char *)h3val.base, h3val.len);
    if(!result)
      result = Curl_dyn_addn(&ctx->scratch, STRCONST("\r\n"));
    if(!result)
      h3_xfer_write_resp_hd(cf, data, stream, Curl_dyn_ptr(&ctx->scratch),
                            Curl_dyn_len(&ctx->scratch), FALSE);
  }
  return 0;
}

static int cb_h3_stop_sending(nghttp3_conn *conn, int64_t stream_id,
                              uint64_t app_error_code, void *user_data,
                              void *stream_user_data)
{
  struct Curl_cfilter *cf = user_data;
  struct cf_linuxq_ctx *ctx = cf->ctx;
  int rv;
  (void)conn;
  (void)stream_user_data;

  //rv = ngtcp2_conn_shutdown_stream_read(ctx->qconn, 0, stream_id,
                                        app_error_code);
  if(rv && rv != NGTCP2_ERR_STREAM_NOT_FOUND) {
    return NGTCP2_ERR_CALLBACK_FAILURE;
  }

  return 0;
}

static int cb_h3_reset_stream(nghttp3_conn *conn, int64_t sid,
                              uint64_t app_error_code, void *user_data,
                              void *stream_user_data) {
  struct Curl_cfilter *cf = user_data;
  struct cf_linuxq_ctx *ctx = cf->ctx;
  curl_int64_t stream_id = (curl_int64_t)sid;
  struct Curl_easy *data = stream_user_data;
  int rv;
  (void)conn;
  (void)data;

  //rv = ngtcp2_conn_shutdown_stream_write(ctx->qconn, 0, stream_id,
                                         app_error_code);
  CURL_TRC_CF(data, cf, "[%" CURL_PRId64 "] reset -> %d", stream_id, rv);
  if(rv && rv != NGTCP2_ERR_STREAM_NOT_FOUND) {
    return NGTCP2_ERR_CALLBACK_FAILURE;
  }

  return 0;
}

static nghttp3_callbacks ngh3_callbacks = {
  cb_h3_acked_req_body, /* acked_stream_data */
  cb_h3_stream_close,
  cb_h3_recv_data,
  cb_h3_deferred_consume,
  NULL, /* begin_headers */
  cb_h3_recv_header,
  cb_h3_end_headers,
  NULL, /* begin_trailers */
  cb_h3_recv_header,
  NULL, /* end_trailers */
  cb_h3_stop_sending,
  NULL, /* end_stream */
  cb_h3_reset_stream,
  NULL, /* shutdown */
  NULL /* recv_settings */
};

static CURLcode init_ngh3_conn(struct Curl_cfilter *cf)
{
  struct cf_linuxq_ctx *ctx = cf->ctx;
  CURLcode result;
  int rc;
  int64_t ctrl_stream_id, qpack_enc_stream_id, qpack_dec_stream_id;

  /*if(ngtcp2_conn_get_streams_uni_left(ctx->qconn) < 3) {
    return CURLE_QUIC_CONNECT_ERROR;
  }*/

  nghttp3_settings_default(&ctx->h3settings);

  rc = nghttp3_conn_client_new(&ctx->h3conn,
                               &ngh3_callbacks,
                               &ctx->h3settings,
                               nghttp3_mem_default(),
                               cf);
  if(rc) {
    result = CURLE_OUT_OF_MEMORY;
    goto fail;
  }

  //rc = ngtcp2_conn_open_uni_stream(ctx->qconn, &ctrl_stream_id, NULL);
  if(rc) {
    result = CURLE_QUIC_CONNECT_ERROR;
    goto fail;
  }

  rc = nghttp3_conn_bind_control_stream(ctx->h3conn, ctrl_stream_id);
  if(rc) {
    result = CURLE_QUIC_CONNECT_ERROR;
    goto fail;
  }

  //rc = ngtcp2_conn_open_uni_stream(ctx->qconn, &qpack_enc_stream_id, NULL);
  if(rc) {
    result = CURLE_QUIC_CONNECT_ERROR;
    goto fail;
  }

  //rc = ngtcp2_conn_open_uni_stream(ctx->qconn, &qpack_dec_stream_id, NULL);
  if(rc) {
    result = CURLE_QUIC_CONNECT_ERROR;
    goto fail;
  }

  rc = nghttp3_conn_bind_qpack_streams(ctx->h3conn, qpack_enc_stream_id,
                                       qpack_dec_stream_id);
  if(rc) {
    result = CURLE_QUIC_CONNECT_ERROR;
    goto fail;
  }

  return CURLE_OK;
fail:

  return result;
}

static void cf_linuxq_adjust_pollset(struct Curl_cfilter *cf,
                                      struct Curl_easy *data,
                                      struct easy_pollset *ps)
{
  struct cf_linuxq_ctx *ctx = cf->ctx;
  bool want_recv, want_send;

  if(!ctx->qconn)
    return;

  Curl_pollset_check(data, ps, ctx->q.sockfd, &want_recv, &want_send);
  if(!want_send && !Curl_bufq_is_empty(&ctx->q.sendbuf))
    want_send = TRUE;

  if(want_recv || want_send) {
    struct h3_stream_ctx *stream = H3_STREAM_CTX(ctx, data);
    struct cf_call_data save;
    bool c_exhaust, s_exhaust;

    CF_DATA_SAVE(save, cf, data);
    /*c_exhaust = want_send && (!ngtcp2_conn_get_cwnd_left(ctx->qconn) ||
                !ngtcp2_conn_get_max_data_left(ctx->qconn));*/
    s_exhaust = want_send && stream && stream->id >= 0 &&
                stream->quic_flow_blocked;
    want_recv = (want_recv || /*c_exhaust*/ || s_exhaust);
    want_send = (!s_exhaust && want_send) ||
                 !Curl_bufq_is_empty(&ctx->q.sendbuf);

    Curl_pollset_set(data, ps, ctx->q.sockfd, want_recv, want_send);
    CF_DATA_RESTORE(cf, save);
  }
}

static CURLcode cf_linuxq_shutdown(struct Curl_cfilter *cf,
                                   struct Curl_easy *data, bool *done)
{
  struct cf_linuxq_ctx *ctx = cf->ctx;
  struct cf_call_data save;
  struct pkt_io_ctx pktx;
  CURLcode result = CURLE_OK;

  if(cf->shutdown || !ctx->qconn) {
    *done = TRUE;
    return CURLE_OK;
  }

  CF_DATA_SAVE(save, cf, data);
  *done = FALSE;
  pktx_init(&pktx, cf, data);

  if(!ctx->shutdown_started) {
    char buffer[NGTCP2_MAX_UDP_PAYLOAD_SIZE];
    ssize_t nwritten;

    if(!Curl_bufq_is_empty(&ctx->q.sendbuf)) {
      CURL_TRC_CF(data, cf, "shutdown, flushing sendbuf");
      result = cf_progress_egress(cf, data, &pktx);
      if(!Curl_bufq_is_empty(&ctx->q.sendbuf)) {
        CURL_TRC_CF(data, cf, "sending shutdown packets blocked");
        result = CURLE_OK;
        goto out;
      }
      else if(result) {
        CURL_TRC_CF(data, cf, "shutdown, error %d flushing sendbuf", result);
        *done = TRUE;
        goto out;
      }
    }

    ctx->shutdown_started = TRUE;
    //nwritten = ngtcp2_conn_write_connection_close(
      //ctx->qconn, NULL, /* path */
      //NULL, /* pkt_info */
      //(uint8_t *)buffer, sizeof(buffer),
      //&ctx->last_error, pktx.ts);
    CURL_TRC_CF(data, cf, "start shutdown(err_type=%d, err_code=%"
                CURL_PRIu64 ") -> %d", ctx->last_error.type,
                (curl_uint64_t)ctx->last_error.error_code, (int)nwritten);
    if(nwritten > 0) {
      Curl_bufq_write(&ctx->q.sendbuf, (const unsigned char *)buffer,
                      (size_t)nwritten, &result);
      if(result) {
        CURL_TRC_CF(data, cf, "error %d adding shutdown packets to sendbuf, "
                    "aborting shutdown", result);
        goto out;
      }
      ctx->q.no_gso = TRUE;
      ctx->q.gsolen = (size_t)nwritten;
      ctx->q.split_len = 0;
    }
  }

  if(!Curl_bufq_is_empty(&ctx->q.sendbuf)) {
    CURL_TRC_CF(data, cf, "shutdown, flushing egress");
    result = vquic_flush(cf, data, &ctx->q);
    if(result == CURLE_AGAIN) {
      CURL_TRC_CF(data, cf, "sending shutdown packets blocked");
      result = CURLE_OK;
      goto out;
    }
    else if(result) {
      CURL_TRC_CF(data, cf, "shutdown, error %d flushing sendbuf", result);
      *done = TRUE;
      goto out;
    }
  }

  if(Curl_bufq_is_empty(&ctx->q.sendbuf)) {
    /* Sent everything off. */
    CURL_TRC_CF(data, cf, "shutdown completely sent off, done");
    *done = TRUE;
    result = CURLE_OK;
  }
out:
  CF_DATA_RESTORE(cf, save);
  return result;
}

static CURLcode h3_data_pause(struct Curl_cfilter *cf,
                              struct Curl_easy *data,
                              bool pause)
{
  /* TODO: there seems right now no API in ngtcp2 to shrink/enlarge
   * the streams windows. As we do in HTTP/2. */
  if(!pause) {
    h3_drain_stream(cf, data);
    Curl_expire(data, 0, EXPIRE_RUN_NOW);
  }
  return CURLE_OK;
}

static CURLcode cf_linuxq_data_event(struct Curl_cfilter *cf,
                                     struct Curl_easy *data,
                                     int event, int arg1, void *arg2)
{
  struct cf_linuxq_ctx *ctx = cf->ctx;
  CURLcode result = CURLE_OK;
  struct cf_call_data save;

  CF_DATA_SAVE(save, cf, data);
  (void)arg1;
  (void)arg2;
  switch(event) {
  case CF_CTRL_DATA_SETUP:
    break;
  case CF_CTRL_DATA_PAUSE:
    result = h3_data_pause(cf, data, (arg1 != 0));
    break;
  case CF_CTRL_DATA_DETACH:
    h3_data_done(cf, data);
    break;
  case CF_CTRL_DATA_DONE:
    h3_data_done(cf, data);
    break;
  case CF_CTRL_DATA_DONE_SEND: {
    struct h3_stream_ctx *stream = H3_STREAM_CTX(ctx, data);
    if(stream && !stream->send_closed) {
      stream->send_closed = TRUE;
      stream->upload_left = Curl_bufq_len(&stream->sendbuf);
      (void)nghttp3_conn_resume_stream(ctx->h3conn, stream->id);
    }
    break;
  }
  case CF_CTRL_DATA_IDLE: {
    struct h3_stream_ctx *stream = H3_STREAM_CTX(ctx, data);
    CURL_TRC_CF(data, cf, "data idle");
    if(stream && !stream->closed) {
/*
      result = check_and_set_expiry(cf, data, NULL);
      if(result)
        CURL_TRC_CF(data, cf, "data idle, check_and_set_expiry -> %d", result);
*/
    }
    break;
  }
  default:
    break;
  }
  CF_DATA_RESTORE(cf, save);
  return result;
}

static CURLcode cf_linuxq_shutdown(struct Curl_cfilter *cf,
                                   struct Curl_easy *data, bool *done)
{
  struct cf_linuxq_ctx *ctx = cf->ctx;
  struct cf_call_data save;
  struct pkt_io_ctx pktx;
  CURLcode result = CURLE_OK;

  if(cf->shutdown || !ctx->qconn) {
    *done = TRUE;
    return CURLE_OK;
  }

  CF_DATA_SAVE(save, cf, data);
  *done = FALSE;
  pktx_init(&pktx, cf, data);

  if(!ctx->shutdown_started) {
    char buffer[NGTCP2_MAX_UDP_PAYLOAD_SIZE];
    ssize_t nwritten;

    if(!Curl_bufq_is_empty(&ctx->q.sendbuf)) {
      CURL_TRC_CF(data, cf, "shutdown, flushing sendbuf");
      result = cf_progress_egress(cf, data, &pktx);
      if(!Curl_bufq_is_empty(&ctx->q.sendbuf)) {
        CURL_TRC_CF(data, cf, "sending shutdown packets blocked");
        result = CURLE_OK;
        goto out;
      }
      else if(result) {
        CURL_TRC_CF(data, cf, "shutdown, error %d flushing sendbuf", result);
        *done = TRUE;
        goto out;
      }
    }

    ctx->shutdown_started = TRUE;
    //nwritten = ngtcp2_conn_write_connection_close(
      //ctx->qconn, NULL, /* path */
      //NULL, /* pkt_info */
      //(uint8_t *)buffer, sizeof(buffer),
      //&ctx->last_error, pktx.ts);
    CURL_TRC_CF(data, cf, "start shutdown(err_type=%d, err_code=%"
                CURL_PRIu64 ") -> %d", ctx->last_error.type,
                (curl_uint64_t)ctx->last_error.error_code, (int)nwritten);
    if(nwritten > 0) {
      Curl_bufq_write(&ctx->q.sendbuf, (const unsigned char *)buffer,
                      (size_t)nwritten, &result);
      if(result) {
        CURL_TRC_CF(data, cf, "error %d adding shutdown packets to sendbuf, "
                    "aborting shutdown", result);
        goto out;
      }
      ctx->q.no_gso = TRUE;
      ctx->q.gsolen = (size_t)nwritten;
      ctx->q.split_len = 0;
    }
  }

  if(!Curl_bufq_is_empty(&ctx->q.sendbuf)) {
    CURL_TRC_CF(data, cf, "shutdown, flushing egress");
    result = vquic_flush(cf, data, &ctx->q);
    if(result == CURLE_AGAIN) {
      CURL_TRC_CF(data, cf, "sending shutdown packets blocked");
      result = CURLE_OK;
      goto out;
    }
    else if(result) {
      CURL_TRC_CF(data, cf, "shutdown, error %d flushing sendbuf", result);
      *done = TRUE;
      goto out;
    }
  }

  if(Curl_bufq_is_empty(&ctx->q.sendbuf)) {
    /* Sent everything off. ngtcp2 seems to have no support for graceful
     * shutdowns. So, we are done. */
    CURL_TRC_CF(data, cf, "shutdown completely sent off, done");
    *done = TRUE;
    result = CURLE_OK;
  }
out:
  CF_DATA_RESTORE(cf, save);
  return result;
}

static void cf_linuxq_conn_close(struct Curl_cfilter *cf,
                                 struct Curl_easy *data)
{
  bool done;
  cf_linuxq_shutdown(cf, data, &done);
}

static void cf_linuxq_close(struct Curl_cfilter *cf, struct Curl_easy *data)
{
  struct cf_linuxq_ctx *ctx = cf->ctx;
  struct cf_call_data save;

  CF_DATA_SAVE(save, cf, data);
  if(ctx && ctx->qconn) {
    cf_linuxq_conn_close(cf, data);
    cf_linuxq_ctx_clear(ctx);
    CURL_TRC_CF(data, cf, "close");
  }
  cf->connected = FALSE;
  CF_DATA_RESTORE(cf, save);
}

static void cf_linuxq_destroy(struct Curl_cfilter *cf, struct Curl_easy *data)
{
  struct cf_linuxq_ctx *ctx = cf->ctx;
  struct cf_call_data save;

  CF_DATA_SAVE(save, cf, data);
  CURL_TRC_CF(data, cf, "destroy");
  if(ctx) {
    cf_linuxq_ctx_clear(ctx);
    free(ctx);
  }
  cf->ctx = NULL;
  /* No CF_DATA_RESTORE(cf, save) possible */
  (void)save;
}

/*
 * Might be called twice for happy eyeballs.
 */
static CURLcode cf_connect_start(struct Curl_cfilter *cf,
                                 struct Curl_easy *data,
                                 struct pkt_io_ctx *pktx)
{
  struct cf_linuxq_ctx *ctx = cf->ctx;
  int rc;
  int rv;
  CURLcode result;
  const struct Curl_sockaddr_ex *sockaddr = NULL;
  int qfd;

  //ctx->version = NGTCP2_PROTO_VER_MAX;
  ctx->max_stream_window = H3_STREAM_WINDOW_SIZE;
  ctx->max_idle_ms = CURL_QUIC_MAX_IDLE_MS;
  Curl_bufcp_init(&ctx->stream_bufcp, H3_STREAM_CHUNK_SIZE,
                  H3_STREAM_POOL_SPARES);
  Curl_dyn_init(&ctx->scratch, CURL_MAX_HTTP_HEADER);
  Curl_hash_offt_init(&ctx->streams, 63, h3_stream_hash_free);

  /*result = Curl_ssl_peer_init(&ctx->peer, cf, TRNSPRT_QUIC);
  if(result)
    return result;*/

#define H3_ALPN "\x2h3\x5h3-29"
  /*result = Curl_vquic_tls_init(&ctx->tls, cf, data, &ctx->peer,
                               H3_ALPN, sizeof(H3_ALPN) - 1,
                               tls_ctx_setup, &ctx->tls, &ctx->conn_ref);*
  if(result)
    return result;*/

/*
#ifdef USE_OPENSSL
  SSL_set_quic_use_legacy_codepoint(ctx->tls.ossl.ssl, 0);
#endif

  ctx->dcid.datalen = NGTCP2_MAX_CIDLEN;
  result = Curl_rand(data, ctx->dcid.data, NGTCP2_MAX_CIDLEN);
  if(result)
    return result;

  ctx->scid.datalen = NGTCP2_MAX_CIDLEN;
  result = Curl_rand(data, ctx->scid.data, NGTCP2_MAX_CIDLEN);
  if(result)
    return result;
*/

  //(void)Curl_qlogdir(data, ctx->scid.data, NGTCP2_MAX_CIDLEN, &qfd);
  //ctx->qlogfd = qfd; /* -1 if failure above */
  //quic_settings(ctx, data, pktx);

/*
  result = vquic_ctx_init(&ctx->q);
  if(result)
    return result;

  Curl_cf_socket_peek(cf->next, data, &ctx->q.sockfd, &sockaddr, NULL);
  if(!sockaddr)
    return CURLE_QUIC_CONNECT_ERROR;
  ctx->q.local_addrlen = sizeof(ctx->q.local_addr);
  rv = getsockname(ctx->q.sockfd, (struct sockaddr *)&ctx->q.local_addr,
                   &ctx->q.local_addrlen);
  if(rv == -1)
    return CURLE_QUIC_CONNECT_ERROR;

  ngtcp2_addr_init(&ctx->connected_path.local,
                   (struct sockaddr *)&ctx->q.local_addr,
                   ctx->q.local_addrlen);
  ngtcp2_addr_init(&ctx->connected_path.remote,
                   &sockaddr->sa_addr, (socklen_t)sockaddr->addrlen);

  rc = ngtcp2_conn_client_new(&ctx->qconn, &ctx->dcid, &ctx->scid,
                              &ctx->connected_path,
                              NGTCP2_PROTO_VER_V1, &ng_callbacks,
                              &ctx->settings, &ctx->transport_params,
                              NULL, cf);
  if(rc)
    return CURLE_QUIC_CONNECT_ERROR;

#ifdef USE_OPENSSL
  ngtcp2_conn_set_tls_native_handle(ctx->qconn, ctx->tls.ossl.ssl);
#elif defined(USE_GNUTLS)
  ngtcp2_conn_set_tls_native_handle(ctx->qconn, ctx->tls.gtls.session);
#else
  ngtcp2_conn_set_tls_native_handle(ctx->qconn, ctx->tls.wssl.handle);
#endif

  ngtcp2_ccerr_default(&ctx->last_error);

  ctx->conn_ref.get_conn = get_conn;
  ctx->conn_ref.user_data = cf;

*/
  return CURLE_OK;
}

static CURLcode cf_linuxq_connect(struct Curl_cfilter *cf,
                                  struct Curl_easy *data,
                                  bool blocking, bool *done)
{
  struct cf_linuxq_ctx *ctx = cf->ctx;
  CURLcode result = CURLE_OK;
  struct cf_call_data save;
  struct curltime now;
  struct pkt_io_ctx pktx;

  if(cf->connected) {
    *done = TRUE;
    return CURLE_OK;
  }

  /* Connect the QUIC filter first */
  if(!cf->next->connected) {
    result = Curl_conn_cf_connect(cf->next, data, blocking, done);
    if(result || !*done)
      return result;
  }

  *done = FALSE;
  now = Curl_now();
  pktx_init(&pktx, cf, data);

  CF_DATA_SAVE(save, cf, data);

  if(ctx->reconnect_at.tv_sec && Curl_timediff(now, ctx->reconnect_at) < 0) {
    /* Not time yet to attempt the next connect */
    CURL_TRC_CF(data, cf, "waiting for reconnect time");
    goto out;
  }

  if(!ctx->qconn) {
    ctx->started_at = now;
    result = cf_connect_start(cf, data, &pktx);
    if(result)
      goto out;
    result = cf_progress_egress(cf, data, &pktx);
    /* we do not expect to be able to recv anything yet */
    goto out;
  }

  result = cf_progress_ingress(cf, data, &pktx);
  if(result)
    goto out;

  result = cf_progress_egress(cf, data, &pktx);
  if(result)
    goto out;

  /*if(ngtcp2_conn_get_handshake_completed(ctx->qconn)) {
    ctx->handshake_at = now;
    CURL_TRC_CF(data, cf, "handshake complete after %dms",
               (int)Curl_timediff(now, ctx->started_at));
    result = qng_verify_peer(cf, data);
    if(!result) {
      CURL_TRC_CF(data, cf, "peer verified");
      cf->connected = TRUE;
      cf->conn->alpn = CURL_HTTP_VERSION_3;
      *done = TRUE;
      connkeep(cf->conn, "HTTP/3 default");
    }*/
  }

out:
  if(result == CURLE_RECV_ERROR && ctx->qconn &&
     //ngtcp2_conn_in_draining_period(ctx->qconn)) {
    /* When a QUIC server instance is shutting down, it may send us a
     * CONNECTION_CLOSE right away. Our connection then enters the DRAINING
     * state. The CONNECT may work in the near future again. Indicate
     * that as a "weird" reply. */
    result = CURLE_WEIRD_SERVER_REPLY;
  }

#ifndef CURL_DISABLE_VERBOSE_STRINGS
  if(result) {
    struct ip_quadruple ip;

    Curl_cf_socket_peek(cf->next, data, NULL, NULL, &ip);
    infof(data, "QUIC connect to %s port %u failed: %s",
          ip.remote_ip, ip.remote_port, curl_easy_strerror(result));
  }
#endif
/*
  if(!result && ctx->qconn) {
    result = check_and_set_expiry(cf, data, &pktx);
  }*/
  if(result || *done)
    CURL_TRC_CF(data, cf, "connect -> %d, done=%d", result, *done);
  CF_DATA_RESTORE(cf, save);
  return result;
}

/* incoming data frames on the h3 stream */
static ssize_t cf_linuxq_recv(struct Curl_cfilter *cf, struct Curl_easy *data,
                              char *buf, size_t blen, CURLcode *err)
{
  struct cf_linuxq_ctx *ctx = cf->ctx;
  struct h3_stream_ctx *stream = H3_STREAM_CTX(ctx, data);
  ssize_t nread = -1;
  struct cf_call_data save;
  struct pkt_io_ctx pktx;

  (void)ctx;
  (void)buf;

  CF_DATA_SAVE(save, cf, data);
  DEBUGASSERT(cf->connected);
  DEBUGASSERT(ctx);
  DEBUGASSERT(ctx->qconn);
  DEBUGASSERT(ctx->h3conn);
  *err = CURLE_OK;

  pktx_init(&pktx, cf, data);

  if(!stream || ctx->shutdown_started) {
    *err = CURLE_RECV_ERROR;
    goto out;
  }

  if(cf_progress_ingress(cf, data, &pktx)) {
    *err = CURLE_RECV_ERROR;
    nread = -1;
    goto out;
  }

  if(stream->xfer_result) {
    CURL_TRC_CF(data, cf, "[%" CURL_PRId64 "] xfer write failed", stream->id);
    //cf_ngtcp2_stream_close(cf, data, stream);
    *err = stream->xfer_result;
    nread = -1;
    goto out;
  }
  else if(stream->closed) {
    nread = recv_closed_stream(cf, data, stream, err);
    goto out;
  }
  *err = CURLE_AGAIN;
  nread = -1;

out:
  if(cf_progress_egress(cf, data, &pktx)) {
    *err = CURLE_SEND_ERROR;
    nread = -1;
  }/*
  else {
    CURLcode result2 = check_and_set_expiry(cf, data, &pktx);
    if(result2) {
      *err = result2;
      nread = -1;
    }
  }*/
  CURL_TRC_CF(data, cf, "[%" CURL_PRId64 "] cf_recv(blen=%zu) -> %zd, %d",
              stream? stream->id : -1, blen, nread, *err);
  CF_DATA_RESTORE(cf, save);
  return nread;
}

static ssize_t cf_linuxq_send(struct Curl_cfilter *cf, struct Curl_easy *data,
                              const void *buf, size_t len, CURLcode *err)
{
  struct cf_linuxq_ctx *ctx = cf->ctx;
  struct h3_stream_ctx *stream = H3_STREAM_CTX(ctx, data);
  ssize_t sent = 0;
  struct cf_call_data save;
  struct pkt_io_ctx pktx;
  CURLcode result;

  CF_DATA_SAVE(save, cf, data);
  DEBUGASSERT(cf->connected);
  DEBUGASSERT(ctx->qconn);
  DEBUGASSERT(ctx->h3conn);
  pktx_init(&pktx, cf, data);
  *err = CURLE_OK;

  result = cf_progress_ingress(cf, data, &pktx);
  if(result) {
    *err = result;
    sent = -1;
  }

  if(!stream || stream->id < 0) {
    if(ctx->shutdown_started) {
      CURL_TRC_CF(data, cf, "cannot open stream on closed connection");
      *err = CURLE_SEND_ERROR;
      sent = -1;
      goto out;
    }
    sent = h3_stream_open(cf, data, buf, len, err);
    if(sent < 0) {
      CURL_TRC_CF(data, cf, "failed to open stream -> %d", *err);
      goto out;
    }
    stream = H3_STREAM_CTX(ctx, data);
  }
  else if(stream->xfer_result) {
    CURL_TRC_CF(data, cf, "[%" CURL_PRId64 "] xfer write failed", stream->id);
    //cf_ngtcp2_stream_close(cf, data, stream);
    *err = stream->xfer_result;
    sent = -1;
    goto out;
  }
  else if(stream->upload_blocked_len) {
    /* the data in `buf` has already been submitted or added to the
     * buffers, but have been EAGAINed on the last invocation. */
    DEBUGASSERT(len >= stream->upload_blocked_len);
    if(len < stream->upload_blocked_len) {
      /* Did we get called again with a smaller `len`? This should not
       * happen. We are not prepared to handle that. */
      failf(data, "HTTP/3 send again with decreased length");
      *err = CURLE_HTTP3;
      sent = -1;
      goto out;
    }
    sent = (ssize_t)stream->upload_blocked_len;
    stream->upload_blocked_len = 0;
  }
  else if(stream->closed) {
    if(stream->resp_hds_complete) {
      /* Server decided to close the stream after having sent us a final
       * response. This is valid if it is not interested in the request
       * body. This happens on 30x or 40x responses.
       * We silently discard the data sent, since this is not a transport
       * error situation. */
      CURL_TRC_CF(data, cf, "[%" CURL_PRId64 "] discarding data"
                  "on closed stream with response", stream->id);
      *err = CURLE_OK;
      sent = (ssize_t)len;
      goto out;
    }
    CURL_TRC_CF(data, cf, "[%" CURL_PRId64 "] send_body(len=%zu) "
                "-> stream closed", stream->id, len);
    *err = CURLE_HTTP3;
    sent = -1;
    goto out;
  }
  else if(ctx->shutdown_started) {
    CURL_TRC_CF(data, cf, "cannot send on closed connection");
    *err = CURLE_SEND_ERROR;
    sent = -1;
    goto out;
  }
  else {
    sent = Curl_bufq_write(&stream->sendbuf, buf, len, err);
    CURL_TRC_CF(data, cf, "[%" CURL_PRId64 "] cf_send, add to "
                "sendbuf(len=%zu) -> %zd, %d",
                stream->id, len, sent, *err);
    if(sent < 0) {
      goto out;
    }

    (void)nghttp3_conn_resume_stream(ctx->h3conn, stream->id);
  }

  result = cf_progress_egress(cf, data, &pktx);
  if(result) {
    *err = result;
    sent = -1;
  }

  if(stream && sent > 0 && stream->sendbuf_len_in_flight) {
    /* We have unacknowledged DATA and cannot report success to our
     * caller. Instead we EAGAIN and remember how much we have already
     * "written" into our various internal connection buffers. */
    stream->upload_blocked_len = sent;
    CURL_TRC_CF(data, cf, "[%" CURL_PRId64 "] cf_send(len=%zu), "
                "%zu bytes in flight -> EGAIN", stream->id, len,
                stream->sendbuf_len_in_flight);
    *err = CURLE_AGAIN;
    sent = -1;
  }

out:
  /*result = check_and_set_expiry(cf, data, &pktx);
  if(result) {
    *err = result;
    sent = -1;
  }*/
  CURL_TRC_CF(data, cf, "[%" CURL_PRId64 "] cf_send(len=%zu) -> %zd, %d",
              stream? stream->id : -1, len, sent, *err);
  CF_DATA_RESTORE(cf, save);
  return sent;
}

/*
 * Called from transfer.c:data_pending to know if we should keep looping
 * to receive more data from the connection.
 */
static bool cf_linuxq_data_pending(struct Curl_cfilter *cf,
                                   const struct Curl_easy *data)
{
  (void)cf;
  (void)data;
  return FALSE;
}

static CURLcode cf_linuxq_query(struct Curl_cfilter *cf,
                                struct Curl_easy *data,
                                int query, int *pres1, void *pres2)
{
  struct cf_linuxq_ctx *ctx = cf->ctx;
  struct cf_call_data save;

  switch(query) {
  case CF_QUERY_MAX_CONCURRENT: {
    DEBUGASSERT(pres1);
    CF_DATA_SAVE(save, cf, data);
    /* Set after transport params arrived and continually updated
     * by callback. QUIC counts the number over the lifetime of the
     * connection, ever increasing.
     * We count the *open* transfers plus the budget for new ones. */
    if(!ctx->qconn || ctx->shutdown_started) {
      *pres1 = 0;
    }
    else if(ctx->max_bidi_streams) {
      uint64_t avail_bidi_streams = 0;
      uint64_t max_streams = CONN_INUSE(cf->conn);
      if(ctx->max_bidi_streams > ctx->used_bidi_streams)
        avail_bidi_streams = ctx->max_bidi_streams - ctx->used_bidi_streams;
      max_streams += avail_bidi_streams;
      *pres1 = (max_streams > INT_MAX)? INT_MAX : (int)max_streams;
    }
    else  /* transport params not arrived yet? take our default. */
      *pres1 = (int)Curl_multi_max_concurrent_streams(data->multi);
    CURL_TRC_CF(data, cf, "query conn[%" CURL_FORMAT_CURL_OFF_T "]: "
                "MAX_CONCURRENT -> %d (%zu in use)",
                cf->conn->connection_id, *pres1, CONN_INUSE(cf->conn));
    CF_DATA_RESTORE(cf, save);
    return CURLE_OK;
  }
  case CF_QUERY_CONNECT_REPLY_MS:
    if(ctx->q.got_first_byte) {
      timediff_t ms = Curl_timediff(ctx->q.first_byte_at, ctx->started_at);
      *pres1 = (ms < INT_MAX)? (int)ms : INT_MAX;
    }
    else
      *pres1 = -1;
    return CURLE_OK;
  case CF_QUERY_TIMER_CONNECT: {
    struct curltime *when = pres2;
    if(ctx->q.got_first_byte)
      *when = ctx->q.first_byte_at;
    return CURLE_OK;
  }
  case CF_QUERY_TIMER_APPCONNECT: {
    struct curltime *when = pres2;
    if(cf->connected)
      *when = ctx->handshake_at;
    return CURLE_OK;
  }
  default:
    break;
  }
  return cf->next?
    cf->next->cft->query(cf->next, data, query, pres1, pres2) :
    CURLE_UNKNOWN_OPTION;
}

static bool cf_linuxq_conn_is_alive(struct Curl_cfilter *cf,
                                    struct Curl_easy *data,
                                    bool *input_pending)
{
  struct cf_linuxq_ctx *ctx = cf->ctx;
  bool alive = FALSE;
  //const ngtcp2_transport_params *rp;
  struct cf_call_data save;

  CF_DATA_SAVE(save, cf, data);
  *input_pending = FALSE;
  if(!ctx->qconn || ctx->shutdown_started)
    goto out;

  /* Both sides of the QUIC connection announce they max idle times in
   * the transport parameters. Look at the minimum of both and if
   * we exceed this, regard the connection as dead. The other side
   * may have completely purged it and will no longer respond
   * to any packets from us. */
/*
  rp = ngtcp2_conn_get_remote_transport_params(ctx->qconn);
  if(rp) {
    timediff_t idletime;
    uint64_t idle_ms = ctx->max_idle_ms;

    if(rp->max_idle_timeout &&
      (rp->max_idle_timeout / NGTCP2_MILLISECONDS) < idle_ms)
      idle_ms = (rp->max_idle_timeout / NGTCP2_MILLISECONDS);
    idletime = Curl_timediff(Curl_now(), ctx->q.last_io);
    if(idletime > 0 && (uint64_t)idletime > idle_ms)
      goto out;
  }
*/

  if(!cf->next || !cf->next->cft->is_alive(cf->next, data, input_pending))
    goto out;

  alive = TRUE;
  if(*input_pending) {
    CURLcode result;
    /* This happens before we have sent off a request and the connection is
       not in use by any other transfer, there should not be any data here,
       only "protocol frames" */
    *input_pending = FALSE;
    result = cf_progress_ingress(cf, data, NULL);
    CURL_TRC_CF(data, cf, "is_alive, progress ingress -> %d", result);
    alive = result? FALSE : TRUE;
  }

out:
  CF_DATA_RESTORE(cf, save);
  return alive;
}

struct Curl_cftype Curl_cft_http3 = {
  "HTTP/3",
  CF_TYPE_IP_CONNECT | CF_TYPE_SSL | CF_TYPE_MULTIPLEX,
  0,
  cf_linuxq_destroy,
  cf_linuxq_connect,
  cf_linuxq_close,
  cf_linuxq_shutdown,
  Curl_cf_def_get_host,
  cf_linuxq_adjust_pollset,
  cf_linuxq_data_pending,
  cf_linuxq_send,
  cf_linuxq_recv,
  cf_linuxq_data_event,
  cf_ngtcp2_conn_is_alive,
  Curl_cf_def_conn_keep_alive,
  cf_ngtcp2_query,
};

CURLcode Curl_cf_linuxq_create(struct Curl_cfilter **pcf,
                               struct Curl_easy *data,
                               struct connectdata *conn,
                               const struct Curl_addrinfo *ai)
{
  struct cf_linuxq_ctx *ctx = NULL;
  struct Curl_cfilter *cf = NULL, *quic_cf = NULL;
  CURLcode result;

  (void)data;
  ctx = calloc(1, sizeof(*ctx));
  if(!ctx) {
    result = CURLE_OUT_OF_MEMORY;
    goto out;
  }
  ctx->qlogfd = -1;
  cf_ngtcp2_ctx_clear(ctx);

  result = Curl_cf_create(&cf, &Curl_cft_http3, ctx);
  if(result)
    goto out;

  result = Curl_cf_quic_create(&quic_cf, data, conn, ai, TRNSPRT_QUIC);
  if(result)
    goto out;

  cf->conn = conn;
  quic_cf->conn = cf->conn;
  quic_cf->sockindex = cf->sockindex;
  cf->next = quic_cf;

out:
  *pcf = (!result)? cf : NULL;
  if(result) {
    if(quic_cf)
      Curl_conn_cf_discard_sub(cf, quic_cf, data, TRUE);
    Curl_safefree(cf);
    Curl_safefree(ctx);
  }
  return result;
}

bool Curl_conn_is_linuxq(const struct Curl_easy *data,
                         const struct connectdata *conn,
                         int sockindex)
{
  struct Curl_cfilter *cf = conn? conn->cfilter[sockindex] : NULL;

  (void)data;
  for(; cf; cf = cf->next) {
    if(cf->cft == &Curl_cft_http3)
      return TRUE;
    if(cf->cft->flags & CF_TYPE_IP_CONNECT)
      return FALSE;
  }
  return FALSE;
}

#endif
