// SPDX-FileCopyrightText: Copyright (c) 2025-2026 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

//! HTTP/2 relay for TLS-terminated, L7-inspected REST endpoints.
//!
//! Each client stream is admitted on its own: the request head is converted to
//! an HTTP/1-shaped header block so it passes through the same parser,
//! canonicalization, policy evaluation, token-grant injection, and header
//! placeholder rewriting as an HTTP/1 request. Only an admitted stream opens a
//! stream upstream. A refused stream gets a response or `RST_STREAM`; the
//! connection and its other streams continue.
//!
//! Request bodies are streamed, not rewritten: a body or trailer carrying a
//! credential placeholder resets the stream instead of reaching upstream.

use crate::l7::relay::{
    L7EvalContext, credential_generation_guard, emit_l7_request_log, evaluate_l7_request,
    prepare_inspected_request, reject_credential_resolution, request_authority_matches_endpoint,
    select_l7_config_for_path,
};
use crate::l7::{EnforcementMode, L7EndpointConfig, L7Protocol, L7RequestInfo};
use crate::opa::TunnelPolicyEngine;
use ::h2::client::{ResponseFuture, SendRequest};
use ::h2::server::SendResponse;
use ::h2::{Reason, RecvStream, SendStream};
use bytes::Bytes;
use futures::stream::{FuturesUnordered, StreamExt};
use http::header::{HOST, HeaderName, HeaderValue};
use http::{Request, Response, StatusCode};
use miette::{IntoDiagnostic, Result};
use openshell_core::secrets;
use std::future::poll_fn;
use std::task::Poll;
use tokio::io::{AsyncRead, AsyncWrite};
use tracing::debug;

const MAX_CONCURRENT_STREAMS: u32 = 100;
const MAX_HEADER_LIST_SIZE: u32 = 64 * 1024;

/// The `host:port` destinations that opt in to HTTP/2, comma-separated, fixed
/// when the supervisor is built (`OPENSHELL_HTTP2_ENDPOINTS`). Unset or empty:
/// every tunnel negotiates HTTP/1.1 only.
pub const HTTP2_ENDPOINTS: &str = match option_env!("OPENSHELL_HTTP2_ENDPOINTS") {
    Some(list) => list,
    None => "",
};

/// Whether `host:port` is listed in `opted_in` (see [`HTTP2_ENDPOINTS`]).
pub fn endpoint_opted_in(opted_in: &str, host: &str, port: u16) -> bool {
    opted_in.split(',').any(|entry| {
        entry.trim().rsplit_once(':').is_some_and(|(h, p)| {
            h.eq_ignore_ascii_case(host) && p.parse::<u16>().is_ok_and(|p| p == port)
        })
    })
}

/// Whether an endpoint's enforcement can be applied to HTTP/2 streams.
///
/// Request signing and body rewriting need the whole HTTP/1 body path, so
/// those endpoints keep negotiating HTTP/1.1.
pub fn endpoint_supports_h2(config: &L7EndpointConfig) -> bool {
    config.protocol == L7Protocol::Rest
        && !config.credential_signing.is_sigv4()
        && !config.request_body_credential_rewrite
}

/// Whether to offer `h2` to the sandbox client: the destination opted in,
/// every endpoint on the route is inspected REST that the relay can enforce,
/// the tunnel can carry credentials, and no middleware applies (the relay
/// refuses streams that need middleware).
pub fn should_offer_h2<'a>(
    opted_in: &str,
    ctx: &L7EvalContext,
    configs: impl IntoIterator<Item = &'a L7EndpointConfig>,
    middleware_chain_is_empty: impl FnOnce() -> bool,
) -> bool {
    let mut configs = configs.into_iter().peekable();
    endpoint_opted_in(opted_in, &ctx.host, ctx.port)
        && configs.peek().is_some()
        && configs.all(endpoint_supports_h2)
        && (ctx.provider_credentials.is_some() || ctx.secret_resolver.is_some())
        && middleware_chain_is_empty()
}

struct Shared<'a> {
    configs: &'a [L7EndpointConfig],
    engine: &'a TunnelPolicyEngine,
    ctx: &'a L7EvalContext,
}

/// Relay one HTTP/2 connection. `upstream` is `None` when the upstream did
/// not negotiate `h2`; every stream is then answered with 502.
pub async fn relay_h2<C, U>(
    client: C,
    upstream: Option<U>,
    configs: &[L7EndpointConfig],
    engine: &TunnelPolicyEngine,
    ctx: &L7EvalContext,
) -> Result<()>
where
    C: AsyncRead + AsyncWrite + Unpin + Send,
    U: AsyncRead + AsyncWrite + Unpin + Send,
{
    let mut server = ::h2::server::Builder::new()
        .max_concurrent_streams(MAX_CONCURRENT_STREAMS)
        .max_header_list_size(MAX_HEADER_LIST_SIZE)
        .handshake::<_, Bytes>(client)
        .await
        .into_diagnostic()?;

    let (sender, upstream_conn) = match upstream {
        Some(io) => match ::h2::client::Builder::new()
            .enable_push(false)
            .max_header_list_size(MAX_HEADER_LIST_SIZE)
            .handshake::<_, Bytes>(io)
            .await
        {
            Ok((sender, conn)) => (Some(sender), Some(conn)),
            Err(error) => {
                debug!(host = %ctx.host, error = %error, "upstream HTTP/2 handshake failed");
                (None, None)
            }
        },
        None => (None, None),
    };
    let upstream_conn = async move {
        match upstream_conn {
            Some(conn) => conn.await,
            None => std::future::pending().await,
        }
    };
    tokio::pin!(upstream_conn);

    let shared = Shared {
        configs,
        engine,
        ctx,
    };
    let mut streams = FuturesUnordered::new();
    let mut upstream_open = true;
    loop {
        let mut shutdown = false;
        tokio::select! {
            accepted = server.accept() => match accepted {
                Some(Ok((request, respond))) => {
                    streams.push(handle_stream(request, respond, sender.clone(), &shared));
                }
                Some(Err(error)) => {
                    debug!(host = %ctx.host, error = %error, "HTTP/2 client connection error");
                    break;
                }
                None => break,
            },
            Some(()) = streams.next(), if !streams.is_empty() => {}
            result = &mut upstream_conn, if upstream_open => {
                debug!(host = %ctx.host, ?result, "upstream HTTP/2 connection closed");
                upstream_open = false;
                shutdown = true;
            }
        }
        if shutdown {
            // New streams would only fail; let open ones finish.
            server.graceful_shutdown();
        }
    }
    Ok(())
}

enum Refusal {
    Respond { status: StatusCode, body: String },
    Reset(Reason),
}

impl Refusal {
    fn json(status: StatusCode, error: &str, detail: &str) -> Self {
        Self::Respond {
            status,
            body: serde_json::json!({ "error": error, "detail": detail }).to_string(),
        }
    }

    fn send(self, respond: &mut SendResponse<Bytes>) {
        match self {
            Self::Respond { status, body } => {
                let Ok(head) = Response::builder()
                    .status(status)
                    .header("content-type", "application/json")
                    .body(())
                else {
                    respond.send_reset(Reason::INTERNAL_ERROR);
                    return;
                };
                if let Ok(mut stream) = respond.send_response(head, false) {
                    let _ = stream.send_data(Bytes::from(body), true);
                }
            }
            Self::Reset(reason) => respond.send_reset(reason),
        }
    }
}

struct Admitted {
    request: Request<()>,
    ctx: L7EvalContext,
}

async fn handle_stream(
    request: Request<RecvStream>,
    mut respond: SendResponse<Bytes>,
    sender: Option<SendRequest<Bytes>>,
    shared: &Shared<'_>,
) {
    let (parts, body) = request.into_parts();
    let admitted = match admit(&parts, shared).await {
        Ok(admitted) => admitted,
        Err(refusal) => {
            refusal.send(&mut respond);
            return;
        }
    };
    let bad_gateway = || {
        Refusal::json(
            StatusCode::BAD_GATEWAY,
            "upstream_unavailable",
            "upstream HTTP/2 connection is not available",
        )
    };
    let Some(sender) = sender else {
        bad_gateway().send(&mut respond);
        return;
    };
    let Ok(mut sender) = sender.ready().await else {
        bad_gateway().send(&mut respond);
        return;
    };
    // Last checks before the first upstream write, matching the HTTP/1 path.
    if shared.engine.is_stale() {
        respond.send_reset(Reason::REFUSED_STREAM);
        return;
    }
    if let Some(guard) = credential_generation_guard(&admitted.ctx)
        && guard.ensure_current().is_err()
    {
        bad_gateway().send(&mut respond);
        return;
    }
    let end_of_stream = body.is_end_stream();
    let Ok((response_future, upstream_send)) = sender.send_request(admitted.request, end_of_stream)
    else {
        bad_gateway().send(&mut respond);
        return;
    };
    let request_body = async {
        if !end_of_stream {
            let _ = pump(body, upstream_send, true).await;
        }
    };
    tokio::join!(request_body, relay_response(response_future, respond));
}

/// Per-stream admission. Returns the upstream request head with credentials
/// resolved, or how to refuse the stream.
async fn admit(parts: &http::request::Parts, shared: &Shared<'_>) -> Result<Admitted, Refusal> {
    let ctx = shared.ctx;
    if parts.method == http::Method::CONNECT {
        return Err(Refusal::json(
            StatusCode::FORBIDDEN,
            "unsupported_request",
            "extended CONNECT is not supported over HTTP/2",
        ));
    }
    // Only origin-form: other forms would be evaluated on the path they name
    // but forwarded as `:path` appended to the authority. The path
    // canonicalizer rejects asterisk-form too.
    if !parts
        .uri
        .path_and_query()
        .is_some_and(|target| target.as_str().starts_with('/'))
    {
        return Err(Refusal::json(
            StatusCode::BAD_REQUEST,
            "bad_request",
            ":path must be origin-form",
        ));
    }
    let head = synthesize_h1_head(parts)
        .map_err(|detail| Refusal::json(StatusCode::BAD_REQUEST, "bad_request", detail))?;

    let lenient = shared
        .configs
        .iter()
        .any(|config| config.allow_encoded_slash);
    let req = parse_head(&head, lenient).await?;
    let config = if shared.configs.len() == 1 {
        &shared.configs[0]
    } else {
        select_l7_config_for_path(shared.configs, &req.target).ok_or_else(|| {
            Refusal::json(
                StatusCode::FORBIDDEN,
                "policy_denied",
                "no L7 endpoint matches the request path",
            )
        })?
    };
    let req = if lenient && !config.allow_encoded_slash {
        parse_head(&head, false).await?
    } else {
        req
    };
    if !endpoint_supports_h2(config) {
        return Err(Refusal::json(
            StatusCode::FORBIDDEN,
            "unsupported_request",
            "this endpoint is not supported over HTTP/2",
        ));
    }
    if !request_authority_matches_endpoint(&req, ctx) {
        return Err(Refusal::json(
            StatusCode::FORBIDDEN,
            "authority_mismatch",
            "request authority does not match the CONNECT endpoint",
        ));
    }

    let redacted_target = match secrets::redact_target_for_policy(&req.target) {
        Ok(target) => target,
        Err(error) => return Err(credential_refusal(ctx, &req.action, &error).await),
    };
    let request_info = L7RequestInfo {
        action: req.action.clone(),
        target: redacted_target.clone(),
        query_params: req.query_params.clone(),
        graphql: None,
        jsonrpc: None,
    };
    let (allowed, reason) = evaluate_l7_request(shared.engine, ctx, &request_info)
        .map_err(|_| Refusal::Reset(Reason::REFUSED_STREAM))?;
    let decision = match (allowed, config.enforcement) {
        (true, _) => "allow",
        (false, EnforcementMode::Audit) => "audit",
        (false, EnforcementMode::Enforce) => "deny",
    };
    emit_l7_request_log(
        ctx,
        &request_info.action,
        &redacted_target,
        decision,
        "l7",
        &reason,
        None,
    );
    if decision == "deny" {
        return Err(Refusal::Respond {
            status: StatusCode::FORBIDDEN,
            body: serde_json::json!({
                "error": "policy_denied",
                "policy": ctx.policy_name,
                "detail": reason,
            })
            .to_string(),
        });
    }

    let chain = shared
        .engine
        .query_middleware_chain(&crate::l7::middleware::middleware_network_input(ctx))
        .map_err(|_| Refusal::Reset(Reason::REFUSED_STREAM))?;
    if !chain.is_empty() {
        return Err(Refusal::json(
            StatusCode::FORBIDDEN,
            "middleware_required",
            "middleware is not supported over HTTP/2",
        ));
    }

    let request_id = uuid::Uuid::new_v4().to_string();
    let (req, scoped) = prepare_inspected_request(
        req,
        ctx,
        shared.engine,
        config,
        &request_info,
        &request_id,
        None,
    )
    .await
    .map_err(|_| {
        Refusal::json(
            StatusCode::BAD_GATEWAY,
            "credential_unavailable",
            "credential could not be prepared",
        )
    })?;
    let rewritten = match secrets::rewrite_http_header_block(
        &req.raw_header,
        scoped.secret_resolver.as_deref(),
    ) {
        Ok(rewritten) => rewritten,
        Err(error) => return Err(credential_refusal(ctx, &req.action, &error).await),
    };
    let request = h1_head_to_h2_request(&rewritten.rewritten, ctx.request_scheme())
        .map_err(|_| Refusal::Reset(Reason::INTERNAL_ERROR))?;
    Ok(Admitted {
        request,
        ctx: scoped,
    })
}

async fn parse_head(
    head: &[u8],
    allow_encoded_slash: bool,
) -> Result<crate::l7::provider::L7Request, Refusal> {
    let options = crate::l7::path::CanonicalizeOptions {
        allow_encoded_slash,
        ..Default::default()
    };
    match crate::l7::rest::parse_synthesized_request_head(head, &options).await {
        Ok(Some(req)) => Ok(req),
        Ok(None) | Err(_) => Err(Refusal::json(
            StatusCode::BAD_REQUEST,
            "bad_request",
            "request head rejected",
        )),
    }
}

/// Emit the HTTP/1 credential-failure events and build the matching refusal.
async fn credential_refusal(
    ctx: &L7EvalContext,
    method: &str,
    error: &secrets::UnresolvedPlaceholderError,
) -> Refusal {
    let _ = reject_credential_resolution(&mut tokio::io::sink(), ctx, method, error).await;
    if error.is_endpoint_mismatch() {
        Refusal::json(
            StatusCode::FORBIDDEN,
            "credential_endpoint_mismatch",
            "Credential is not authorized for this request endpoint",
        )
    } else {
        Refusal::json(
            StatusCode::INTERNAL_SERVER_ERROR,
            "credential_unavailable",
            "Credential placeholder could not be resolved",
        )
    }
}

/// Render an HTTP/2 request head as an HTTP/1.1 header block. `:authority`
/// becomes `Host` and replaces any `host` header.
fn synthesize_h1_head(parts: &http::request::Parts) -> Result<Vec<u8>, &'static str> {
    let target = parts
        .uri
        .path_and_query()
        .map_or("/", http::uri::PathAndQuery::as_str);
    let authority = match parts.uri.authority() {
        Some(authority) => authority.as_str(),
        None => parts
            .headers
            .get(HOST)
            .and_then(|value| value.to_str().ok())
            .ok_or("request has no :authority")?,
    };
    let mut head = format!(
        "{} {target} HTTP/1.1\r\nHost: {authority}\r\n",
        parts.method
    )
    .into_bytes();
    for (name, value) in &parts.headers {
        if name == HOST {
            continue;
        }
        let value = value
            .to_str()
            .map_err(|_| "header value is not visible ASCII")?;
        head.extend_from_slice(name.as_str().as_bytes());
        head.extend_from_slice(b": ");
        head.extend_from_slice(value.as_bytes());
        head.extend_from_slice(b"\r\n");
    }
    head.extend_from_slice(b"\r\n");
    Ok(head)
}

/// Convert a (rewritten) HTTP/1.1 header block back into an HTTP/2 request head.
fn h1_head_to_h2_request(raw: &[u8], scheme: &str) -> Result<Request<()>, &'static str> {
    let text = std::str::from_utf8(raw).map_err(|_| "rewritten head is not UTF-8")?;
    let head = text.split("\r\n\r\n").next().unwrap_or_default();
    let mut lines = head.split("\r\n");
    let request_line = lines.next().ok_or("empty head")?;
    let mut parts = request_line.splitn(3, ' ');
    let method = parts.next().ok_or("missing method")?;
    let target = parts.next().ok_or("missing target")?;
    let mut authority = None;
    let mut builder = Request::builder()
        .method(method)
        .version(http::Version::HTTP_2);
    for line in lines {
        let (name, value) = line.split_once(':').ok_or("malformed header")?;
        let (name, value) = (name.trim(), value.trim());
        if name.eq_ignore_ascii_case("host") {
            authority = Some(value);
            continue;
        }
        builder = builder.header(
            HeaderName::from_bytes(name.as_bytes()).map_err(|_| "bad header name")?,
            HeaderValue::from_str(value).map_err(|_| "bad header value")?,
        );
    }
    let authority = authority.ok_or("missing host")?;
    builder
        .uri(format!("{scheme}://{authority}{target}"))
        .body(())
        .map_err(|_| "invalid request head")
}

async fn relay_response(response_future: ResponseFuture, mut respond: SendResponse<Bytes>) {
    // Dropping the response future on a client reset cancels the upstream stream.
    let response = tokio::select! {
        response = response_future => response,
        _ = poll_fn(|cx| respond.poll_reset(cx)) => return,
    };
    let response = match response {
        Ok(response) => response,
        Err(error) => {
            respond.send_reset(error.reason().unwrap_or(Reason::INTERNAL_ERROR));
            return;
        }
    };
    let (parts, body) = response.into_parts();
    let end_of_stream = body.is_end_stream();
    let Ok(send) = respond.send_response(Response::from_parts(parts, ()), end_of_stream) else {
        return;
    };
    if !end_of_stream {
        let _ = pump(body, send, false).await;
    }
}

/// Forward DATA and trailers from `recv` to `send`, releasing receive window
/// only after the bytes were accepted by the other side's flow control.
async fn pump(
    mut recv: RecvStream,
    mut send: SendStream<Bytes>,
    scan_markers: bool,
) -> Result<(), Reason> {
    let mut tail = Vec::new();
    loop {
        let next = tokio::select! {
            next = recv.data() => next,
            reset = poll_fn(|cx| send.poll_reset(cx)) => {
                return Err(reset.unwrap_or(Reason::CANCEL));
            }
        };
        let Some(chunk) = next else { break };
        let mut chunk = match chunk {
            Ok(chunk) => chunk,
            Err(error) => {
                let reason = error.reason().unwrap_or(Reason::CANCEL);
                send.send_reset(reason);
                return Err(reason);
            }
        };
        let len = chunk.len();
        if scan_markers && carries_marker(&mut tail, &chunk) {
            send.send_reset(Reason::CANCEL);
            return Err(Reason::CANCEL);
        }
        while !chunk.is_empty() {
            send.reserve_capacity(chunk.len());
            let capacity = poll_fn(|cx| {
                if let Poll::Ready(reset) = send.poll_reset(cx) {
                    return Poll::Ready(Err(reset.unwrap_or(Reason::CANCEL)));
                }
                send.poll_capacity(cx).map(|capacity| match capacity {
                    Some(Ok(capacity)) => Ok(capacity),
                    _ => Err(Reason::CANCEL),
                })
            })
            .await?;
            let n = capacity.min(chunk.len());
            if n > 0 {
                send.send_data(chunk.split_to(n), false)
                    .map_err(|_| Reason::CANCEL)?;
            }
        }
        let _ = recv.flow_control().release_capacity(len);
    }
    let trailers = match recv.trailers().await {
        Ok(trailers) => trailers,
        Err(error) => {
            let reason = error.reason().unwrap_or(Reason::CANCEL);
            send.send_reset(reason);
            return Err(reason);
        }
    };
    match trailers {
        Some(trailers) => {
            if scan_markers
                && trailers.values().any(|value| {
                    secrets::contains_reserved_credential_marker_bytes(value.as_bytes())
                })
            {
                send.send_reset(Reason::CANCEL);
                return Err(Reason::CANCEL);
            }
            send.send_trailers(trailers).map_err(|_| Reason::CANCEL)
        }
        None => send
            .send_data(Bytes::new(), true)
            .map_err(|_| Reason::CANCEL),
    }
}

/// Scan a DATA chunk for a reserved credential marker, carrying a short tail
/// so a marker split across frames is still found.
fn carries_marker(tail: &mut Vec<u8>, chunk: &[u8]) -> bool {
    let mut window = std::mem::take(tail);
    window.extend_from_slice(chunk);
    let found = secrets::contains_reserved_credential_marker_bytes(&window);
    let keep = window.len().min(secrets::CREDENTIAL_MARKER_SCAN_TAIL_BYTES);
    *tail = window[window.len() - keep..].to_vec();
    found
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::l7::tls::{
        CertCache, ProxyTlsState, SandboxCa, build_upstream_client_config,
        tls_connect_upstream_alpn, tls_terminate_client_alpn,
    };
    use crate::opa::{NetworkInput, OpaEngine};
    use openshell_core::secrets::SecretResolver;
    use std::path::PathBuf;
    use std::sync::Arc;
    use std::time::Duration;
    use tokio::io::{AsyncReadExt, AsyncWriteExt};
    use tokio::sync::mpsc;

    const TEST_POLICY: &str = include_str!("../../data/sandbox-policy.rego");
    const HOST: &str = "api.example.test";
    const POLICY_DATA: &str = r#"
network_policies:
  rest_api:
    name: rest_api
    endpoints:
      - host: api.example.test
        port: 443
        protocol: rest
        enforcement: enforce
        rules:
          - allow:
              method: GET
              path: "/v1/**"
          - allow:
              method: POST
              path: "/grpc.Service/**"
    binaries:
      - { path: /usr/bin/curl }
"#;

    /// What the in-process upstream received on one request.
    #[derive(Debug)]
    struct Seen {
        path: String,
        headers: Vec<(String, String)>,
        body: Vec<u8>,
        reset: bool,
    }

    impl Seen {
        fn header(&self, name: &str) -> Option<&str> {
            self.headers
                .iter()
                .find(|(n, _)| n == name)
                .map(|(_, v)| v.as_str())
        }

        fn carries_marker(&self) -> bool {
            secrets::contains_reserved_credential_marker(&self.path)
                || self
                    .headers
                    .iter()
                    .any(|(_, v)| secrets::contains_reserved_credential_marker(v))
                || secrets::contains_reserved_credential_marker_bytes(&self.body)
        }
    }

    struct Fixture {
        configs: Vec<L7EndpointConfig>,
        opa: Arc<OpaEngine>,
        generation: u64,
        ctx: Arc<L7EvalContext>,
        proxy_tls: Arc<ProxyTlsState>,
        sandbox_ca_pem: String,
        upstream_addr: std::net::SocketAddr,
        seen: mpsc::UnboundedReceiver<Seen>,
        /// Placeholders handed to the "sandbox": token and modal secret.
        token: String,
        secret: String,
        /// The build-time opt-in list (`HTTP2_ENDPOINTS`) for this proxy.
        opted_in: &'static str,
    }

    const OPTED_IN: &str = "other.example.test:443, API.example.test:443";

    async fn fixture(upstream_h2: bool) -> Fixture {
        fixture_with(upstream_h2, POLICY_DATA, OPTED_IN).await
    }

    async fn fixture_with(upstream_h2: bool, policy_data: &str, opted_in: &'static str) -> Fixture {
        let engine = OpaEngine::from_strings(TEST_POLICY, policy_data).unwrap();
        let input = NetworkInput {
            host: HOST.into(),
            port: 443,
            binary_path: PathBuf::from("/usr/bin/curl"),
            binary_sha256: "unused".into(),
            ancestors: vec![],
            cmdline_paths: vec![],
        };
        let (endpoint_config, generation) = engine
            .query_endpoint_config_with_generation(&input)
            .unwrap();
        let config = crate::l7::parse_l7_config(&endpoint_config.unwrap()).unwrap();

        let (child_env, resolver) = SecretResolver::from_provider_env(
            [
                ("TOKEN".to_string(), "real-token".to_string()),
                ("MODAL_SECRET".to_string(), "real-secret".to_string()),
            ]
            .into_iter()
            .collect(),
        );
        let ctx = L7EvalContext {
            host: HOST.into(),
            port: 443,
            request_default_port: Some(443),
            policy_name: "rest_api".into(),
            binary_path: "/usr/bin/curl".into(),
            secret_resolver: resolver.map(Arc::new),
            ..Default::default()
        };

        let upstream_ca = SandboxCa::generate().unwrap();
        let upstream_ca_pem = upstream_ca.cert_pem().to_string();
        let upstream_tls = ProxyTlsState::new(
            CertCache::new(upstream_ca),
            build_upstream_client_config("").unwrap(),
        );
        let (seen_tx, seen) = mpsc::unbounded_channel();
        let upstream_addr = spawn_upstream(upstream_tls, upstream_h2, seen_tx).await;

        let sandbox_ca = SandboxCa::generate().unwrap();
        let sandbox_ca_pem = sandbox_ca.cert_pem().to_string();
        let proxy_tls = ProxyTlsState::new(
            CertCache::new(sandbox_ca),
            build_upstream_client_config(&upstream_ca_pem).unwrap(),
        );
        Fixture {
            configs: vec![config],
            opa: Arc::new(engine),
            generation,
            ctx: Arc::new(ctx),
            proxy_tls: Arc::new(proxy_tls),
            sandbox_ca_pem,
            upstream_addr,
            seen,
            token: child_env["TOKEN"].clone(),
            secret: child_env["MODAL_SECRET"].clone(),
            opted_in,
        }
    }

    /// Upstream: h2 (echoes the body, adds grpc trailers) or HTTP/1.1 only.
    async fn spawn_upstream(
        tls: ProxyTlsState,
        h2: bool,
        seen: mpsc::UnboundedSender<Seen>,
    ) -> std::net::SocketAddr {
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        tokio::spawn(async move {
            loop {
                let Ok((tcp, _)) = listener.accept().await else {
                    return;
                };
                let Ok((mut stream, negotiated_h2)) =
                    tls_terminate_client_alpn(tcp, &tls, HOST, h2).await
                else {
                    continue;
                };
                let seen = seen.clone();
                tokio::spawn(async move {
                    if negotiated_h2 {
                        serve_h2(stream, seen).await;
                    } else {
                        serve_h1(&mut stream, seen).await;
                    }
                });
            }
        });
        addr
    }

    async fn serve_h2<S>(io: S, seen: mpsc::UnboundedSender<Seen>)
    where
        S: AsyncRead + AsyncWrite + Unpin + Send + 'static,
    {
        let mut conn = ::h2::server::handshake(io).await.unwrap();
        while let Some(Ok((request, mut respond))) = conn.accept().await {
            let seen = seen.clone();
            tokio::spawn(async move {
                let (parts, mut body) = request.into_parts();
                let headers = parts
                    .headers
                    .iter()
                    .map(|(n, v)| {
                        (
                            n.as_str().to_string(),
                            String::from_utf8_lossy(v.as_bytes()).into_owned(),
                        )
                    })
                    .collect::<Vec<_>>();
                let grpc = parts
                    .headers
                    .get("content-type")
                    .is_some_and(|v| v.as_bytes().starts_with(b"application/grpc"));
                let mut data = Vec::new();
                let mut reset = false;
                while let Some(chunk) = body.data().await {
                    match chunk {
                        Ok(chunk) => {
                            let _ = body.flow_control().release_capacity(chunk.len());
                            data.extend_from_slice(&chunk);
                        }
                        Err(_) => {
                            reset = true;
                            break;
                        }
                    }
                }
                let request_trailers = if reset {
                    None
                } else {
                    body.trailers().await.ok().flatten()
                };
                let _ = request_trailers;
                let path = parts.uri.path().to_string();
                seen.send(Seen {
                    path: path.clone(),
                    headers,
                    body: data.clone(),
                    reset,
                })
                .unwrap();
                if reset {
                    return;
                }
                let mut head = Response::builder().status(200).header("x-path", path);
                if grpc {
                    head = head.header("content-type", "application/grpc");
                }
                let mut send = respond
                    .send_response(head.body(()).unwrap(), false)
                    .unwrap();
                send.send_data(Bytes::from(data), !grpc).unwrap();
                if grpc {
                    let mut trailers = http::HeaderMap::new();
                    trailers.insert("grpc-status", HeaderValue::from_static("0"));
                    trailers.insert("grpc-message", HeaderValue::from_static("ok"));
                    send.send_trailers(trailers).unwrap();
                }
            });
        }
    }

    async fn serve_h1<S>(io: &mut S, seen: mpsc::UnboundedSender<Seen>)
    where
        S: AsyncRead + AsyncWrite + Unpin,
    {
        let mut buf = Vec::new();
        let mut byte = [0u8; 1];
        while !buf.ends_with(b"\r\n\r\n") {
            if io.read(&mut byte).await.unwrap_or(0) == 0 {
                return;
            }
            buf.push(byte[0]);
        }
        let text = String::from_utf8_lossy(&buf).into_owned();
        let mut lines = text.split("\r\n");
        let path = lines
            .next()
            .and_then(|l| l.split(' ').nth(1))
            .unwrap_or_default()
            .to_string();
        let headers = lines
            .filter_map(|l| l.split_once(':'))
            .map(|(n, v)| (n.trim().to_ascii_lowercase(), v.trim().to_string()))
            .collect();
        seen.send(Seen {
            path,
            headers,
            body: Vec::new(),
            reset: false,
        })
        .unwrap();
        let _ = io
            .write_all(b"HTTP/1.1 200 OK\r\nContent-Length: 2\r\nConnection: close\r\n\r\nok")
            .await;
        let _ = io.shutdown().await;
    }

    /// The proxy side of one CONNECT tunnel after `200`, as in `proxy.rs`.
    fn spawn_proxy(
        f: &Fixture,
        client_io: tokio::io::DuplexStream,
    ) -> tokio::task::JoinHandle<Result<()>> {
        let engine = f.opa.clone_engine_for_tunnel(f.generation).unwrap();
        let (configs, ctx, tls, addr) = (
            f.configs.clone(),
            Arc::clone(&f.ctx),
            Arc::clone(&f.proxy_tls),
            f.upstream_addr,
        );
        let offer_h2 = should_offer_h2(f.opted_in, &ctx, &configs, || {
            engine
                .query_middleware_chain(&crate::l7::middleware::middleware_network_input(&ctx))
                .is_ok_and(|chain| chain.is_empty())
        });
        tokio::spawn(async move {
            let (mut tls_client, client_h2) =
                tls_terminate_client_alpn(client_io, &tls, HOST, offer_h2).await?;
            let config = if client_h2 {
                tls.upstream_config_h2()
            } else {
                tls.upstream_config()
            };
            let tcp = tokio::net::TcpStream::connect(addr)
                .await
                .into_diagnostic()?;
            let (mut tls_upstream, upstream_h2) =
                tls_connect_upstream_alpn(tcp, HOST, config).await?;
            if client_h2 {
                relay_h2(
                    &mut tls_client,
                    upstream_h2.then_some(&mut tls_upstream),
                    &configs,
                    &engine,
                    &ctx,
                )
                .await
            } else {
                crate::l7::relay::relay_with_inspection(
                    &configs[0],
                    engine,
                    &mut tls_client,
                    &mut tls_upstream,
                    &ctx,
                )
                .await
            }
        })
    }

    async fn sandbox_tls(
        f: &Fixture,
        alpn: &[&[u8]],
    ) -> (
        tokio_rustls::client::TlsStream<tokio::io::DuplexStream>,
        tokio::task::JoinHandle<Result<()>>,
    ) {
        let (app, proxy_side) = tokio::io::duplex(64 * 1024);
        let proxy = spawn_proxy(f, proxy_side);
        let mut config = (*build_upstream_client_config(&f.sandbox_ca_pem).unwrap()).clone();
        config.alpn_protocols = alpn.iter().map(|p| p.to_vec()).collect();
        let connector = tokio_rustls::TlsConnector::from(Arc::new(config));
        let name = rustls::pki_types::ServerName::try_from(HOST).unwrap();
        let stream = connector.connect(name, app).await.unwrap();
        (stream, proxy)
    }

    async fn h2_client(f: &Fixture) -> (SendRequest<Bytes>, tokio::task::JoinHandle<Result<()>>) {
        let (stream, proxy) = sandbox_tls(f, &[b"h2", b"http/1.1"]).await;
        assert_eq!(stream.get_ref().1.alpn_protocol(), Some(&b"h2"[..]));
        let (sender, conn) = ::h2::client::handshake(stream).await.unwrap();
        tokio::spawn(async move {
            let _ = conn.await;
        });
        (sender, proxy)
    }

    fn get(path: &str, headers: &[(&str, &str)]) -> Request<()> {
        let mut builder = Request::builder()
            .method("GET")
            .uri(format!("https://{HOST}{path}"));
        for (name, value) in headers {
            builder = builder.header(*name, *value);
        }
        builder.body(()).unwrap()
    }

    /// Send a request and collect status, body, and trailers.
    async fn exchange(
        sender: &SendRequest<Bytes>,
        request: Request<()>,
        body: Option<&[u8]>,
    ) -> std::result::Result<(StatusCode, Vec<u8>, Option<http::HeaderMap>), ::h2::Error> {
        let mut sender = sender.clone().ready().await?;
        let (response, mut send) = sender.send_request(request, body.is_none())?;
        if let Some(body) = body {
            send.send_data(Bytes::copy_from_slice(body), true)?;
        }
        let response = tokio::time::timeout(Duration::from_secs(5), response)
            .await
            .expect("response in time")?;
        let status = response.status();
        let mut recv = response.into_body();
        let mut data = Vec::new();
        while let Some(chunk) = recv.data().await {
            let chunk = chunk?;
            let _ = recv.flow_control().release_capacity(chunk.len());
            data.extend_from_slice(&chunk);
        }
        let trailers = recv.trailers().await?;
        Ok((status, data, trailers))
    }

    async fn next_seen(f: &mut Fixture) -> Seen {
        tokio::time::timeout(Duration::from_secs(5), f.seen.recv())
            .await
            .expect("upstream request in time")
            .expect("upstream channel open")
    }

    async fn assert_upstream_quiet(f: &mut Fixture) {
        let result = tokio::time::timeout(Duration::from_millis(200), f.seen.recv()).await;
        assert!(result.is_err(), "upstream must not see a request");
    }

    #[tokio::test]
    async fn header_placeholders_are_substituted_over_h2() {
        let mut f = fixture(true).await;
        let (sender, _proxy) = h2_client(&f).await;
        let bearer = format!("Bearer {}", f.token);
        let request = get(
            "/v1/apps",
            &[
                ("authorization", bearer.as_str()),
                ("x-modal-token-secret", f.secret.as_str()),
            ],
        );
        let (status, _, _) = exchange(&sender, request, None).await.unwrap();
        assert_eq!(status, StatusCode::OK);
        let seen = next_seen(&mut f).await;
        assert_eq!(seen.path, "/v1/apps");
        assert_eq!(seen.header("authorization"), Some("Bearer real-token"));
        assert_eq!(seen.header("x-modal-token-secret"), Some("real-secret"));
        assert!(!seen.carries_marker());
    }

    #[tokio::test]
    async fn denied_stream_does_not_affect_other_streams() {
        let mut f = fixture(true).await;
        let (sender, _proxy) = h2_client(&f).await;
        let token = f.token.clone();
        let bearer = format!("Bearer {token}");
        let auth = [("authorization", bearer.as_str())];
        let (allowed, denied) = tokio::join!(
            exchange(&sender, get("/v1/one", &auth), None),
            exchange(&sender, get("/admin/secret", &auth), None),
        );
        assert_eq!(allowed.unwrap().0, StatusCode::OK);
        let (status, body, _) = denied.unwrap();
        assert_eq!(status, StatusCode::FORBIDDEN);
        assert!(String::from_utf8_lossy(&body).contains("policy_denied"));
        // The connection survives the denial.
        let (status, _, _) = exchange(&sender, get("/v1/two", &auth), None)
            .await
            .unwrap();
        assert_eq!(status, StatusCode::OK);
        let mut paths = vec![next_seen(&mut f).await.path, next_seen(&mut f).await.path];
        paths.sort();
        assert_eq!(paths, ["/v1/one", "/v1/two"]);
        assert_upstream_quiet(&mut f).await;
    }

    #[tokio::test]
    async fn unresolvable_placeholder_fails_the_stream_closed() {
        let mut f = fixture(true).await;
        let (sender, _proxy) = h2_client(&f).await;
        let unknown = secrets::placeholder_for_env_key("NOT_CONFIGURED");
        let request = get("/v1/apps", &[("x-api-key", unknown.as_str())]);
        let (status, _, _) = exchange(&sender, request, None).await.unwrap();
        assert_eq!(status, StatusCode::INTERNAL_SERVER_ERROR);
        assert_upstream_quiet(&mut f).await;
        let (status, _, _) = exchange(&sender, get("/v1/after", &[]), None)
            .await
            .unwrap();
        assert_eq!(status, StatusCode::OK);
        assert_eq!(next_seen(&mut f).await.path, "/v1/after");
    }

    #[tokio::test]
    async fn grpc_post_streams_body_and_trailers() {
        let mut f = fixture(true).await;
        let (sender, _proxy) = h2_client(&f).await;
        let request = Request::builder()
            .method("POST")
            .uri(format!("https://{HOST}/grpc.Service/Call"))
            .header("content-type", "application/grpc")
            .header("te", "trailers")
            .header("x-modal-token-id", f.token.as_str())
            .body(())
            .unwrap();
        let message = b"\x00\x00\x00\x00\x05hello";
        let (status, body, trailers) = exchange(&sender, request, Some(message)).await.unwrap();
        assert_eq!(status, StatusCode::OK);
        assert_eq!(body, message);
        let trailers = trailers.expect("grpc trailers");
        assert_eq!(trailers["grpc-status"], "0");
        let seen = next_seen(&mut f).await;
        assert_eq!(seen.header("x-modal-token-id"), Some("real-token"));
        assert_eq!(seen.header("te"), Some("trailers"));
        assert_eq!(seen.body, message);
    }

    #[tokio::test]
    async fn body_placeholder_resets_the_stream() {
        let mut f = fixture(true).await;
        let (sender, _proxy) = h2_client(&f).await;
        let request = Request::builder()
            .method("POST")
            .uri(format!("https://{HOST}/grpc.Service/Call"))
            .header("content-type", "application/grpc")
            .body(())
            .unwrap();
        let body = format!("\x00\x00\x00\x00\x40{}", f.token);
        let result = exchange(&sender, request, Some(body.as_bytes())).await;
        assert!(result.is_err(), "stream must be reset");
        let seen = next_seen(&mut f).await;
        assert!(seen.reset);
        assert!(!seen.carries_marker());
    }

    #[tokio::test]
    async fn h1_client_still_uses_http1_path() {
        let mut f = fixture(true).await;
        let (mut stream, _proxy) = sandbox_tls(&f, &[b"http/1.1"]).await;
        assert_eq!(stream.get_ref().1.alpn_protocol(), Some(&b"http/1.1"[..]));
        let request = format!(
            "GET /v1/h1 HTTP/1.1\r\nHost: {HOST}\r\nAuthorization: Bearer {}\r\nConnection: close\r\n\r\n",
            f.token
        );
        stream.write_all(request.as_bytes()).await.unwrap();
        let mut response = Vec::new();
        let _ =
            tokio::time::timeout(Duration::from_secs(5), stream.read_to_end(&mut response)).await;
        assert!(String::from_utf8_lossy(&response).starts_with("HTTP/1.1 200"));
        let seen = next_seen(&mut f).await;
        assert_eq!(seen.path, "/v1/h1");
        assert_eq!(seen.header("authorization"), Some("Bearer real-token"));
        assert!(!seen.carries_marker());
    }

    async fn negotiated_alpn(f: &Fixture) -> Option<Vec<u8>> {
        let (stream, _proxy) = sandbox_tls(f, &[b"h2", b"http/1.1"]).await;
        stream.get_ref().1.alpn_protocol().map(<[u8]>::to_vec)
    }

    #[tokio::test]
    async fn endpoint_without_opt_in_offers_only_http1() {
        for opted_in in ["", "other.example.test:443", "api.example.test:8443"] {
            let f = fixture_with(true, POLICY_DATA, opted_in).await;
            assert!(f.ctx.secret_resolver.is_some());
            assert_eq!(
                negotiated_alpn(&f).await.as_deref(),
                Some(&b"http/1.1"[..]),
                "{opted_in:?}"
            );
        }
        let f = fixture(true).await;
        assert_eq!(negotiated_alpn(&f).await.as_deref(), Some(&b"h2"[..]));
    }

    #[tokio::test]
    async fn route_with_middleware_never_offers_h2() {
        let data = format!(
            r#"
network_middlewares:
  request-middleware:
    middleware: openshell/regex
    on_error: fail_closed
    endpoints:
      include: ["{HOST}"]
{}"#,
            POLICY_DATA.trim_start_matches('\n')
        );
        let f = fixture_with(true, &data, OPTED_IN).await;
        assert_eq!(negotiated_alpn(&f).await.as_deref(), Some(&b"http/1.1"[..]));
    }

    #[tokio::test]
    async fn non_origin_form_path_is_refused_for_that_stream() {
        let mut f = fixture(true).await;
        let (sender, _proxy) = h2_client(&f).await;
        let uri = http::Uri::from_parts({
            let mut parts = http::uri::Parts::default();
            parts.scheme = Some(http::uri::Scheme::HTTPS);
            parts.authority = Some(HOST.parse().unwrap());
            parts.path_and_query = Some(http::uri::PathAndQuery::from_static(
                "https://api.example.test/v1/x",
            ));
            parts
        })
        .unwrap();
        let request = Request::builder().method("GET").uri(uri).body(()).unwrap();
        let (status, _, _) = exchange(&sender, request, None).await.unwrap();
        assert_eq!(status, StatusCode::BAD_REQUEST);
        assert_upstream_quiet(&mut f).await;
        let (status, _, _) = exchange(&sender, get("/v1/after", &[]), None)
            .await
            .unwrap();
        assert_eq!(status, StatusCode::OK);
        assert_eq!(next_seen(&mut f).await.path, "/v1/after");
    }

    #[tokio::test]
    async fn upstream_without_h2_refuses_streams_cleanly() {
        let mut f = fixture(false).await;
        let (sender, _proxy) = h2_client(&f).await;
        let (status, _, _) = exchange(&sender, get("/v1/apps", &[]), None).await.unwrap();
        assert_eq!(status, StatusCode::BAD_GATEWAY);
        let (status, _, _) = exchange(&sender, get("/v1/again", &[]), None)
            .await
            .unwrap();
        assert_eq!(status, StatusCode::BAD_GATEWAY);
        assert_upstream_quiet(&mut f).await;
    }
}
