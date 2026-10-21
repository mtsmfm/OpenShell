// SPDX-FileCopyrightText: Copyright (c) 2025-2026 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

//! Shared relay primitives for authorized explicit-proxy egress.

use super::{EgressDecision, L7RouteSnapshot, emit_l7_tunnel_close_after_policy_change};
use crate::l7::relay::L7EvalContext;
use crate::opa::{
    NetworkAction, NetworkInput, OpaEngine, PolicyGenerationGuard, TunnelPolicyEngine,
};
use miette::{IntoDiagnostic, Result};
use openshell_core::activity::ActivitySender;
use openshell_core::endpoint_status::EndpointObservationSender;
use openshell_core::secrets::SecretResolver;
use std::sync::Arc;
use tokio::io::{AsyncRead, AsyncWrite};

enum PreparedHttpPolicy {
    Inspect {
        configs: Vec<crate::l7::L7EndpointConfig>,
        evaluator: Box<TunnelPolicyEngine>,
    },
    Passthrough {
        generation_guard: PolicyGenerationGuard,
    },
}

/// Everything an HTTP relay needs after authorization is complete.
///
/// The relay deliberately owns a generation-pinned policy primitive instead
/// of retaining access to the mutable OPA engine. Policy reloads therefore
/// fail closed through the guard or tunnel evaluator already attached here.
pub(super) struct RelayContext<'a> {
    request: &'a L7EvalContext,
    policy: PreparedHttpPolicy,
    middleware_engine: &'a OpaEngine,
}

/// Non-blocking observation channels attached to an authorized HTTP relay.
pub(super) struct RelaySignals {
    /// Receives general sandbox network activity.
    pub(super) activity: Option<ActivitySender>,
    /// Receives terminal tool server results for endpoint status reporting.
    pub(super) endpoint_observation: Option<EndpointObservationSender>,
}

/// Build the request-processing context shared by CONNECT and forward HTTP.
pub(super) fn http_context(
    decision: &EgressDecision,
    provider_credentials: Option<openshell_core::provider_credentials::ProviderCredentialState>,
    secret_resolver: Option<Arc<SecretResolver>>,
    policy_local: Option<&crate::policy_local::PolicyLocalContext>,
    agent_proposals: openshell_core::proposals::AgentProposals,
    signals: RelaySignals,
) -> L7EvalContext {
    // Provider-backed credentials must be acquired from the live state for
    // each request after middleware/token-grant awaits. Keep only the legacy
    // resolver fallback when no live provider state exists.
    let secret_resolver = provider_credentials
        .is_none()
        .then_some(secret_resolver)
        .flatten();
    // Grants use the owning sandbox instance's resolver; without one they fail closed.
    let token_grant_resolver = provider_credentials
        .as_ref()
        .and(policy_local)
        .and_then(crate::policy_local::PolicyLocalContext::token_grant_resolver);
    let workspace = policy_local
        .map(crate::policy_local::PolicyLocalContext::workspace)
        .unwrap_or_default();
    let policy_name = match &decision.action {
        NetworkAction::Allow { matched_policy } => matched_policy.clone().unwrap_or_default(),
        NetworkAction::Deny { .. } => String::new(),
    };

    L7EvalContext {
        host: decision.intent.destination.host.clone(),
        port: decision.intent.destination.port,
        request_default_port: None,
        policy_name,
        binary_path: decision
            .binary
            .as_ref()
            .map(|path| path.to_string_lossy().into_owned())
            .unwrap_or_default(),
        ancestors: decision
            .ancestors
            .iter()
            .map(|path| path.to_string_lossy().into_owned())
            .collect(),
        cmdline_paths: decision
            .cmdline_paths
            .iter()
            .map(|path| path.to_string_lossy().into_owned())
            .collect(),
        secret_resolver,
        provider_credentials,
        provider_credential_revision: None,
        provider_credential_installation_id: None,
        body_classifier: None,
        activity_tx: signals.activity,
        token_grant_resolver,
        agent_proposals,
        workspace,
        endpoint_observation_tx: signals.endpoint_observation,
    }
}

/// Pin a generation for a relay or the forward HTTP single-request path.
pub(super) fn pin_policy_generation(
    opa_engine: &OpaEngine,
    expected_generation: u64,
) -> Result<PolicyGenerationGuard> {
    opa_engine.generation_guard(expected_generation)
}

/// Clone an L7 evaluator for a relay or the forward HTTP single-request path.
pub(super) fn pin_l7_evaluator(
    opa_engine: &OpaEngine,
    expected_generation: u64,
) -> Result<TunnelPolicyEngine> {
    opa_engine.clone_engine_for_tunnel(expected_generation)
}

/// Reconstruct the policy input that authorized `decision`.
///
/// Process identity was verified when the connection was admitted, so a
/// relay is re-evaluated with that identity rather than a fresh lookup.
fn relay_policy_input(decision: &EgressDecision) -> NetworkInput {
    NetworkInput {
        host: decision.intent.destination.host.clone(),
        port: decision.intent.destination.port,
        binary_path: decision.binary.clone().unwrap_or_default(),
        binary_sha256: String::new(),
        ancestors: decision.ancestors.clone(),
        cmdline_paths: decision.cmdline_paths.clone(),
    }
}

pub(super) fn validate_route_generation(
    route: Option<&L7RouteSnapshot>,
    expected_generation: u64,
) -> Result<()> {
    if let Some(route) = route
        && route.l7_policy_generation != expected_generation
    {
        return Err(miette::miette!(
            "policy changed before CONNECT route hydration \
             [l4_generation:{} l7_generation:{}]",
            expected_generation,
            route.l7_policy_generation,
        ));
    }
    Ok(())
}

/// Prepare a generation-pinned HTTP relay at the adapter boundary.
///
/// A stale generation preserves the established CONNECT behavior: emit the
/// policy-change close event and let the adapter close the live tunnel without
/// attempting to write an HTTP response into it.
///
/// Once started, the relay survives a policy reload that admits its
/// connection identically and closes otherwise; L7 requests after the reload
/// are evaluated against the new policy.
pub(super) fn prepare_http_relay<'a>(
    route: Option<&L7RouteSnapshot>,
    opa_engine: &'a Arc<OpaEngine>,
    decision: &EgressDecision,
    request: &'a L7EvalContext,
) -> Option<RelayContext<'a>> {
    if let Err(error) = validate_route_generation(route, decision.policy_generation) {
        emit_l7_tunnel_close_after_policy_change(
            &decision.intent.destination.host,
            decision.intent.destination.port,
            error,
        );
        return None;
    }

    let policy = if let Some(route) = route.filter(|route| !route.configs.is_empty()) {
        let evaluator = match opa_engine
            .clone_engine_for_relay(decision.policy_generation, relay_policy_input(decision))
        {
            Ok(evaluator) => evaluator,
            Err(error) => {
                emit_l7_tunnel_close_after_policy_change(
                    &decision.intent.destination.host,
                    decision.intent.destination.port,
                    error,
                );
                return None;
            }
        };
        let configs = route
            .configs
            .iter()
            .map(|snapshot| snapshot.config.clone())
            .collect();
        PreparedHttpPolicy::Inspect {
            configs,
            evaluator: Box::new(evaluator),
        }
    } else {
        let generation_guard = match opa_engine
            .relay_generation_guard(decision.policy_generation, relay_policy_input(decision))
        {
            Ok(guard) => guard,
            Err(error) => {
                emit_l7_tunnel_close_after_policy_change(
                    &decision.intent.destination.host,
                    decision.intent.destination.port,
                    error,
                );
                return None;
            }
        };
        PreparedHttpPolicy::Passthrough { generation_guard }
    };

    Some(RelayContext {
        request,
        policy,
        middleware_engine: opa_engine,
    })
}

/// Pin the generation used by a raw relay so quarantine, or a policy change
/// that no longer admits the connection identically, closes streams that
/// otherwise have no request boundary at which to notice a stale decision.
pub(super) fn prepare_raw_relay(
    route: Option<&L7RouteSnapshot>,
    opa_engine: &Arc<OpaEngine>,
    decision: &EgressDecision,
) -> Option<PolicyGenerationGuard> {
    if let Err(error) = validate_route_generation(route, decision.policy_generation) {
        emit_l7_tunnel_close_after_policy_change(
            &decision.intent.destination.host,
            decision.intent.destination.port,
            error,
        );
        return None;
    }

    match opa_engine
        .relay_generation_guard(decision.policy_generation, relay_policy_input(decision))
    {
        Ok(guard) => Some(guard),
        Err(error) => {
            emit_l7_tunnel_close_after_policy_change(
                &decision.intent.destination.host,
                decision.intent.destination.port,
                error,
            );
            None
        }
    }
}

/// Relay an HTTP/1 stream using an already-authorized, generation-pinned context.
///
/// CONNECT plaintext and TLS-terminated streams both enter through this
/// function. Forward HTTP will provide a buffered first request to the same
/// boundary in the next migration step.
pub(super) async fn relay_http_stream<C, U>(
    client: &mut C,
    upstream: &mut U,
    context: RelayContext<'_>,
) -> Result<()>
where
    C: AsyncRead + AsyncWrite + Unpin + Send,
    U: AsyncRead + AsyncWrite + Unpin + Send,
{
    match context.policy {
        PreparedHttpPolicy::Inspect { configs, evaluator } if configs.len() == 1 => {
            let generation_guard = evaluator.generation_guard().clone();
            tokio::select! {
                result = crate::l7::relay::relay_with_inspection(
                    &configs[0],
                    *evaluator,
                    client,
                    upstream,
                    context.request,
                ) => result,
                () = generation_guard.wait_until_stale() => {
                    emit_stale_relay_close(context.request, &generation_guard);
                    Ok(())
                }
            }
        }
        PreparedHttpPolicy::Inspect { configs, evaluator } => {
            let generation_guard = evaluator.generation_guard().clone();
            tokio::select! {
                result = crate::l7::relay::relay_with_route_selection(
                    &configs,
                    *evaluator,
                    client,
                    upstream,
                    context.request,
                ) => result,
                () = generation_guard.wait_until_stale() => {
                    emit_stale_relay_close(context.request, &generation_guard);
                    Ok(())
                }
            }
        }
        PreparedHttpPolicy::Passthrough { generation_guard } => {
            tokio::select! {
                result = crate::l7::relay::relay_passthrough_with_credentials(
                    client,
                    upstream,
                    context.request,
                    &generation_guard,
                    Some(context.middleware_engine),
                ) => result,
                () = generation_guard.wait_until_stale() => {
                    emit_stale_relay_close(context.request, &generation_guard);
                    Ok(())
                }
            }
        }
    }
}

/// Whether to offer `h2` to the sandbox client (`l7::http2::should_offer_h2`).
pub(super) fn offer_h2(
    route: Option<&L7RouteSnapshot>,
    opa_engine: &OpaEngine,
    request: &L7EvalContext,
) -> bool {
    let Some(route) = route else {
        return false;
    };
    crate::l7::http2::should_offer_h2(
        crate::l7::http2::HTTP2_ENDPOINTS,
        request,
        route.configs.iter().map(|snapshot| &snapshot.config),
        || {
            opa_engine
                .query_middleware_chain_with_generation(
                    &crate::l7::middleware::middleware_network_input(request),
                )
                .is_ok_and(|(chain, _)| chain.is_empty())
        },
    )
}

/// Relay an HTTP/2 connection. `upstream` is `None` when the upstream did not
/// negotiate `h2`.
pub(super) async fn relay_h2_stream<C, U>(
    client: C,
    upstream: Option<U>,
    context: RelayContext<'_>,
) -> Result<()>
where
    C: AsyncRead + AsyncWrite + Unpin + Send,
    U: AsyncRead + AsyncWrite + Unpin + Send,
{
    match context.policy {
        PreparedHttpPolicy::Inspect { configs, evaluator } => {
            let generation_guard = evaluator.generation_guard().clone();
            tokio::select! {
                result = crate::l7::http2::relay_h2(
                    client,
                    upstream,
                    &configs,
                    &evaluator,
                    context.request,
                ) => result,
                () = generation_guard.wait_until_stale() => {
                    emit_stale_relay_close(context.request, &generation_guard);
                    Ok(())
                }
            }
        }
        PreparedHttpPolicy::Passthrough { .. } => {
            Err(miette::miette!("HTTP/2 requires an inspected L7 route"))
        }
    }
}

// Exercise the production single/multiple-route dispatch from L7 fixtures.
#[cfg(test)]
pub async fn relay_inspected_http_stream_for_test<C, U>(
    client: &mut C,
    upstream: &mut U,
    configs: Vec<crate::l7::L7EndpointConfig>,
    evaluator: TunnelPolicyEngine,
    middleware_engine: &OpaEngine,
    request: &L7EvalContext,
) -> Result<()>
where
    C: AsyncRead + AsyncWrite + Unpin + Send,
    U: AsyncRead + AsyncWrite + Unpin + Send,
{
    relay_http_stream(
        client,
        upstream,
        RelayContext {
            request,
            policy: PreparedHttpPolicy::Inspect {
                configs,
                evaluator: Box::new(evaluator),
            },
            middleware_engine,
        },
    )
    .await
}

/// Relay a policy-authorized raw TCP stream.
pub(super) async fn relay_tcp<C, U>(
    client: &mut C,
    upstream: &mut U,
    generation_guard: &PolicyGenerationGuard,
    request: &L7EvalContext,
) -> Result<()>
where
    C: AsyncRead + AsyncWrite + Unpin,
    U: AsyncRead + AsyncWrite + Unpin,
{
    tokio::select! {
        result = tokio::io::copy_bidirectional(client, upstream) => {
            result.into_diagnostic()?;
        }
        () = generation_guard.wait_until_stale() => {
            emit_stale_relay_close(request, generation_guard);
        }
    }
    Ok(())
}

fn emit_stale_relay_close(request: &L7EvalContext, guard: &PolicyGenerationGuard) {
    emit_l7_tunnel_close_after_policy_change(
        &request.host,
        request.port,
        miette::miette!(
            "policy generation is stale [captured_generation:{} current_generation:{}]",
            guard.captured_generation(),
            guard.current_generation(),
        ),
    );
}

#[cfg(test)]
mod tests {
    use super::super::{EgressIntent, EndpointDecision, ProcessIdentityEvidence};
    use super::*;

    const POLICY_REGO: &str = include_str!("../../data/sandbox-policy.rego");
    const EMPTY_POLICY_DATA: &str = "network_policies: {}\n";

    fn decision(policy_generation: u64) -> EgressDecision {
        EgressDecision {
            intent: EgressIntent::connect("example.com".to_string(), 80),
            action: NetworkAction::Allow {
                matched_policy: Some("test".to_string()),
            },
            policy_generation,
            identity: ProcessIdentityEvidence::Available,
            endpoint: EndpointDecision::default(),
            binary: None,
            binary_pid: None,
            ancestors: vec![],
            cmdline_paths: vec![],
        }
    }

    fn request_context() -> L7EvalContext {
        L7EvalContext {
            host: "example.com".to_string(),
            port: 80,
            request_default_port: Some(80),
            policy_name: "test".to_string(),
            binary_path: String::new(),
            ancestors: vec![],
            cmdline_paths: vec![],
            secret_resolver: None,
            provider_credentials: None,
            provider_credential_revision: None,
            provider_credential_installation_id: None,
            body_classifier: None,
            activity_tx: None,
            token_grant_resolver: None,
            agent_proposals: openshell_core::proposals::AgentProposals::default(),
            workspace: String::new(),
            endpoint_observation_tx: None,
        }
    }

    async fn assert_response_lifecycle<C, P>(mut caller: C, mut client: P)
    where
        C: AsyncRead + AsyncWrite + Unpin,
        P: AsyncRead + AsyncWrite + Unpin + Send,
    {
        use tokio::io::{AsyncReadExt, AsyncWriteExt};

        let (mut upstream, mut server) = tokio::io::duplex(1024);
        let engine = Arc::new(OpaEngine::from_strings(POLICY_REGO, EMPTY_POLICY_DATA).unwrap());
        let decision = decision(engine.current_generation());
        let request = request_context();
        let context = prepare_http_relay(None, &engine, &decision, &request).unwrap();
        let persistent = b"HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello";
        // Larger than either transport buffer: closing must drain the body.
        let body = vec![b'x'; 64 * 1024];
        let mut closing = format!(
            "HTTP/1.1 200 OK\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
            body.len()
        )
        .into_bytes();
        closing.extend_from_slice(&body);
        let relay = Box::pin(relay_http_stream(&mut client, &mut upstream, context));
        let serve = async {
            for response in [persistent.as_slice(), closing.as_slice()] {
                let mut request = Vec::new();
                while !request.ends_with(b"\r\n\r\n") {
                    request.push(server.read_u8().await.unwrap());
                    assert!(request.len() < 4096);
                }
                assert!(request.starts_with(b"GET / HTTP/1.1\r\n"));
                server.write_all(response).await.unwrap();
                server.flush().await.unwrap();
            }
            // Retain the upstream socket: response headers decide persistence.
        };
        let receive = async {
            let request = b"GET / HTTP/1.1\r\nHost: example.com\r\n\r\n";
            caller.write_all(request).await.unwrap();
            caller.flush().await.unwrap();
            let mut first = vec![0; persistent.len()];
            caller.read_exact(&mut first).await.unwrap();
            assert_eq!(first, persistent);
            // A real second exchange verifies reuse, without a timing assertion.
            caller.write_all(request).await.unwrap();
            caller.flush().await.unwrap();
            let mut second = Vec::new();
            // TLS must return clean EOF, not UnexpectedEof from a dropped socket.
            caller.read_to_end(&mut second).await.unwrap();
            assert_eq!(second, closing);
        };
        tokio::time::timeout(std::time::Duration::from_secs(5), async {
            let (result, (), ()) = tokio::join!(relay, serve, receive);
            result.unwrap();
        })
        .await
        .expect("response delivery and EOF must not await another request");
    }

    #[tokio::test]
    async fn http_relay_reuses_then_closes_after_complete_response() {
        let (caller, client) = tokio::io::duplex(1024);
        assert_response_lifecycle(caller, client).await;
    }

    #[tokio::test]
    async fn tls_http_relay_reuses_then_sends_close_notify_after_complete_response() {
        use crate::l7::tls::{CertCache, ProxyTlsState, SandboxCa, tls_terminate_client};
        let ca = SandboxCa::generate().unwrap();
        let mut roots = rustls::RootCertStore::empty();
        for cert in rustls_pemfile::certs(&mut ca.cert_pem().as_bytes()) {
            roots.add(cert.unwrap()).unwrap();
        }
        let config = Arc::new(
            openshell_crypto::tls::client_builder()
                .with_root_certificates(roots)
                .with_no_client_auth(),
        );
        let state = ProxyTlsState::new(CertCache::new(ca), config.clone());
        let connector = tokio_rustls::TlsConnector::from(config);
        let (caller, client) = tokio::io::duplex(1024);
        let (caller, client) = tokio::time::timeout(std::time::Duration::from_secs(5), async {
            tokio::join!(
                connector.connect(
                    rustls::pki_types::ServerName::try_from("example.com").unwrap(),
                    caller
                ),
                tls_terminate_client(client, &state, "example.com"),
            )
        })
        .await
        .expect("TLS handshake must complete");
        assert_response_lifecycle(caller.unwrap(), client.unwrap()).await;
    }

    #[test]
    fn relay_without_route_pins_l4_decision_generation() {
        let engine = Arc::new(OpaEngine::from_strings(POLICY_REGO, EMPTY_POLICY_DATA).unwrap());
        let decision = decision(engine.current_generation());
        let request = request_context();

        let context = prepare_http_relay(None, &engine, &decision, &request)
            .expect("current L4 generation should prepare a relay");
        let PreparedHttpPolicy::Passthrough { generation_guard } = context.policy else {
            panic!("route-less relay should use a generation guard");
        };

        assert_eq!(
            generation_guard.captured_generation(),
            decision.policy_generation
        );
    }

    #[test]
    fn empty_hydrated_route_cannot_replace_stale_l4_generation() {
        let engine = Arc::new(OpaEngine::from_strings(POLICY_REGO, EMPTY_POLICY_DATA).unwrap());
        let decision = decision(u64::MAX);
        let route = L7RouteSnapshot {
            configs: vec![],
            l7_policy_generation: engine.current_generation(),
        };
        let request = request_context();

        assert!(
            prepare_http_relay(Some(&route), &engine, &decision, &request).is_none(),
            "a current L7 lookup must not freshen a stale L4 allow"
        );
    }

    #[test]
    fn inspected_route_cannot_replace_stale_l4_generation() {
        let engine = Arc::new(OpaEngine::from_strings(POLICY_REGO, EMPTY_POLICY_DATA).unwrap());
        let decision = decision(u64::MAX);
        let route = L7RouteSnapshot {
            configs: vec![super::super::L7ConfigSnapshot {
                config: crate::l7::L7EndpointConfig {
                    protocol: crate::l7::L7Protocol::Rest,
                    endpoint_id: String::new(),
                    policy_hash: String::new(),
                    path: "/**".to_string(),
                    tls: crate::l7::TlsMode::Auto,
                    enforcement: crate::l7::EnforcementMode::Enforce,
                    graphql_max_body_bytes: crate::l7::graphql::DEFAULT_MAX_BODY_BYTES,
                    json_rpc_max_body_bytes: crate::l7::jsonrpc::DEFAULT_MAX_BODY_BYTES,
                    mcp_strict_tool_names: true,
                    mcp_versions: Vec::new(),
                    allow_encoded_slash: false,
                    websocket_credential_rewrite: false,
                    request_body_credential_rewrite: false,
                    allow_uninspected_credentials: false,
                    provider_credentialed: false,
                    websocket_graphql_policy: false,
                    credential_signing: crate::l7::CredentialSigning::None,
                    signing_service: String::new(),
                    signing_region: String::new(),
                },
            }],
            l7_policy_generation: engine.current_generation(),
        };
        let request = request_context();

        assert!(
            prepare_http_relay(Some(&route), &engine, &decision, &request).is_none(),
            "an inspected route must use the generation that authorized CONNECT"
        );
    }

    #[test]
    fn raw_route_cannot_replace_stale_l4_generation() {
        let engine = Arc::new(OpaEngine::from_strings(POLICY_REGO, EMPTY_POLICY_DATA).unwrap());
        let decision = decision(u64::MAX);
        let route = L7RouteSnapshot {
            configs: vec![],
            l7_policy_generation: engine.current_generation(),
        };

        assert!(
            prepare_raw_relay(Some(&route), &engine, &decision).is_none(),
            "a raw relay must not freshen a stale L4 allow"
        );
    }

    #[test]
    fn stale_generation_fails_before_relay_context_is_created() {
        let engine = Arc::new(OpaEngine::from_strings(POLICY_REGO, EMPTY_POLICY_DATA).unwrap());
        let decision = decision(engine.current_generation());
        let request = request_context();
        engine.reload(POLICY_REGO, EMPTY_POLICY_DATA).unwrap();

        assert!(
            prepare_http_relay(None, &engine, &decision, &request).is_none(),
            "policy reload must prevent a stale relay from starting"
        );
    }

    const STREAM_ENDPOINT: &str = "
network_policies:
  stream:
    name: stream
    endpoints:
      - { host: example.com, port: 80 }
    binaries:
      - { path: /usr/bin/curl }
";
    const STREAM_REST_ENDPOINT: &str = "
network_policies:
  stream:
    name: stream
    endpoints:
      - host: example.com
        port: 80
        protocol: rest
        enforcement: enforce
        rules:
          - allow:
              method: GET
              path: /**
    binaries:
      - { path: /usr/bin/curl }
";
    const UNRELATED_POLICY: &str = "
  other:
    name: other
    endpoints:
      - { host: other.example.com, port: 443 }
    binaries:
      - { path: /usr/bin/curl }
";
    const OTHER_POLICY_ONLY: &str = "
network_policies:
  other:
    name: other
    endpoints:
      - { host: other.example.com, port: 443 }
    binaries:
      - { path: /usr/bin/curl }
";

    fn authorized_decision(engine: &OpaEngine) -> EgressDecision {
        let input = NetworkInput {
            host: "example.com".to_string(),
            port: 80,
            binary_path: "/usr/bin/curl".into(),
            binary_sha256: String::new(),
            ancestors: vec![],
            cmdline_paths: vec![],
        };
        let authorization = engine.authorize_egress(&input).unwrap();
        assert!(matches!(authorization.action, NetworkAction::Allow { .. }));
        let mut decision = EgressDecision {
            intent: EgressIntent::connect("example.com".to_string(), 80),
            action: authorization.action.clone(),
            policy_generation: authorization.generation,
            identity: ProcessIdentityEvidence::Available,
            endpoint: EndpointDecision::from_authorization(&authorization),
            binary: Some(input.binary_path),
            binary_pid: None,
            ancestors: vec![],
            cmdline_paths: vec![],
        };
        super::super::hydrate_l7_route(&mut decision);
        decision
    }

    async fn read_request_head(server: &mut tokio::io::DuplexStream) -> Option<Vec<u8>> {
        use tokio::io::AsyncReadExt;

        let mut request = Vec::new();
        while !request.ends_with(b"\r\n\r\n") {
            request.push(server.read_u8().await.ok()?);
        }
        Some(request)
    }

    /// Stream a chunked response through an established relay while the
    /// policy reloads to `reloaded`. Returns the bytes the client received
    /// after the reload, and whether a second request on the same
    /// connection was answered.
    async fn stream_across_reload(initial: &str, reloaded: &str) -> (Vec<u8>, bool) {
        use tokio::io::{AsyncReadExt, AsyncWriteExt};

        let engine = Arc::new(OpaEngine::from_strings(POLICY_REGO, initial).unwrap());
        let decision = authorized_decision(&engine);
        let mut request = http_context(
            &decision,
            None,
            None,
            None,
            openshell_core::proposals::AgentProposals::default(),
            RelaySignals {
                activity: None,
                endpoint_observation: None,
            },
        );
        request.request_default_port = Some(80);
        let (mut caller, mut client) = tokio::io::duplex(4096);
        let (mut upstream, mut server) = tokio::io::duplex(4096);
        let context = prepare_http_relay(
            decision.endpoint.l7_route.as_ref(),
            &engine,
            &decision,
            &request,
        )
        .expect("current generation should prepare a relay");
        // Own both sides so a closed relay is visible to its peers as EOF.
        let relay =
            Box::pin(async move { relay_http_stream(&mut client, &mut upstream, context).await });

        let head = b"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n";
        let first = b"5\r\nhello\r\n";
        let rest = b"5\r\nworld\r\n0\r\n\r\n";
        let second = b"HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nok";
        let (reloaded_tx, reloaded_rx) = tokio::sync::oneshot::channel::<()>();
        let serve = async {
            if read_request_head(&mut server).await.is_none() {
                return;
            }
            server.write_all(head).await.unwrap();
            server.write_all(first).await.unwrap();
            server.flush().await.unwrap();
            let _ = reloaded_rx.await;
            let _ = server.write_all(rest).await;
            let _ = server.flush().await;
            if read_request_head(&mut server).await.is_some() {
                let _ = server.write_all(second).await;
                let _ = server.flush().await;
            }
        };
        let receive = async {
            let request = b"GET /stream HTTP/1.1\r\nHost: example.com\r\n\r\n";
            caller.write_all(request).await.unwrap();
            let mut received = vec![0; head.len() + first.len()];
            caller.read_exact(&mut received).await.unwrap();
            engine.reload(POLICY_REGO, reloaded).unwrap();
            // Let the relay observe the new generation before more bytes arrive.
            tokio::time::sleep(std::time::Duration::from_millis(50)).await;
            reloaded_tx.send(()).unwrap();
            let mut after = vec![0; rest.len()];
            let mut read = 0;
            while read < after.len() {
                match caller.read(&mut after[read..]).await {
                    Ok(0) | Err(_) => break,
                    Ok(n) => read += n,
                }
            }
            after.truncate(read);
            let mut response = vec![0; second.len()];
            let answered = read == rest.len()
                && caller.write_all(request).await.is_ok()
                && caller.read_exact(&mut response).await.is_ok()
                && response == second;
            drop(caller);
            (after, answered)
        };
        tokio::time::timeout(
            std::time::Duration::from_secs(5),
            Box::pin(async {
                let (_, (), received) = tokio::join!(relay, serve, receive);
                received
            }),
        )
        .await
        .expect("relay must not hang across a policy reload")
    }

    #[tokio::test]
    async fn passthrough_stream_survives_unrelated_policy_reload() {
        let reloaded = format!("{STREAM_ENDPOINT}{UNRELATED_POLICY}");
        let (after, answered) = Box::pin(stream_across_reload(STREAM_ENDPOINT, &reloaded)).await;
        assert_eq!(after, b"5\r\nworld\r\n0\r\n\r\n");
        assert!(
            answered,
            "keep-alive connection must serve the next request"
        );
    }

    #[tokio::test]
    async fn inspected_stream_survives_unrelated_policy_reload() {
        let reloaded = format!("{STREAM_REST_ENDPOINT}{UNRELATED_POLICY}");
        let (after, answered) =
            Box::pin(stream_across_reload(STREAM_REST_ENDPOINT, &reloaded)).await;
        assert_eq!(after, b"5\r\nworld\r\n0\r\n\r\n");
        assert!(
            answered,
            "keep-alive connection must serve the next request"
        );
    }

    #[tokio::test]
    async fn stream_closes_when_reload_removes_its_endpoint() {
        for initial in [STREAM_ENDPOINT, STREAM_REST_ENDPOINT] {
            let (after, answered) =
                Box::pin(stream_across_reload(initial, OTHER_POLICY_ONLY)).await;
            assert!(
                after.is_empty(),
                "revoked stream must not deliver more bytes"
            );
            assert!(!answered);
        }
    }

    #[test]
    fn relay_guard_follows_reloads_until_admission_changes() {
        let engine = Arc::new(OpaEngine::from_strings(POLICY_REGO, STREAM_ENDPOINT).unwrap());
        let decision = authorized_decision(&engine);
        let guard = prepare_raw_relay(None, &engine, &decision).unwrap();
        let observer = guard.clone();

        let unrelated = format!("{STREAM_ENDPOINT}{UNRELATED_POLICY}");
        engine.reload(POLICY_REGO, &unrelated).unwrap();
        assert!(!guard.is_stale(), "identical admission keeps the relay");
        assert_eq!(observer.captured_generation(), engine.current_generation());

        let other_binary = STREAM_ENDPOINT.replace("/usr/bin/curl", "/usr/bin/wget");
        engine.reload(POLICY_REGO, &other_binary).unwrap();
        assert!(
            guard.is_stale(),
            "a binary that is no longer allowed closes"
        );

        engine.reload(POLICY_REGO, STREAM_ENDPOINT).unwrap();
        assert!(observer.is_stale(), "a revoked relay never becomes current");
    }

    #[test]
    fn relay_guard_closes_on_endpoint_change_and_quarantine() {
        let engine = Arc::new(OpaEngine::from_strings(POLICY_REGO, STREAM_ENDPOINT).unwrap());
        let decision = authorized_decision(&engine);
        let guard = prepare_raw_relay(None, &engine, &decision).unwrap();
        engine.reload(POLICY_REGO, STREAM_REST_ENDPOINT).unwrap();
        assert!(guard.is_stale(), "a changed endpoint configuration closes");

        let engine = Arc::new(OpaEngine::from_strings(POLICY_REGO, STREAM_ENDPOINT).unwrap());
        let decision = authorized_decision(&engine);
        let guard = prepare_raw_relay(None, &engine, &decision).unwrap();
        engine.enter_fail_closed("invalid candidate").unwrap();
        assert!(guard.is_stale(), "fail-closed quarantine closes");
    }

    #[tokio::test]
    async fn raw_relay_closes_immediately_when_fail_closed_generation_is_published() {
        let engine = Arc::new(OpaEngine::from_strings(POLICY_REGO, EMPTY_POLICY_DATA).unwrap());
        let guard = engine
            .generation_guard(engine.current_generation())
            .unwrap();
        let request = request_context();
        let (_client_peer, mut proxy_client) = tokio::io::duplex(64);
        let (_upstream_peer, mut proxy_upstream) = tokio::io::duplex(64);

        let relay = tokio::spawn(async move {
            relay_tcp(&mut proxy_client, &mut proxy_upstream, &guard, &request).await
        });
        tokio::task::yield_now().await;

        engine
            .enter_fail_closed("candidate policy validation failed")
            .unwrap();

        tokio::time::timeout(std::time::Duration::from_secs(1), relay)
            .await
            .expect("raw relay should close when its generation becomes stale")
            .expect("relay task should not panic")
            .expect("stale relay closure should be clean");
    }
}
