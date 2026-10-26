---------------------------- MODULE H2Relay ----------------------------
(***************************************************************************)
(* Per-connection, per-stream model of the HTTP/2 L7 relay in             *)
(* crates/openshell-supervisor-network/src/l7/http2.rs.                   *)
(*                                                                         *)
(* One sandbox client connection is multiplexed onto one upstream         *)
(* connection.  Each direction is one ordered frame queue (a TCP stream). *)
(* The h2 crate demultiplexes client frames into per-stream buffers; one  *)
(* handler per stream (handle_stream) admits, forwards and relays.        *)
(*                                                                         *)
(* Abstractions: a request is (allowed?, header placeholder kind, body    *)
(* kind).  Placeholder rewriting is the function Rewrite; policy is the   *)
(* allowed bit.  A response is a head frame RH plus an end frame RT       *)
(* (DATA + trailers).  Flow control and HPACK are not modelled.           *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Streams,   \* client stream ids, e.g. {1, 2}
          Bug,       \* "none" or a seeded defect, to show properties bite
          HdrKinds,  \* subset of {"none", "ok", "bad"}: no / resolvable / unresolvable placeholder
          BodyKinds  \* subset of {"empty", "clean", "ph"}: no body / body / body with placeholder

Requests  == [allowed : BOOLEAN, hdr : HdrKinds, body : BodyKinds]
UIds      == 1..Cardinality(Streams)
NoId      == 0

Frame(t, id, tag, ph, eos) == [t |-> t, id |-> id, tag |-> tag, ph |-> ph, eos |-> eos]

\* secrets::rewrite_http_header_block: substitutes resolvable placeholders;
\* an unresolvable one would survive (its fail-closed error is what admit checks).
Rewrite(h) == IF h = "bad" THEN "placeholder" ELSE "clean"

VARIABLES
  cl,        \* client per-stream: [sentEnd, recvEnd, reset, opened]
  req,       \* request chosen by the client
  c2p,       \* client -> proxy frames
  inbuf,     \* proxy per-stream receive buffers (h2 server demux)
  px,        \* handler state
  decision,  \* "none" | "allow" | "deny" | "fail"
  pReqDone,  \* handler forwarded the request END_STREAM
  hdrOf,     \* header kind the handler received
  umap,      \* upstream stream id -> client stream id
  uidOf,     \* client stream id -> upstream stream id
  nextUid,
  p2u,       \* proxy -> upstream frames
  up,        \* upstream per-stream: "idle" | "open" | "done" | "reset"
  utag, uReqDone, uHead,
  u2p,       \* upstream -> proxy frames
  p2c,       \* proxy -> client frames
  upAlive,   \* upstream connection usable
  goaway,    \* proxy sent GOAWAY to the client
  upLog,     \* history: frames the upstream received
  cLog       \* history: frames the client received

vars == <<cl, req, c2p, inbuf, px, decision, pReqDone, hdrOf, umap, uidOf, nextUid,
          p2u, up, utag, uReqDone, uHead, u2p, p2c, upAlive, goaway, upLog, cLog>>

Init ==
  /\ cl = [s \in Streams |-> [opened |-> FALSE, sentEnd |-> FALSE, recvEnd |-> FALSE, reset |-> FALSE]]
  /\ req = [s \in Streams |-> [allowed |-> FALSE, hdr |-> "none", body |-> "empty"]]
  /\ c2p = <<>> /\ inbuf = [s \in Streams |-> <<>>]
  /\ px = [s \in Streams |-> "none"] /\ decision = [s \in Streams |-> "none"]
  /\ pReqDone = [s \in Streams |-> FALSE] /\ hdrOf = [s \in Streams |-> "none"]
  /\ umap = [u \in UIds |-> NoId] /\ uidOf = [s \in Streams |-> NoId] /\ nextUid = 1
  /\ p2u = <<>> /\ up = [u \in UIds |-> "idle"] /\ utag = [u \in UIds |-> NoId]
  /\ uReqDone = [u \in UIds |-> FALSE] /\ uHead = [u \in UIds |-> FALSE]
  /\ u2p = <<>> /\ p2c = <<>> /\ upAlive = TRUE /\ goaway = FALSE
  /\ upLog = <<>> /\ cLog = <<>>

Terminal(s) == cl[s].recvEnd \/ cl[s].reset
HandlerDone(s) == px[s] \in {"refused", "reset", "done"}

-----------------------------------------------------------------------------
(* Sandbox client *)

ClientOpen(s) ==
  /\ ~cl[s].opened /\ ~goaway
  /\ \E r \in Requests :
       /\ req' = [req EXCEPT ![s] = r]
       /\ c2p' = Append(c2p, Frame("H", s, s, r.hdr, r.body = "empty"))
       /\ cl' = [cl EXCEPT ![s].opened = TRUE, ![s].sentEnd = (r.body = "empty")]
  /\ UNCHANGED <<inbuf, px, decision, pReqDone, hdrOf, umap, uidOf, nextUid, p2u, up,
                 utag, uReqDone, uHead, u2p, p2c, upAlive, goaway, upLog, cLog>>

ClientData(s) ==
  /\ cl[s].opened /\ ~cl[s].sentEnd /\ ~cl[s].reset
  /\ c2p' = Append(c2p, Frame("D", s, s, IF req[s].body = "ph" THEN "placeholder" ELSE "clean", TRUE))
  /\ cl' = [cl EXCEPT ![s].sentEnd = TRUE]
  /\ UNCHANGED <<req, inbuf, px, decision, pReqDone, hdrOf, umap, uidOf, nextUid, p2u, up,
                 utag, uReqDone, uHead, u2p, p2c, upAlive, goaway, upLog, cLog>>

ClientReset(s) ==
  /\ cl[s].opened /\ ~Terminal(s)
  /\ c2p' = Append(c2p, Frame("R", s, NoId, "clean", TRUE))
  /\ cl' = [cl EXCEPT ![s].reset = TRUE]
  /\ UNCHANGED <<req, inbuf, px, decision, pReqDone, hdrOf, umap, uidOf, nextUid, p2u, up,
                 utag, uReqDone, uHead, u2p, p2c, upAlive, goaway, upLog, cLog>>

ClientRecv ==
  /\ p2c # <<>>
  /\ LET f == Head(p2c) IN
       /\ p2c' = Tail(p2c)
       /\ cLog' = Append(cLog, f)
       /\ cl' = IF cl[f.id].reset THEN cl
                ELSE CASE f.t \in {"RESP", "RT"} -> [cl EXCEPT ![f.id].recvEnd = TRUE]
                       [] f.t = "R"             -> [cl EXCEPT ![f.id].reset = TRUE]
                       [] OTHER                 -> cl
  /\ UNCHANGED <<req, c2p, inbuf, px, decision, pReqDone, hdrOf, umap, uidOf, nextUid, p2u,
                 up, utag, uReqDone, uHead, u2p, upAlive, goaway, upLog>>

-----------------------------------------------------------------------------
(* Proxy: connection task.  relay_h2 accept loop, http2.rs:140-165 *)

ProxyDemux ==
  /\ c2p # <<>>
  /\ LET f == Head(c2p) IN
       inbuf' = [inbuf EXCEPT ![f.id] = Append(@, f)]
  /\ c2p' = Tail(c2p)
  /\ UNCHANGED <<cl, req, px, decision, pReqDone, hdrOf, umap, uidOf, nextUid, p2u, up,
                 utag, uReqDone, uHead, u2p, p2c, upAlive, goaway, upLog, cLog>>

\* server.accept() yields (request, respond); streams.push(handle_stream) http2.rs:144-146
Accept(s) ==
  /\ px[s] = "none" /\ inbuf[s] # <<>> /\ Head(inbuf[s]).t = "H"
  /\ hdrOf' = [hdrOf EXCEPT ![s] = Head(inbuf[s]).ph]
  /\ pReqDone' = [pReqDone EXCEPT ![s] = Head(inbuf[s]).eos]
  /\ inbuf' = [inbuf EXCEPT ![s] = Tail(@)]
  /\ px' = [px EXCEPT ![s] = IF Bug = "forward_before_admit" THEN "ready" ELSE "admitting"]
  /\ UNCHANGED <<cl, req, c2p, decision, umap, uidOf, nextUid, p2u, up, utag, uReqDone,
                 uHead, u2p, p2c, upAlive, goaway, upLog, cLog>>

\* admit(): a non-origin-form :path -> 400 http2.rs:275-286 (a refusal like
\* deny: allowed = FALSE), evaluate_l7_request http2.rs:336, deny -> 403 http2.rs:352,
\* rewrite_http_header_block failure -> credential_refusal http2.rs:394-399,
\* refusal.send http2.rs:217.  Only this stream's respond handle is touched.
Admit(s) ==
  /\ px[s] = "admitting"
  /\ \/ /\ ~req[s].allowed
        /\ decision' = [decision EXCEPT ![s] = "deny"]
        /\ px' = [px EXCEPT ![s] = "refused"]
        /\ p2c' = Append(p2c, Frame("RESP", s, s, "clean", TRUE))
     \/ /\ req[s].allowed /\ hdrOf[s] = "bad" /\ Bug # "skip_fail_closed"
        /\ decision' = [decision EXCEPT ![s] = "fail"]
        /\ px' = [px EXCEPT ![s] = "refused"]
        /\ p2c' = Append(p2c, Frame("RESP", s, s, "clean", TRUE))
     \/ /\ req[s].allowed /\ (hdrOf[s] # "bad" \/ Bug = "skip_fail_closed")
        /\ decision' = [decision EXCEPT ![s] = "allow"]
        /\ px' = [px EXCEPT ![s] = "ready"]
        /\ UNCHANGED p2c
  /\ UNCHANGED <<cl, req, c2p, inbuf, pReqDone, hdrOf, umap, uidOf, nextUid, p2u, up, utag,
                 uReqDone, uHead, u2p, upAlive, goaway, upLog, cLog>>

\* sender.ready() / send_request http2.rs:229-251; no upstream -> 502.
Forward(s) ==
  /\ px[s] = "ready"
  /\ IF ~upAlive
       THEN /\ px' = [px EXCEPT ![s] = "refused"]
            /\ p2c' = Append(p2c, Frame("RESP", s, s, "clean", TRUE))
            /\ UNCHANGED <<umap, uidOf, nextUid, p2u>>
       ELSE /\ px' = [px EXCEPT ![s] = "fwd"]
            /\ umap' = [umap EXCEPT ![nextUid] = s]
            /\ uidOf' = [uidOf EXCEPT ![s] = nextUid]
            /\ nextUid' = nextUid + 1
            /\ p2u' = Append(p2u, Frame("H", nextUid, s, Rewrite(hdrOf[s]), pReqDone[s]))
            /\ UNCHANGED p2c
  /\ UNCHANGED <<cl, req, c2p, inbuf, decision, pReqDone, hdrOf, up, utag, uReqDone, uHead,
                 u2p, upAlive, goaway, upLog, cLog>>

\* pump(body, upstream_send, true) http2.rs:542-609: DATA forwarded unless it
\* carries a marker (carries_marker http2.rs:565 -> send_reset); a client RST
\* surfaces as a recv error and is propagated upstream (http2.rs:557-561), or
\* via respond.poll_reset in relay_response (http2.rs:521).
PumpReq(s) ==
  /\ px[s] = "fwd" /\ inbuf[s] # <<>>
  /\ LET f == Head(inbuf[s]) IN
       \/ /\ f.t = "D" /\ (f.ph = "clean" \/ Bug = "no_body_scan")
          /\ p2u' = Append(p2u, Frame("D", uidOf[s], s, f.ph, f.eos))
          /\ pReqDone' = [pReqDone EXCEPT ![s] = f.eos]
          /\ UNCHANGED <<px, p2c>>
       \/ /\ f.t = "D" /\ f.ph = "placeholder" /\ Bug # "no_body_scan"
          /\ p2u' = Append(p2u, Frame("R", uidOf[s], NoId, "clean", TRUE))
          /\ p2c' = Append(p2c, Frame("R", s, NoId, "clean", TRUE))
          /\ px' = [px EXCEPT ![s] = "reset"]
          /\ UNCHANGED pReqDone
       \/ /\ f.t = "R"
          /\ p2u' = Append(p2u, Frame("R", uidOf[s], NoId, "clean", TRUE))
          /\ px' = [px EXCEPT ![s] = "reset"]
          /\ UNCHANGED <<pReqDone, p2c>>
  /\ inbuf' = [inbuf EXCEPT ![s] = Tail(@)]
  /\ UNCHANGED <<cl, req, c2p, decision, hdrOf, umap, uidOf, nextUid, up, utag, uReqDone,
                 uHead, u2p, upAlive, goaway, upLog, cLog>>

\* Frames for a finished stream are discarded by the h2 crate.
Drop(s) ==
  /\ HandlerDone(s) /\ inbuf[s] # <<>>
  /\ inbuf' = [inbuf EXCEPT ![s] = Tail(@)]
  /\ UNCHANGED <<cl, req, c2p, px, decision, pReqDone, hdrOf, umap, uidOf, nextUid, p2u, up,
                 utag, uReqDone, uHead, u2p, p2c, upAlive, goaway, upLog, cLog>>

\* relay_response / pump(.., false) http2.rs:517-539: frames from upstream
\* stream u go to the client stream whose handler owns u.
ProxyRecvUp ==
  /\ u2p # <<>>
  /\ LET f == Head(u2p)
         s == IF Bug = "swap_map" /\ Cardinality(Streams) > 1
                THEN CHOOSE t \in Streams : t # umap[f.id]
                ELSE umap[f.id] IN
       IF px[s] = "fwd"
         THEN /\ p2c' = Append(p2c, Frame(f.t, s, f.tag, "clean", f.t # "RH"))
              /\ px' = [px EXCEPT ![s] = CASE f.t = "RT" -> "done"
                                          [] f.t = "R"  -> "reset"
                                          [] OTHER      -> "fwd"]
         ELSE UNCHANGED <<p2c, px>>
  /\ u2p' = Tail(u2p)
  /\ UNCHANGED <<cl, req, c2p, inbuf, decision, pReqDone, hdrOf, umap, uidOf, nextUid, p2u,
                 up, utag, uReqDone, uHead, upAlive, goaway, upLog, cLog>>

\* Upstream connection ended (GOAWAY or close): upstream_conn branch
\* http2.rs:155-163 -> graceful_shutdown; in-flight streams error -> RST.
UpLost(s) ==
  /\ px[s] = "fwd" /\ ~upAlive
  /\ px' = [px EXCEPT ![s] = "reset"]
  /\ p2c' = Append(p2c, Frame("R", s, NoId, "clean", TRUE))
  /\ UNCHANGED <<cl, req, c2p, inbuf, decision, pReqDone, hdrOf, umap, uidOf, nextUid, p2u,
                 up, utag, uReqDone, uHead, u2p, upAlive, goaway, upLog, cLog>>

-----------------------------------------------------------------------------
(* Upstream server *)

UpRecv ==
  /\ p2u # <<>> /\ upAlive
  /\ LET f == Head(p2u) IN
       /\ upLog' = Append(upLog, f)
       /\ CASE f.t = "H" ->
                 /\ up' = [up EXCEPT ![f.id] = "open"]
                 /\ utag' = [utag EXCEPT ![f.id] = f.tag]
                 /\ uReqDone' = [uReqDone EXCEPT ![f.id] = f.eos]
            [] f.t = "D" ->
                 /\ uReqDone' = [uReqDone EXCEPT ![f.id] = f.eos]
                 /\ UNCHANGED <<up, utag>>
            [] OTHER ->
                 /\ up' = [up EXCEPT ![f.id] = IF @ = "open" THEN "reset" ELSE @]
                 /\ UNCHANGED <<utag, uReqDone>>
  /\ p2u' = Tail(p2u)
  /\ UNCHANGED <<cl, req, c2p, inbuf, px, decision, pReqDone, hdrOf, umap, uidOf, nextUid,
                 uHead, u2p, p2c, upAlive, goaway, cLog>>

UpHead(u) ==
  /\ upAlive /\ up[u] = "open" /\ ~uHead[u]
  /\ uHead' = [uHead EXCEPT ![u] = TRUE]
  /\ u2p' = Append(u2p, Frame("RH", u, utag[u], "clean", FALSE))
  /\ UNCHANGED <<cl, req, c2p, inbuf, px, decision, pReqDone, hdrOf, umap, uidOf, nextUid,
                 p2u, up, utag, uReqDone, p2c, upAlive, goaway, upLog, cLog>>

UpEnd(u) ==
  /\ upAlive /\ up[u] = "open" /\ uHead[u] /\ uReqDone[u]
  /\ up' = [up EXCEPT ![u] = "done"]
  /\ u2p' = Append(u2p, Frame("RT", u, utag[u], "clean", TRUE))
  /\ UNCHANGED <<cl, req, c2p, inbuf, px, decision, pReqDone, hdrOf, umap, uidOf, nextUid,
                 p2u, utag, uReqDone, uHead, p2c, upAlive, goaway, upLog, cLog>>

UpReset(u) ==
  /\ upAlive /\ up[u] = "open"
  /\ up' = [up EXCEPT ![u] = "reset"]
  /\ u2p' = Append(u2p, Frame("R", u, NoId, "clean", TRUE))
  /\ UNCHANGED <<cl, req, c2p, inbuf, px, decision, pReqDone, hdrOf, umap, uidOf, nextUid,
                 p2u, utag, uReqDone, uHead, p2c, upAlive, goaway, upLog, cLog>>

UpClose ==
  /\ upAlive
  /\ upAlive' = FALSE /\ goaway' = TRUE
  /\ p2u' = <<>> /\ u2p' = <<>>
  /\ UNCHANGED <<cl, req, c2p, inbuf, px, decision, pReqDone, hdrOf, umap, uidOf, nextUid,
                 up, utag, uReqDone, uHead, p2c, upLog, cLog>>

-----------------------------------------------------------------------------

Next ==
  \/ \E s \in Streams : ClientOpen(s) \/ ClientData(s) \/ ClientReset(s)
  \/ ClientRecv \/ ProxyDemux \/ ProxyRecvUp \/ UpRecv \/ UpClose
  \/ \E s \in Streams : Accept(s) \/ Admit(s) \/ Forward(s) \/ PumpReq(s) \/ Drop(s) \/ UpLost(s)
  \/ \E u \in UIds : UpHead(u) \/ UpEnd(u) \/ UpReset(u)

\* Fairness only for the relay, the upstream finishing a request it has, and
\* the client finishing its body; resets, GOAWAY and new streams are optional.
Fairness ==
  /\ WF_vars(ClientRecv) /\ WF_vars(ProxyDemux) /\ WF_vars(ProxyRecvUp) /\ WF_vars(UpRecv)
  /\ \A s \in Streams : WF_vars(ClientData(s)) /\ WF_vars(Accept(s)) /\ WF_vars(Admit(s))
                        /\ WF_vars(Forward(s)) /\ WF_vars(PumpReq(s)) /\ WF_vars(Drop(s))
                        /\ WF_vars(UpLost(s))
  /\ \A u \in UIds : WF_vars(UpHead(u)) /\ WF_vars(UpEnd(u))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties *)

TypeOK ==
  /\ HdrKinds \subseteq {"none", "ok", "bad"} /\ BodyKinds \subseteq {"empty", "clean", "ph"}
  /\ px \in [Streams -> {"none", "admitting", "ready", "fwd", "refused", "reset", "done"}]
  /\ decision \in [Streams -> {"none", "allow", "deny", "fail"}]
  /\ nextUid \in 1..(Cardinality(Streams) + 1)

ToUpstream == {upLog[i] : i \in DOMAIN upLog} \cup {p2u[i] : i \in DOMAIN p2u}

\* P1: nothing of a stream is sent upstream before (or without) an allow decision.
OnlyAllowedReachUpstream ==
  \A f \in ToUpstream : f.t \in {"H", "D"} => decision[f.tag] = "allow"

\* P2a: a denied or failed stream sends nothing upstream.
RefusedSendsNothing ==
  \A s \in Streams : decision[s] \in {"deny", "fail"} =>
     /\ \A f \in ToUpstream : f.t \in {"H", "D"} => f.tag # s
     /\ uidOf[s] = NoId

\* P2b: refusing a stream changes no other stream and keeps the connection.
RefusalIsLocal ==
  [][\A s \in Streams :
       (decision[s] = "none" /\ decision'[s] \in {"deny", "fail"}) =>
         /\ \A t \in Streams \ {s} : px'[t] = px[t] /\ inbuf'[t] = inbuf[t]
         /\ upAlive' = upAlive /\ goaway' = goaway /\ p2u' = p2u]_vars

\* P3: every header block and DATA frame reaching upstream is placeholder-free;
\* an unresolvable header placeholder fails the stream closed.
NoPlaceholderUpstream ==
  /\ \A f \in ToUpstream : f.t \in {"H", "D"} => f.ph = "clean"
  /\ \A s \in Streams : (px[s] # "none" /\ hdrOf[s] = "bad" /\ req[s].allowed
                         /\ px[s] \notin {"admitting", "ready"}) => decision[s] = "fail"

\* P4: response frames are delivered on the stream whose request produced them.
NoCrossStream ==
  \A i \in DOMAIN cLog : cLog[i].t \in {"RH", "RT"} => cLog[i].tag = cLog[i].id

\* P5: under fairness, every opened stream completes, is refused, or is reset,
\* and every stream handler terminates.
StreamsComplete == \A s \in Streams : cl[s].opened ~> Terminal(s)
HandlersFinish == \A s \in Streams : (px[s] # "none") ~> HandlerDone(s)
=============================================================================
