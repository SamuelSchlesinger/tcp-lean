## Context

We are formalizing RFC 793 in Lean 4 as a publication-quality research
artifact. The formalization spans seven interconnected modules and must
faithfully capture the protocol's two-endpoint interaction model, full event
processing logic, and key correctness theorems. This design document records
the major modeling decisions that cut across modules.

## Goals / Non-Goals

### Goals
- Full-fidelity model of RFC 793 Section 3.9 event processing (all user calls,
  segment arrival 8-check pipeline, all timeout types, all state transitions)
- Two-endpoint system model with explicit network (in-flight segments)
- Machine-checked proofs of handshake correctness, teardown correctness,
  and safety invariants over the system model
- Sliding window invariants and data delivery ordering
- RFC section citations in every doc comment and theorem name

### Non-Goals
- Executable TCP implementation (this is a logical model, not runnable code)
- Later TCP extensions (congestion control, timestamps, window scaling)
- Security/compartment/precedence (IP-layer; modeled as always-matching)
- ISN generation clock or RTO calculation (abstracted)
- Performance or computability of the model

## Decisions

### D1: Sequence Number Representation

**Decision**: Use `Fin (2^32)` (or equivalently a structure wrapping a `UInt32`
value with a proof of bounds) rather than `UInt32` directly.

**Rationale**: `Fin n` gives us modular arithmetic via `Fin.add` and `Fin.sub`
with built-in well-formedness, and integrates cleanly with Lean's `omega` and
`decide` tactics. `UInt32` lacks direct proof-level support for modular
reasoning.

**Alternative considered**: Opaque type with axioms. Rejected because axioms
risk unsoundness and `Fin` provides everything we need.

### D2: Circular Less-Than Relation

**Decision**: Define `SeqNum.lt a b` as `(b.val - a.val) % 2^32 ∈ (0, 2^31)`,
i.e., `b` is strictly ahead of `a` within the forward half of the circular
space (RFC 793 §3.3).

**Rationale**: This is the standard interpretation used by all TCP
implementations. The RFC's notation `=<` ("less than or equal modulo 2^32")
relies on this half-space convention without stating it explicitly. The half-
space window of 2^31 ensures that the relation is a strict partial order on
any set of sequence numbers that fits within a half-space.

### D3: Two-Endpoint System Model

**Decision**: Define a `System` structure containing:
- `endpointA : TcpEndpoint` — one TCP's full state (TcpState, TCB, queues)
- `endpointB : TcpEndpoint` — the other TCP's full state
- `network : List Segment` — in-flight segments (treated as a multiset)

The system evolves via a `SystemStep` inductive that represents one atomic
action: delivering a segment from the network to an endpoint, a user call on
either endpoint, a timeout event on either endpoint, segment loss, or segment
duplication.

**Rationale**: Modeling the network explicitly as a bag of segments lets us
capture reordering (any segment can be delivered next), duplication (a segment
can be copied), and loss (a segment can be removed). This is the standard
approach in protocol verification (cf. the TLA+ TCP spec). Proving properties
over `SystemStep` traces gives us guarantees about all possible network
behaviors.

**Alternative considered**: Single-endpoint model. Rejected because the user
explicitly requires two-endpoint reasoning, and key theorems (handshake,
simultaneous close) inherently involve both sides.

### D4: Event Processing as a Pure Function

**Decision**: Model each endpoint's event processing as a pure function:
```
processSegment : TcpEndpoint → Segment → TcpEndpoint × List Segment
processUserCall : TcpEndpoint → UserCall → TcpEndpoint × List Segment × UserResponse
processTimeout : TcpEndpoint → TimeoutKind → TcpEndpoint × List Segment
```

The `List Segment` output represents segments to be placed on the network.
`UserResponse` captures signals back to the user (error messages, ok, data).

**Rationale**: Pure functions are easiest to reason about in Lean. The
nondeterminism (which segment is delivered, whether loss/duplication occurs)
lives in the `SystemStep` inductive, not inside the endpoint processing.

### D5: Segment Length Includes SYN and FIN

**Decision**: `Segment.len` (corresponding to `SEG.LEN` in the RFC) counts data
octets plus 1 for SYN (if set) plus 1 for FIN (if set), per RFC 793 §3.3:
"The segment length (SEG.LEN) includes both data and sequence space occupying
controls."

**Rationale**: This is not a design choice but a faithful transcription of the
RFC. It affects acceptability tests and acknowledgment processing. Getting this
wrong would invalidate handshake and teardown proofs.

### D6: Retransmission Queue Abstraction

**Decision**: Model the retransmission queue as a `List Segment` of
unacknowledged sent segments. On ACK receipt, remove segments whose
`seq + len ≤ ack` (modular). On retransmission timeout, the head of the queue
is re-emitted.

**Rationale**: The RFC specifies this behavior but leaves queue management to
the implementation. A `List Segment` ordered by sequence number is the simplest
faithful model. We do not model timer values; retransmission is triggered by an
abstract `TimeoutKind.Retransmission` event.

### D7: Send/Receive Buffers as Byte Lists

**Decision**: Model send and receive buffers as `List UInt8`. The send buffer
holds data submitted by the user via SEND but not yet transmitted. The receive
buffer holds in-order data accepted but not yet delivered to the user via
RECEIVE.

**Rationale**: `List UInt8` is simple and sufficient for proving ordering and
completeness properties. We do not model buffer capacity limits; "insufficient
resources" errors are outside the scope of protocol correctness.

### D8: Scope of Window Management

**Decision**: Formalize the window update condition from RFC 793 §3.9 (fifth
check, ESTABLISHED):
```
if SND.WL1 < SEG.SEQ ∨ (SND.WL1 = SEG.SEQ ∧ SND.WL2 ≤ SEG.ACK) then
  SND.WND ← SEG.WND; SND.WL1 ← SEG.SEQ; SND.WL2 ← SEG.ACK
```
Also formalize the invariant that `RCV.NXT + RCV.WND` does not decrease
(RFC 793 §3.7: "The total of RCV.NXT and RCV.WND should not be reduced").

**Rationale**: Window management is central to TCP flow control and the user
specifically requested sliding window invariants. The window update condition
prevents old segments from corrupting the window state.

### D9: Omission of Security/Precedence

**Decision**: Omit security/compartment and precedence checks from the event
processing model. The third check in the SEGMENT ARRIVES pipeline ("check
security and precedence") is treated as always passing.

**Rationale**: These are IP-layer security features (RFC 793 §3.6) orthogonal
to TCP protocol correctness. Including them would add complexity without
contributing to the core theorems. If needed later, they can be added as a
separate change.

### D10: Urgent Data

**Decision**: Model the urgent pointer (`SND.UP`, `RCV.UP`) and URG flag
faithfully in the types and event processing (RFC 793 §3.9 sixth check), but
do not prove separate urgent-specific theorems. Urgent data is a signaling
mechanism that does not affect state transitions or data ordering.

**Rationale**: Completeness of the event processing model requires handling
URG, but the interesting correctness properties (handshake, teardown,
invariants) are independent of urgent data.

## Risks / Trade-offs

- **Proof complexity**: Some invariants (especially data delivery ordering)
  require induction over system traces, which can be verbose. Mitigation: break
  proofs into small lemmas per state transition.
- **Model fidelity vs tractability**: The full Section 3.9 processing is
  detailed (8 checks, 11 states, 6 user calls). Mitigation: the pure-function
  decomposition (D4) keeps each case manageable.
- **Sequence number reasoning**: Modular arithmetic proofs can be tedious.
  Mitigation: build a strong lemma library in `SeqNum.lean` and rely on
  `omega`/`decide` where possible.
- **Lean version sensitivity**: The formalization targets Lean 4.28.0 without
  Mathlib. If advanced lemmas are needed, Mathlib can be added, but this
  increases build times.

## Resolved Questions

- **Out-of-order reassembly**: DECIDED — model explicitly with a reassembly
  buffer (`reassemblyBuf : List Segment` on `TcpEndpoint`). RFC 793 §3.9 first
  check says "Segments with higher beginning sequence numbers may be held for
  later processing." This is critical for proving in-order data delivery.
- **Open mode tracking**: DECIDED — `TcpEndpoint` includes
  `openMode : Option OpenMode`. Required for RST handling in SYN-RECEIVED
  (RFC 793 §3.9 second check: passive origin returns to LISTEN, active origin
  aborts to CLOSED).
