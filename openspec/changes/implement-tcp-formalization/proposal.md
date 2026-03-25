# Change: Implement the full TCP (RFC 793) formalization

## Why
The project scaffolding is complete but every Lean module is an empty namespace.
To produce a publication-quality formal verification we must now populate the
modules with definitions, predicates, a two-endpoint system model, and
machine-checked proofs of the core correctness properties described in RFC 793.

## What Changes
- **SeqNum** (`Tcp/SeqNum.lean`): Define the `SeqNum` type (modular 2^32
  arithmetic), addition/subtraction, the circular less-than relation, and prove
  key properties (irreflexivity, transitivity within the half-space, decidability).
  RFC 793 &sect;3.3.

- **Types** (`Tcp/Types.lean`): Define `Port`, `SocketAddr`, `ControlBits`,
  `Segment` (all header fields per RFC 793 &sect;3.1), and the Transmission
  Control Block (`Tcb`) with all send/receive variables per RFC 793 &sect;3.2.
  Model `SEG.LEN` to include SYN and FIN contributions to sequence space
  (RFC 793 &sect;3.3).

- **State** (`Tcp/State.lean`): Define the `TcpState` enum (11 states + Closed),
  user call types (OPEN, SEND, RECEIVE, CLOSE, ABORT, STATUS per RFC 793 &sect;3.8),
  timeout types, and the `TcpEndpoint` structure bundling state, TCB, send
  queue, receive buffer, and retransmission queue. Define the two-endpoint
  `System` model with a network (multiset of in-flight segments) and the
  full event-processing step function implementing RFC 793 &sect;3.9 in its
  entirety (SEGMENT ARRIVES 8-check pipeline, all user calls per-state, all
  three timeout types).

- **Acceptability** (`Tcp/Acceptability.lean`): Define the segment acceptability
  predicate (4-case table from RFC 793 &sect;3.3) and ACK acceptability
  (`SND.UNA < SEG.ACK =< SND.NXT`). Prove key lemmas about these predicates
  over modular sequence number space.

- **Handshake** (`Tcp/Handshake.lean`): Prove that the three-way handshake
  (normal active/passive open, simultaneous open) correctly transitions both
  endpoints to ESTABLISHED with synchronized sequence numbers.
  Model old-duplicate-SYN recovery and half-open connection detection via RST.
  RFC 793 &sect;3.4, Figures 7--12.

- **Teardown** (`Tcp/Teardown.lean`): Prove correctness of connection closing:
  normal close (FIN-WAIT-1 &rarr; FIN-WAIT-2 &rarr; TIME-WAIT &rarr; CLOSED),
  simultaneous close (FIN-WAIT-1 &rarr; CLOSING &rarr; TIME-WAIT &rarr; CLOSED),
  and the TIME-WAIT 2&times;MSL requirement. RFC 793 &sect;3.5, Figures 13--14.

- **Invariants** (`Tcp/Invariants.lean`): State and prove safety invariants
  over the two-endpoint system: sequence number monotonicity
  (`SND.UNA =< SND.NXT`), send window bounds, receive window validity,
  in-order data delivery, and the property that no data is delivered to the
  user before the connection reaches ESTABLISHED. Prove sliding window
  invariants including that `RCV.NXT + RCV.WND` does not decrease.

- **Whitepaper** (`whitepaper.tex`): Populate all section stubs with prose
  describing the formalization, design decisions, key definitions, and
  statement/explanation of each proved theorem.

## Impact
- Affected specs: `seq-num-arithmetic`, `tcp-types`, `tcp-state-machine`,
  `segment-acceptability`, `connection-establishment`, `connection-teardown`,
  `safety-invariants`, `whitepaper` (all new)
- Affected code: All files under `Tcp/`, `whitepaper.tex`

## Scope Exclusions
The following RFC 793 features are **out of scope** for this change, with
justification:

- **Security/compartment/precedence** (RFC 793 &sect;3.6): IP-layer security
  features orthogonal to core TCP correctness. Modeled as always-matching.
- **Checksum computation**: Implementation concern, not protocol logic.
- **MSS option negotiation**: Performance optimization, not correctness.
- **ISN clock-based generation** (RFC 793 &sect;3.3): ISN treated as an
  abstract parameter. Quiet-time concept noted but not formalized.
- **RTO calculation** (RFC 793 &sect;3.7): Retransmission modeled as abstract
  timeout events; specific SRTT/RTO algorithm is an implementation choice.
- **IP-layer interactions**: Addressing, fragmentation, and routing abstracted
  away.
