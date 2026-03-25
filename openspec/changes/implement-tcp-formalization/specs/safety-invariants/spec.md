## ADDED Requirements

### Requirement: Sequence Number Monotonicity
The library SHALL prove that for every reachable system state (obtained by any
sequence of `SystemStep` transitions from a valid initial state), each
endpoint's TCB satisfies `SND.UNA ≤ SND.NXT` (using `SeqNum.le`, modular).

This invariant reflects that the oldest unacknowledged sequence number never
exceeds the next sequence number to be sent (RFC 793 §3.7).

#### Scenario: Invariant preserved by ACK processing
- **WHEN** an acceptable ACK advances `SND.UNA`
- **THEN** `SND.UNA ≤ SND.NXT` still holds

#### Scenario: Invariant preserved by SEND
- **WHEN** new data is sent (advancing `SND.NXT`)
- **THEN** `SND.UNA ≤ SND.NXT` still holds

### Requirement: Send Window Bound
The library SHALL prove that data is only transmitted with sequence numbers in
the range `[SND.UNA, SND.UNA + SND.WND)`. No segment is placed on the network
with a sequence number outside the send window (RFC 793 §3.7).

Additionally, the library SHALL prove that `SND.NXT ≤ SND.UNA + SND.WND` is
an invariant: the next sequence number to send never exceeds the right edge of
the send window. Combined with sequence number monotonicity, this gives the
full chain: `SND.UNA ≤ SND.NXT ≤ SND.UNA + SND.WND`.

#### Scenario: Segment within send window
- **WHEN** a data segment is emitted by `processEvent`
- **THEN** its sequence number satisfies `SND.UNA ≤ SEG.SEQ < SND.UNA + SND.WND`

#### Scenario: SND.NXT bounded by window
- **WHEN** any system step advances `SND.NXT`
- **THEN** `SND.NXT ≤ SND.UNA + SND.WND` still holds

### Requirement: Receive Window Monotonicity
The library SHALL prove that `RCV.NXT + RCV.WND` (the right edge of the receive
window) does not decrease across any `SystemStep` on a well-behaved endpoint.

Note: RFC 793 §3.7 states "The total of RCV.NXT and RCV.WND should not be
reduced" — this is a normative requirement on the implementation, not a
guarantee about remote peers. Our model enforces this as an invariant of each
endpoint's own processing. A remote peer advertising a shrunk window is handled
by the robustness principle (RFC 793 §2.10: "be prepared for such behavior on
the part of other TCPs").

#### Scenario: Window right edge preserved
- **WHEN** data is accepted (advancing `RCV.NXT`) and `RCV.WND` is adjusted
- **THEN** the sum `RCV.NXT + RCV.WND` is greater than or equal to its previous value

### Requirement: RCV.NXT Monotonicity
The library SHALL prove that `RCV.NXT` only advances (never retreats) across
`SystemStep` transitions. Data acceptance always advances `RCV.NXT` forward
(RFC 793 §3.9 seventh check: "advances RCV.NXT over the data accepted").

#### Scenario: RCV.NXT never goes backward
- **WHEN** any system step modifies `RCV.NXT`
- **THEN** the new value is ≥ the old value (modular)

### Requirement: ACK Monotonicity
The library SHALL prove that `SND.UNA` only advances (never retreats) across
`SystemStep` transitions. Formally: if `SND.UNA` changes from value `u` to
value `u'`, then `u ≤ u'` (modular).

#### Scenario: SND.UNA never goes backward
- **WHEN** any system step modifies `SND.UNA`
- **THEN** the new value is ≥ the old value (modular)

### Requirement: No Data Before ESTABLISHED
The library SHALL prove that no data bytes are delivered to the user's receive
buffer (via the `recvBuffer` field or `processReceive` output) before the
endpoint reaches ESTABLISHED state. Data piggybacked on SYN segments or
received during SYN-RECEIVED is queued in the reassembly buffer but not
delivered until the connection is fully synchronized (RFC 793 §3.4: "the
receiving TCP doesn't deliver the data to the user until it is clear the data
is valid").

#### Scenario: Data buffered in SYN-RECEIVED
- **WHEN** a data-bearing SYN arrives at a LISTEN endpoint
- **THEN** data is queued but not delivered to the user until ESTABLISHED

#### Scenario: Data piggybacked on SYN
- **WHEN** a SYN segment carries payload data (RFC 793 §3.4 allows this)
- **THEN** the data is buffered and only delivered after the handshake completes

### Requirement: In-Order Data Delivery
The library SHALL prove that data bytes delivered to the user via RECEIVE calls
appear in the same order as their sequence numbers in the sender's SEND calls.
If sender transmits byte `b1` at sequence number `s1` and byte `b2` at `s2`
with `s1 < s2`, and both are delivered to the receiver, then `b1` is delivered
to the user before `b2`.

The proof SHALL account for out-of-order segment arrival: segments held in the
reassembly buffer are reordered by sequence number before delivery
(RFC 793 §3.9 first check: "further processing is done in SEG.SEQ order").

#### Scenario: Out-of-order segments delivered in order
- **WHEN** segments arrive out of order but are reassembled
- **THEN** the data delivered to the user is in sequence number order

### Requirement: Window Update Correctness
The library SHALL prove that `SND.WND` is only updated when the window update
condition from RFC 793 §3.9 holds:
```
SND.WL1 < SEG.SEQ ∨ (SND.WL1 = SEG.SEQ ∧ SND.WL2 ≤ SEG.ACK)
```
This prevents old segments from corrupting the window state. The window update
applies in ESTABLISHED and also in FIN-WAIT-1, FIN-WAIT-2, and CLOSE-WAIT
(which do "the same processing as for the ESTABLISHED state" per RFC 793 §3.9).

#### Scenario: Old segment does not update window
- **WHEN** a segment arrives with `SEG.SEQ < SND.WL1`
- **THEN** `SND.WND` is not modified

#### Scenario: Window update in non-ESTABLISHED states
- **WHEN** an ACK arrives in FIN-WAIT-1 with a valid window update condition
- **THEN** `SND.WND` is updated (same logic as ESTABLISHED)

### Requirement: RST Validation
The library SHALL prove that RST segments are validated correctly according to
RFC 793 §3.4 with state-dependent rules:
- In SYN-SENT: RST is acceptable if and only if the ACK field acknowledges the
  SYN (i.e., `SEG.ACK` acknowledges ISS)
- In all other states: RST is valid if and only if its sequence number is in
  the receive window (`RCV.NXT ≤ SEG.SEQ < RCV.NXT + RCV.WND`)

#### Scenario: RST in SYN-SENT validated by ACK
- **WHEN** a RST arrives in SYN-SENT with `SEG.ACK = ISS + 1`
- **THEN** the RST is valid (connection aborted)

#### Scenario: RST in ESTABLISHED validated by sequence number
- **WHEN** a RST arrives in ESTABLISHED with `SEG.SEQ` in the receive window
- **THEN** the RST is valid (connection aborted)
