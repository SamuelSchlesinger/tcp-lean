## 1. Sequence Number Arithmetic (`Tcp/SeqNum.lean`) — RFC 793 §3.3
- [x] 1.1 Define `SeqNum` type (wrapper over `UInt32`) with `DecidableEq` and `Repr`
- [x] 1.2 Define `SeqNum.add : SeqNum → UInt32 → SeqNum` (advance by offset, modular)
- [x] 1.3 Define `SeqNum.diff : SeqNum → SeqNum → UInt32` (distance, modular)
- [x] 1.4 Define `SeqNum.lt` (circular less-than: `b - a` in `(0, 2^31)`) and `SeqNum.le`
- [x] 1.5 Prove `SeqNum.lt` is irreflexive
- [ ] 1.6 Prove `SeqNum.lt` is transitive within the half-space
- [ ] 1.7 Prove `SeqNum.lt` is trichotomous within the half-space (exactly one of `a < b`, `a = b`, `b < a`)
- [x] 1.8 Prove `SeqNum.lt` is decidable; provide `Decidable` instance
- [x] 1.9 Prove interaction lemmas: `add_zero`, `diff_self`, `le_refl`, `le_of_lt`
- [x] 1.10 Verify `lake build Tcp.SeqNum` succeeds with no `sorry`

## 2. Core Types (`Tcp/Types.lean`) — RFC 793 §3.1, §3.2
- [x] 2.1 Define `Port` (abbrev for `UInt16`)
- [x] 2.2 Define `SocketAddr` structure (address abstracted as `Nat`, port)
- [x] 2.3 Define `ControlBits` structure (`urg ack psh rst syn fin : Bool`)
- [x] 2.4 Define `Segment` structure (srcPort, dstPort, seq : SeqNum, ack : SeqNum, ctl : ControlBits, window : UInt16, urgPtr : UInt16, data : List UInt8) — cite RFC 793 §3.1 header fields
- [x] 2.5 Define `Segment.len : Segment → UInt32` computing SEG.LEN (data.length + SYN + FIN per RFC 793 §3.3)
- [x] 2.6 Define `Tcb` structure with all send variables (sndUna, sndNxt, sndWnd, sndUp, sndWl1, sndWl2, iss : SeqNum) and receive variables (rcvNxt, rcvWnd, rcvUp, irs : SeqNum) — cite RFC 793 §3.2
- [x] 2.7 Define `TcpState` inductive (Closed, Listen, SynSent, SynReceived, Established, FinWait1, FinWait2, CloseWait, Closing, LastAck, TimeWait) — cite RFC 793 §3.2
- [x] 2.8 Define `OpenMode` (Active, Passive)
- [x] 2.9 Define `UserCall` inductive (Open, Send, Receive, Close, Abort, Status) with relevant parameters — cite RFC 793 §3.8
- [x] 2.10 Define `TimeoutKind` inductive (UserTimeout, Retransmission, TimeWait)
- [x] 2.11 Define `UserResponse` inductive (Ok, Error, Data, StateInfo) for responses to user calls
- [x] 2.12 Verify `lake build Tcp.Types` succeeds with no `sorry`

## 3. State Machine and Event Processing (`Tcp/State.lean`) — RFC 793 §3.9
- [x] 3.1 Define `TcpEndpoint` structure (state : TcpState, tcb : Tcb, openMode : Option OpenMode, sendQueue : List UInt8, recvBuffer : List UInt8, reassemblyBuf : List Segment, retxQueue : List Segment, finSent : Bool)
- [x] 3.2 Define `System` structure (endpointA : TcpEndpoint, endpointB : TcpEndpoint, network : List Segment)
- [x] 3.3 Implement `processOpen` — per-state OPEN call processing (CLOSED: create TCB, passive→LISTEN or active→SYN-SENT with SYN; other states: error) — cite RFC 793 §3.9 OPEN Call
- [x] 3.4 Implement `processSend` — per-state SEND call processing (CLOSED: error; LISTEN: switch to active; SYN-SENT/SYN-RECEIVED: queue; ESTABLISHED/CLOSE-WAIT: segmentize; FIN-WAIT-*/CLOSING/LAST-ACK/TIME-WAIT: error) — cite RFC 793 §3.9 SEND Call
- [x] 3.5 Implement `processReceive` — per-state RECEIVE call processing — cite RFC 793 §3.9 RECEIVE Call
- [x] 3.6 Implement `processClose` — per-state CLOSE call processing (ESTABLISHED→FIN-WAIT-1, CLOSE-WAIT→LAST-ACK, etc.) — cite RFC 793 §3.9 CLOSE Call
- [x] 3.7 Implement `processAbort` — per-state ABORT call processing (send RST in synchronized states) — cite RFC 793 §3.9 ABORT Call
- [x] 3.8 Implement `processSegmentClosed` — SEGMENT ARRIVES in CLOSED state (RST generation) — cite RFC 793 §3.9 SEGMENT ARRIVES, CLOSED
- [x] 3.9 Implement `processSegmentListen` — SEGMENT ARRIVES in LISTEN state (RST check, ACK check, SYN processing → SYN-RECEIVED) — cite RFC 793 §3.9 SEGMENT ARRIVES, LISTEN
- [x] 3.10 Implement `processSegmentSynSent` — SEGMENT ARRIVES in SYN-SENT state (5-step pipeline: ACK check, RST check, security, SYN processing → ESTABLISHED or SYN-RECEIVED) — cite RFC 793 §3.9 SEGMENT ARRIVES, SYN-SENT
- [x] 3.11 Implement `processSegmentOtherwise` — SEGMENT ARRIVES in all remaining states (8-check pipeline): (1) sequence check/acceptability, (2) RST, (3) security, (4) SYN, (5) ACK + window update, (6) URG, (7) segment text, (8) FIN — cite RFC 793 §3.9 SEGMENT ARRIVES, "Otherwise"
- [x] 3.12 Implement `processTimeout` — USER TIMEOUT (abort), RETRANSMISSION TIMEOUT (resend head of retx queue), TIME-WAIT TIMEOUT (→ CLOSED) — cite RFC 793 §3.9 Timeouts
- [x] 3.13 Define `SystemStep` inductive relating `System` states (deliver segment, user call, timeout, loss, duplication)
- [x] 3.14 Verify `lake build Tcp.State` succeeds with no `sorry`

## 4. Segment Acceptability (`Tcp/Acceptability.lean`) — RFC 793 §3.3
- [x] 4.1 Define `segmentAcceptable' : Tcb → Segment → Bool` implementing the 4-case table
- [x] 4.2 Define `ackAcceptable : Tcb → Segment → Bool` implementing `SND.UNA < SEG.ACK ≤ SND.NXT` (ESTABLISHED and later) — cite RFC 793 §3.9 fifth check
- [x] 4.2a Define `ackAcceptableSynRecv : Tcb → Segment → Bool` implementing `SND.UNA ≤ SEG.ACK ≤ SND.NXT` (SYN-RECEIVED, non-strict left) — cite RFC 793 §3.9 fifth check, SYN-RECEIVED
- [x] 4.3 Prove: zero-length segment with zero window is acceptable iff `SEG.SEQ = RCV.NXT`
- [x] 4.4 Prove: segment with data is never acceptable when `RCV.WND = 0`
- [ ] 4.5 Prove: if a segment is acceptable and its sequence range is contained in the window, then both start and end are in the window
- [x] 4.6 Prove: `ackAcceptable` advances `SND.UNA` (if accepted, new `SND.UNA = SEG.ACK` satisfies `SND.UNA ≤ SND.NXT`)
- [x] 4.7 Verify `lake build Tcp.Acceptability` succeeds with no `sorry`

## 5. Connection Establishment Proofs (`Tcp/Handshake.lean`) — RFC 793 §3.4
- [x] 5.1 Prove normal three-way handshake correctness: starting from (A=CLOSED, B=LISTEN), after A does active OPEN, the system reaches (A=ESTABLISHED, B=ESTABLISHED) with `A.tcb.irs = B.tcb.iss` and `B.tcb.irs = A.tcb.iss` — cite RFC 793 §3.4 Figure 7
- [x] 5.2 Prove simultaneous open enters SYN-RECEIVED — cite RFC 793 §3.4 Figure 8
- [x] 5.3 Prove RST in SYN-RECEIVED (passive) returns to LISTEN — cite RFC 793 §3.4 Figure 9
- [x] 5.4 Prove RST in ESTABLISHED aborts — cite RFC 793 §3.4 Figures 10--11
- [x] 5.5 Prove SYN occupies sequence space: after handshake, `SND.NXT = ISS + 1` on both sides
- [ ] 5.6 Prove data piggybacked on SYN is buffered until ESTABLISHED — cite RFC 793 §3.4
- [ ] 5.7 Prove SYN-SENT "continue processing" semantics: SYN-ACK with data processes through steps 6-8 after ESTABLISHED transition — cite RFC 793 §3.9 SYN-SENT fourth check
- [x] 5.8 Verify `lake build Tcp.Handshake` succeeds with no `sorry`

## 6. Connection Teardown Proofs (`Tcp/Teardown.lean`) — RFC 793 §3.5
- [x] 6.1 Prove normal close: A issues CLOSE from ESTABLISHED → FIN-WAIT-1; B receives FIN → CLOSE-WAIT; B CLOSE → LAST-ACK — cite RFC 793 §3.5 Figure 13
- [ ] 6.2 Prove simultaneous close: both issue CLOSE from ESTABLISHED, both transition through FIN-WAIT-1 → CLOSING → TIME-WAIT → CLOSED — cite RFC 793 §3.5 Figure 14
- [x] 6.3 Prove FIN occupies sequence space: FIN increments `SND.NXT` by 1
- [x] 6.4 Prove TIME-WAIT timeout → CLOSED
- [ ] 6.5 Prove TIME-WAIT FIN retransmission: a retransmitted FIN in TIME-WAIT is ACKed and the 2×MSL timer is restarted — cite RFC 793 §3.9 eighth check, TIME-WAIT
- [ ] 6.6 Prove data can be received in FIN-WAIT-1 and FIN-WAIT-2 — cite RFC 793 §3.5, §3.9 seventh check
- [ ] 6.7 Prove FIN with data: data is processed (step 7) before FIN (step 8), FIN implies PUSH — cite RFC 793 §3.9 eighth check
- [ ] 6.8 Prove FIN acknowledgment detection: FIN is acknowledged when `SEG.ACK > finSeqNum` — cite RFC 793 §3.9 fifth check, FIN-WAIT-1
- [ ] 6.9 Prove FIN ordering guarantee: FIN is sent only after all preceding SEND data is segmentized — cite RFC 793 §3.9 CLOSE Call, §3.5
- [x] 6.10 Prove RST in TIME-WAIT causes immediate transition to CLOSED — cite RFC 793 §3.9 second check
- [x] 6.11 Verify `lake build Tcp.Teardown` succeeds with no `sorry`

## 7. Safety Invariants (`Tcp/Invariants.lean`)
- [x] 7.1 Prove sequence number monotonicity `SND.UNA ≤ SND.NXT` preserved across handshake, close, and send (concrete values)
- [ ] 7.2 Prove send window bound: data is only sent with sequence numbers in `[SND.UNA, SND.UNA + SND.WND)` and `SND.NXT ≤ SND.UNA + SND.WND` is invariant — cite RFC 793 §3.7
- [ ] 7.3 Prove receive window monotonicity: `RCV.NXT + RCV.WND` does not decrease across `SystemStep` — cite RFC 793 §3.7
- [ ] 7.4 Prove ACK monotonicity: `SND.UNA` only advances (never retreats) across `SystemStep`
- [x] 7.5 Prove no data before ESTABLISHED: RECEIVE in pre-ESTABLISHED states never returns Data
- [ ] 7.6 Prove in-order delivery: data bytes delivered to the user via RECEIVE appear in the same order as their sequence numbers in the original SEND calls
- [x] 7.7 Define window update condition predicate
- [ ] 7.8 Prove `RCV.NXT` monotonicity: `RCV.NXT` only advances across `SystemStep` — cite RFC 793 §3.9 seventh check
- [ ] 7.9 Prove RST validation: state-dependent rules (SYN-SENT: ACK-based; others: sequence-in-window) — cite RFC 793 §3.4, §3.9 second check
- [x] 7.10 Verify `lake build Tcp.Invariants` succeeds with no `sorry`

## 8. Whitepaper Content (`whitepaper.tex`)
- [x] 8.1 Write Introduction section (motivation, contributions, related work)
- [x] 8.2 Write Sequence Numbers section (definition, properties, relation to RFC 793 §3.3)
- [x] 8.3 Write Core Types section (structures, design choices, relation to RFC 793 §3.1--3.2)
- [x] 8.4 Write State Machine section (system model, event processing, relation to RFC 793 §3.9)
- [x] 8.5 Write Segment Acceptability section (predicate, 4-case table, lemmas)
- [x] 8.6 Write Connection Establishment section (theorems, handshake scenarios, figures)
- [x] 8.7 Write Connection Teardown section (theorems, close scenarios, TIME-WAIT)
- [x] 8.8 Write Invariants section (safety properties, proof sketches)
- [x] 8.9 Write Conclusion section (summary, limitations, future work)
- [x] 8.10 Verify full LaTeX build succeeds (`pdflatex` + `bibtex`)

## 9. Final Validation
- [x] 9.1 Verify `lake build` succeeds on the full project with zero `sorry`
- [x] 9.2 Verify every Lean doc comment cites the relevant RFC 793 section
- [x] 9.3 Verify every whitepaper theorem reference maps to a named Lean theorem
