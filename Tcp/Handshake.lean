import Tcp.SeqNum
import Tcp.Types
import Tcp.State

/-!
# Three-Way Handshake Correctness

Correctness theorems for TCP connection establishment per RFC 793 §3.4.

This module proves that the three-way handshake (SYN → SYN-ACK → ACK)
correctly transitions both endpoints from CLOSED/LISTEN to ESTABLISHED
with synchronized sequence numbers. It also covers simultaneous open
(both endpoints in SYN-SENT), old-duplicate-SYN recovery, and half-open
connection detection via RST.

Key theorems:
- `threeWayHandshake_correct`: normal active/passive open reaches ESTABLISHED
  (for arbitrary ISS values)
- `syn_occupies_sequence_space`: SND.NXT = ISS + 1 after SYN
-/

namespace Tcp

open SeqNum

-- ============================================================================
-- Basic open and SYN properties
-- ============================================================================

/-- After A performs active OPEN from CLOSED, A is in SYN-SENT.
    RFC 793 §3.9 OPEN Call, CLOSED + active. -/
theorem activeOpen_synSent (issA : SeqNum) :
    (processOpen {} (.Active) issA).endpoint.state = .SynSent := by
  simp [processOpen, freshTcb]

/-- Active OPEN emits exactly one segment (the SYN). -/
theorem activeOpen_emits_syn (issA : SeqNum) :
    (processOpen {} (.Active) issA).segments.length = 1 := by
  simp [processOpen, freshTcb, mkSegment]

/-- SYN occupies one sequence number: after sending SYN, SND.NXT = ISS + 1.
    RFC 793 §3.3: "the SYN is considered to occur before the first actual
    data octet." -/
theorem syn_occupies_sequence_space (issA : SeqNum) :
    (processOpen {} (.Active) issA).endpoint.tcb.sndNxt = issA.add 1 := by
  simp [processOpen, freshTcb]

/-- Passive OPEN from CLOSED enters LISTEN.
    RFC 793 §3.9 OPEN Call, CLOSED + passive. -/
theorem passiveOpen_listen (iss : SeqNum) :
    (processOpen {} (.Passive) iss).endpoint.state = .Listen := by
  simp [processOpen, freshTcb]

/-- When a SYN arrives at a LISTEN endpoint, it transitions to SYN-RECEIVED.
    RFC 793 §3.9 SEGMENT ARRIVES, LISTEN, step 3 (SYN). -/
theorem syn_at_listen_enters_synReceived (issB : SeqNum) (syn : Segment)
    (hSyn : syn.ctl.syn = true) (hNoRst : syn.ctl.rst = false)
    (hNoAck : syn.ctl.ack = false) :
    let listenEp := (processOpen {} (.Passive) issB).endpoint
    let result := processSegmentListen listenEp syn issB
    result.endpoint.state = .SynReceived := by
  simp [processOpen, freshTcb, processSegmentListen, hSyn, hNoRst, hNoAck]

/-- The IRS recorded after SYN arrival equals the SYN's sequence number. -/
theorem syn_at_listen_records_irs (issB : SeqNum) (syn : Segment)
    (hSyn : syn.ctl.syn = true) (hNoRst : syn.ctl.rst = false)
    (hNoAck : syn.ctl.ack = false) :
    let listenEp := (processOpen {} (.Passive) issB).endpoint
    let result := processSegmentListen listenEp syn issB
    result.endpoint.tcb.irs = syn.seq := by
  simp [processOpen, freshTcb, processSegmentListen, hSyn, hNoRst, hNoAck]

-- ============================================================================
-- Three-Way Handshake — RFC 793 §3.4, Figure 7 (Symbolic)
-- ============================================================================

/-- Full three-way handshake correctness for arbitrary ISS values.

    RFC 793 §3.4, Figure 7:
    ```
    TCP A                                             TCP B
    CLOSED                                            LISTEN
    SYN-SENT    --> <SEQ=issA><CTL=SYN>            --> SYN-RECEIVED
    ESTABLISHED <-- <SEQ=issB><ACK=issA+1><CTL=SYN,ACK> <-- SYN-RECEIVED
    ESTABLISHED --> <SEQ=issA+1><ACK=issB+1><CTL=ACK>   --> ESTABLISHED
    ``` -/
theorem threeWayHandshake_correct (issA issB : SeqNum) :
    let openA := processOpen {} (.Active) issA
    let synSeg := openA.segments.head!
    let listenB := (processOpen {} (.Passive) issB).endpoint
    let step2 := processSegmentListen listenB synSeg issB
    let synAckSeg := step2.segments.head!
    let step3 := processSegmentSynSent openA.endpoint synAckSeg
    let ackSeg := step3.segments.head!
    let step4 := processSegmentOtherwise step2.endpoint ackSeg
    -- Both ESTABLISHED
    step3.endpoint.state = .Established ∧
    step4.endpoint.state = .Established ∧
    -- Sequence numbers synchronized: each side's IRS = other's ISS
    step3.endpoint.tcb.irs = issB ∧
    step4.endpoint.tcb.irs = issA := by
  -- Pass 1: unfold all processing functions to expose SeqNum operations
  simp only [processOpen, freshTcb, mkSegment, processSegmentListen,
    processSegmentSynSent, processSegmentOtherwise, pipelinePreAck,
    pipelineAck, pipelinePostAck, pipelineAckReject,
    ackUpdate, ackAdvanceTcb, windowUpdateTcb,
    pipelineUrg, pipelineText, pipelineFin,
    segmentAcceptable, defaultRcvWnd, List.head!, List.isEmpty,
    Nat.toUInt32, SeqNum.add, Segment.len, removeAcked, closedEndpoint]
  -- Pass 2: resolve SeqNum comparisons via modular arithmetic
  simp [SeqNum.lt, SeqNum.le, SeqNum.halfSpace, UInt32.add_sub_self]

/-- In simultaneous open, receiving a SYN (no ACK) in SYN-SENT enters
    SYN-RECEIVED (not ESTABLISHED).
    RFC 793 §3.9 SEGMENT ARRIVES, SYN-SENT, step 4: "Otherwise, enter
    SYN-RECEIVED". -/
theorem simultaneousOpen_enters_synReceived (issA issB : SeqNum) :
    let openA := processOpen {} (.Active) issA
    let synB := (processOpen {} (.Active) issB).segments.head!
    -- A (SYN-SENT) receives B's SYN (no ACK) → SYN-RECEIVED
    let stepA := processSegmentSynSent openA.endpoint synB
    stepA.endpoint.state = .SynReceived := by
  simp only [processOpen, freshTcb, mkSegment, processSegmentSynSent,
    defaultRcvWnd, List.head!, SeqNum.add]
  simp [SeqNum.lt, SeqNum.halfSpace]

-- ============================================================================
-- Old Duplicate SYN Recovery — RFC 793 §3.4, Figure 9
-- ============================================================================

/-- When a RST arrives at SYN-RECEIVED that originated from LISTEN (passive),
    the endpoint returns to LISTEN.
    RFC 793 §3.9 second check, SYN-RECEIVED with passive open mode. -/
theorem rst_synReceived_passive_returns_to_listen (ep : TcpEndpoint)
    (rst : Segment)
    (hState : ep.state = .SynReceived)
    (hMode : ep.openMode = some .Passive)
    (hRst : rst.ctl.rst = true)
    (hAcceptable : segmentAcceptable ep.tcb rst = true) :
    (processSegmentOtherwise ep rst).endpoint.state = .Listen := by
  simp [processSegmentOtherwise, pipelinePreAck, hAcceptable, hRst, hState, hMode]

-- ============================================================================
-- Half-Open Connection Detection — RFC 793 §3.4, Figures 10-11
-- ============================================================================

/-- When a RST arrives at ESTABLISHED with acceptable sequence number,
    the connection is aborted.
    RFC 793 §3.9 second check, ESTABLISHED: "enter CLOSED state, delete TCB". -/
theorem rst_established_aborts (ep : TcpEndpoint)
    (rst : Segment)
    (hState : ep.state = .Established)
    (hRst : rst.ctl.rst = true)
    (hAcceptable : segmentAcceptable ep.tcb rst = true) :
    (processSegmentOtherwise ep rst).endpoint.state = .Closed := by
  simp [processSegmentOtherwise, pipelinePreAck, hAcceptable, hRst, hState, closedEndpoint]

end Tcp
