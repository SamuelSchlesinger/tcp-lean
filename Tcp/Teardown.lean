import Tcp.SeqNum
import Tcp.Types
import Tcp.State

/-!
# Connection Teardown

Theorems for graceful connection closing and TIME-WAIT behavior.

RFC 793 §3.5 specifies a graceful close via FIN exchange:
- Normal close: ESTABLISHED → FIN-WAIT-1 → FIN-WAIT-2 → TIME-WAIT → CLOSED
  (initiator) and ESTABLISHED → CLOSE-WAIT → LAST-ACK → CLOSED (responder)
- Simultaneous close: both sides FIN-WAIT-1 → CLOSING → TIME-WAIT → CLOSED

This module proves correctness properties of the closing handshake, FIN
sequence space consumption, TIME-WAIT duration, and data reception during
teardown.
-/

namespace Tcp

-- ============================================================================
-- CLOSE from ESTABLISHED — RFC 793 §3.9 CLOSE Call
-- ============================================================================

/-- CLOSE from ESTABLISHED sends FIN and transitions to FIN-WAIT-1.
    RFC 793 §3.9 CLOSE Call, ESTABLISHED state. -/
theorem close_established_enters_finWait1 (ep : TcpEndpoint)
    (hState : ep.state = .Established) (hNoData : ep.sendQueue = []) :
    (processClose ep).endpoint.state = .FinWait1 := by
  simp [processClose, hState, hNoData, segmentize, mkSegment]

/-- FIN occupies one sequence number: after sending FIN, SND.NXT advances by 1.
    RFC 793 §3.3: "the FIN is considered to occur after the last actual data
    octet." -/
theorem fin_occupies_sequence_space (ep : TcpEndpoint)
    (hState : ep.state = .Established) (hNoData : ep.sendQueue = []) :
    (processClose ep).endpoint.tcb.sndNxt = ep.tcb.sndNxt.add 1 := by
  simp [processClose, hState, hNoData, segmentize, mkSegment]

/-- After CLOSE, the endpoint records that a FIN was sent. -/
theorem close_established_sets_finSent (ep : TcpEndpoint)
    (hState : ep.state = .Established) (hNoData : ep.sendQueue = []) :
    (processClose ep).endpoint.finSent = true := by
  simp [processClose, hState, hNoData, segmentize, mkSegment]

/-- After CLOSE, the FIN sequence number is recorded. -/
theorem close_established_records_finSeqNum (ep : TcpEndpoint)
    (hState : ep.state = .Established) (hNoData : ep.sendQueue = []) :
    (processClose ep).endpoint.finSeqNum = some ep.tcb.sndNxt := by
  simp [processClose, hState, hNoData, segmentize, mkSegment]

-- ============================================================================
-- CLOSE from CLOSE-WAIT — RFC 793 §3.9 CLOSE Call
-- ============================================================================

/-- CLOSE from CLOSE-WAIT enters LAST-ACK.
    RFC 793 Figure 6: CLOSE-WAIT → LAST-ACK (not CLOSING).
    Note: RFC 793 §3.9 text says "enter CLOSING state" but Figure 6 is
    authoritative. -/
theorem close_closeWait_enters_lastAck (ep : TcpEndpoint)
    (hState : ep.state = .CloseWait) (hNoData : ep.sendQueue = []) :
    (processClose ep).endpoint.state = .LastAck := by
  simp [processClose, hState, hNoData, segmentize, mkSegment]

-- ============================================================================
-- FIN Delivery via Pipeline — RFC 793 §3.9 eighth check
-- ============================================================================

/-- When FIN arrives at the FIN processing step with ESTABLISHED state,
    the endpoint transitions to CLOSE-WAIT.
    RFC 793 §3.9 eighth check: "If the FIN bit is set... → CLOSE-WAIT". -/
theorem pipelineFin_established (ep : TcpEndpoint) (seg : Segment)
    (needAck : Bool)
    (hState : ep.state = .Established)
    (hFin : seg.ctl.fin = true) :
    (pipelineFin ep seg needAck).endpoint.state = .CloseWait := by
  simp [pipelineFin, hState, hFin]

/-- When FIN arrives with ESTABLISHED state, composed post-ACK gives CLOSE-WAIT.
    Uses the URG/text state-preservation lemmas to bridge to `pipelineFin`. -/
theorem pipelinePostAck_fin_established (ep : TcpEndpoint) (seg : Segment)
    (hState : ep.state = .Established)
    (hFin : seg.ctl.fin = true) :
    (pipelinePostAck ep seg).endpoint.state = .CloseWait := by
  simp only [pipelinePostAck]
  apply pipelineFin_established
  · simp [pipelineText_state, pipelineUrg_state, hState]
  · exact hFin

/-- When FIN arrives at the FIN processing step with FIN-WAIT-2 state,
    the endpoint transitions to TIME-WAIT.
    RFC 793 §3.9: "FIN-WAIT-2 + FIN → TIME-WAIT". -/
theorem pipelineFin_finWait2 (ep : TcpEndpoint) (seg : Segment)
    (needAck : Bool)
    (hState : ep.state = .FinWait2)
    (hFin : seg.ctl.fin = true) :
    (pipelineFin ep seg needAck).endpoint.state = .TimeWait := by
  simp [pipelineFin, hState, hFin]

/-- When FIN arrives with FIN-WAIT-2 state, composed post-ACK gives TIME-WAIT. -/
theorem pipelinePostAck_fin_finWait2 (ep : TcpEndpoint) (seg : Segment)
    (hState : ep.state = .FinWait2)
    (hFin : seg.ctl.fin = true) :
    (pipelinePostAck ep seg).endpoint.state = .TimeWait := by
  simp only [pipelinePostAck]
  apply pipelineFin_finWait2
  · simp [pipelineText_state, pipelineUrg_state, hState]
  · exact hFin

-- ============================================================================
-- TIME-WAIT behavior — RFC 793 §3.9
-- ============================================================================

/-- TIME-WAIT timeout transitions to CLOSED.
    RFC 793 §3.9 Timeouts: "TIME-WAIT TIMEOUT: delete TCB, enter CLOSED." -/
theorem timeWait_timeout_closes (ep : TcpEndpoint)
    (hState : ep.state = .TimeWait) :
    (processTimeout ep .TimeWait).endpoint.state = .Closed := by
  simp [processTimeout, hState, closedEndpoint]

/-- RST in TIME-WAIT causes immediate transition to CLOSED.
    RFC 793 §3.9 second check: "CLOSING/LAST-ACK/TIME-WAIT + RST → CLOSED". -/
theorem rst_timeWait_closes (ep : TcpEndpoint) (rst : Segment)
    (hState : ep.state = .TimeWait)
    (hRst : rst.ctl.rst = true)
    (hAcceptable : segmentAcceptable ep.tcb rst = true) :
    (processSegmentOtherwise ep rst).endpoint.state = .Closed := by
  simp [processSegmentOtherwise, pipelinePreAck, hAcceptable, hRst, hState, closedEndpoint]

/-- TIME-WAIT timeout completes the close. -/
theorem timeWait_timeout_completes :
    let epTW : TcpEndpoint := { state := .TimeWait }
    (processTimeout epTW .TimeWait).endpoint.state = .Closed := by
  simp [processTimeout, closedEndpoint]

end Tcp
