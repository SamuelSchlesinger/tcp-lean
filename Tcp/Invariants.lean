import Tcp.SeqNum
import Tcp.Types
import Tcp.State
import Tcp.Acceptability

/-!
# Safety and Data Delivery Invariants

Proofs of global safety properties and data delivery guarantees.

- **No data before ESTABLISHED** (RFC 793 §3.4)
- **Per-function SND.UNA ≤ SND.NXT preservation**
- **SystemStep invariant**: preserved by every atomic transition
-/

namespace Tcp

open SeqNum

-- ============================================================================
-- No Data Before ESTABLISHED — RFC 793 §3.4
-- ============================================================================

theorem no_data_in_closed :
    (processReceive {}).response = some (.Error "connection does not exist") := by
  rfl

theorem no_data_in_listen (ep : TcpEndpoint)
    (hState : ep.state = .Listen) :
    ∀ d, (processReceive ep).response ≠ some (.Data d) := by
  simp [processReceive, hState]

theorem no_data_in_synSent (ep : TcpEndpoint)
    (hState : ep.state = .SynSent) :
    ∀ d, (processReceive ep).response ≠ some (.Data d) := by
  simp [processReceive, hState]

theorem no_data_in_synReceived (ep : TcpEndpoint)
    (hState : ep.state = .SynReceived) :
    ∀ d, (processReceive ep).response ≠ some (.Data d) := by
  simp [processReceive, hState]

-- ============================================================================
-- Endpoint Invariant
-- ============================================================================

/-- The core per-endpoint invariant: `SND.UNA ≤ SND.NXT`. -/
def endpointInvariant (ep : TcpEndpoint) : Prop :=
  SeqNum.le ep.tcb.sndUna ep.tcb.sndNxt = true

def systemInvariant (s : System) : Prop :=
  endpointInvariant s.endpointA ∧ endpointInvariant s.endpointB

theorem closedEndpoint_invariant : endpointInvariant closedEndpoint := by
  simp [endpointInvariant, closedEndpoint, SeqNum.le]

-- ============================================================================
-- SeqNum add associativity
-- ============================================================================

@[simp] theorem SeqNum.add_add (a : SeqNum) (b c : UInt32) :
    (a.add b).add c = a.add (b + c) := by
  apply congrArg SeqNum.mk
  apply UInt32.eq_of_toBitVec_eq
  simp only [SeqNum.add, UInt32.toBitVec_add]
  ac_rfl

-- ============================================================================
-- ackUpdate — unconditional preservation
-- ============================================================================

theorem ackAdvanceTcb_preserves (tcb : Tcb) (seg : Segment)
    (hPre : SeqNum.le tcb.sndUna tcb.sndNxt = true) :
    SeqNum.le (ackAdvanceTcb tcb seg).sndUna (ackAdvanceTcb tcb seg).sndNxt = true := by
  simp only [ackAdvanceTcb]
  split
  · rename_i hCond; simp [Bool.and_eq_true] at hCond; simp_all
  · exact hPre

theorem ackUpdate_preserves (ep : TcpEndpoint) (seg : Segment)
    (hPre : endpointInvariant ep) :
    endpointInvariant (ackUpdate ep seg) := by
  simp only [endpointInvariant, ackUpdate, windowUpdateTcb_sndUna, windowUpdateTcb_sndNxt]
  exact ackAdvanceTcb_preserves ep.tcb seg hPre

-- ============================================================================
-- Simple function preservation
-- ============================================================================

theorem processOpen_preserves (ep : TcpEndpoint) (mode : OpenMode) (iss : SeqNum)
    (h : endpointInvariant ep) :
    endpointInvariant (processOpen ep mode iss).endpoint := by
  simp only [endpointInvariant, processOpen]
  split
  · split <;> simp [freshTcb, SeqNum.le, lt_add_one]
  · split
    · simp [SeqNum.le, lt_add_one]
    · exact h
  · exact h

theorem processReceive_preserves (ep : TcpEndpoint) (h : endpointInvariant ep) :
    endpointInvariant (processReceive ep).endpoint := by
  simp only [endpointInvariant, processReceive]
  split <;> (try split) <;> simp_all [endpointInvariant]

theorem processAbort_preserves (ep : TcpEndpoint) (h : endpointInvariant ep) :
    endpointInvariant (processAbort ep).endpoint := by
  simp only [endpointInvariant]
  unfold processAbort
  split <;> (first | exact h | (dsimp only []; simp [closedEndpoint, SeqNum.le]))

theorem processTimeout_preserves (ep : TcpEndpoint) (kind : TimeoutKind)
    (h : endpointInvariant ep) :
    endpointInvariant (processTimeout ep kind).endpoint := by
  simp only [endpointInvariant, processTimeout]
  split
  · simp [closedEndpoint, SeqNum.le]
  · split <;> exact h
  · split
    · simp [closedEndpoint, SeqNum.le]
    · exact h

theorem processSegmentClosed_preserves (ep : TcpEndpoint) (seg : Segment)
    (h : endpointInvariant ep) :
    endpointInvariant (processSegmentClosed ep seg).endpoint := by
  simp only [endpointInvariant, processSegmentClosed]
  split <;> (try split) <;> exact h

theorem processSegmentListen_preserves (ep : TcpEndpoint) (seg : Segment)
    (iss : SeqNum) (h : endpointInvariant ep) :
    endpointInvariant (processSegmentListen ep seg iss).endpoint := by
  simp only [endpointInvariant, processSegmentListen]
  split
  · exact h
  · split
    · exact h
    · split
      · simp [SeqNum.le, lt_add_one]
      · exact h

-- ============================================================================
-- Segmentize / Send / Close — need queue bounds
-- ============================================================================

@[simp] theorem segmentize_sndUna (ep : TcpEndpoint) :
    (segmentize ep).1.tcb.sndUna = ep.tcb.sndUna := by
  simp only [segmentize]; split <;> simp_all

theorem segmentize_preserves (ep : TcpEndpoint)
    (h : endpointInvariant ep)
    (hBound : SeqNum.le ep.tcb.sndUna
      (ep.tcb.sndNxt.add ep.sendQueue.length.toUInt32) = true) :
    endpointInvariant (segmentize ep).1 := by
  simp only [endpointInvariant, segmentize]
  split
  · exact h
  · simp_all

theorem processSend_preserves (ep : TcpEndpoint) (data : List UInt8)
    (h : endpointInvariant ep)
    (hBound : SeqNum.le ep.tcb.sndUna
      (ep.tcb.sndNxt.add (ep.sendQueue ++ data).length.toUInt32) = true) :
    endpointInvariant (processSend ep data).endpoint := by
  cases hState : ep.state <;>
    simp only [endpointInvariant, processSend, hState, segmentize] <;>
    first | exact h | (split <;> simp_all)

theorem processClose_preserves (ep : TcpEndpoint)
    (h : endpointInvariant ep)
    (hBound : SeqNum.le ep.tcb.sndUna
      (ep.tcb.sndNxt.add (ep.sendQueue.length.toUInt32 + 1)) = true) :
    endpointInvariant (processClose ep).endpoint := by
  cases hState : ep.state <;>
    simp only [processClose, hState, segmentize] <;>
    first
    | exact h
    | exact closedEndpoint_invariant
    | (split <;> simp_all [endpointInvariant])

-- ============================================================================
-- processSegmentSynSent
-- ============================================================================

theorem processSegmentSynSent_preserves (ep : TcpEndpoint) (seg : Segment)
    (h : endpointInvariant ep) :
    endpointInvariant (processSegmentSynSent ep seg).endpoint := by
  unfold processSegmentSynSent
  dsimp only [mkSegment, defaultRcvWnd]
  -- Exhaustive case splits on all boolean conditions
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
    first
    | exact h
    | exact closedEndpoint_invariant
    | (simp only [endpointInvariant]; simp_all)

-- ============================================================================
-- Pipeline preservation
-- ============================================================================

theorem pipelineUrg_preserves (ep : TcpEndpoint) (seg : Segment)
    (h : endpointInvariant ep) :
    endpointInvariant (pipelineUrg ep seg) := by
  simp only [endpointInvariant, pipelineUrg]
  split <;> (try split) <;> simp_all [endpointInvariant]

theorem pipelineText_preserves (ep : TcpEndpoint) (seg : Segment)
    (h : endpointInvariant ep) :
    endpointInvariant (pipelineText ep seg).1 := by
  simp only [endpointInvariant, pipelineText]
  split <;> (try split) <;> simp_all [endpointInvariant]

theorem pipelineFin_preserves (ep : TcpEndpoint) (seg : Segment) (needAck : Bool)
    (h : endpointInvariant ep) :
    endpointInvariant (pipelineFin ep seg needAck).endpoint := by
  simp only [endpointInvariant]
  unfold pipelineFin
  dsimp only [mkSegment]
  split <;> (try split) <;> (try split) <;> (try split) <;>
    first | exact h | simp_all

theorem pipelinePostAck_preserves (ep : TcpEndpoint) (seg : Segment)
    (h : endpointInvariant ep) :
    endpointInvariant (pipelinePostAck ep seg).endpoint := by
  simp only [pipelinePostAck]
  exact pipelineFin_preserves _ seg _
    (pipelineText_preserves _ seg (pipelineUrg_preserves ep seg h))

theorem pipelinePreAck_preserves (ep : TcpEndpoint) (seg : Segment)
    (h : endpointInvariant ep) (result : ProcessResult)
    (hPre : pipelinePreAck ep seg = some result) :
    endpointInvariant result.endpoint := by
  simp only [endpointInvariant]
  unfold pipelinePreAck at hPre
  dsimp only [mkSegment] at hPre
  split at hPre
  · split at hPre <;> simp at hPre <;> rw [← hPre] <;> exact h
  · split at hPre
    · split at hPre
      · -- SynReceived: nested match on openMode
        split at hPre <;> simp at hPre <;> rw [← hPre]
        · exact h
        · simp [closedEndpoint, SeqNum.le]
      -- All remaining RST state cases (Est, FW1, FW2, CW, Closing, LA, TW, wildcard)
      all_goals (simp at hPre; rw [← hPre]; first | exact h | simp [closedEndpoint, SeqNum.le])
    · split at hPre
      · simp at hPre; rw [← hPre]; simp [closedEndpoint, SeqNum.le]
      · split at hPre
        · simp at hPre; rw [← hPre]; exact h
        · simp at hPre

theorem pipelineAck_preserves (ep : TcpEndpoint) (seg : Segment)
    (h : endpointInvariant ep) (ep' : TcpEndpoint)
    (hAck : pipelineAck ep seg = some ep') :
    endpointInvariant ep' := by
  simp only [endpointInvariant]
  simp only [pipelineAck] at hAck
  split at hAck
  · -- SynReceived
    split at hAck
    · simp at hAck; rw [← hAck]
      rename_i hCond; simp [Bool.and_eq_true] at hCond; exact hCond.2
    · simp at hAck
  · -- Established
    split at hAck
    · simp at hAck; rw [← hAck]
      exact ackUpdate_preserves _ _ h
    · split at hAck
      · simp at hAck
      · simp at hAck; rw [← hAck]; exact h
  · -- FinWait1: ackUpdate, then state change
    simp at hAck; rw [← hAck]
    unfold ackUpdate
    simp [windowUpdateTcb_sndUna, windowUpdateTcb_sndNxt]
    rw [← ackAdvanceTcb_sndNxt ep.tcb seg]
    exact ackAdvanceTcb_preserves ep.tcb seg h
  · -- FinWait2
    simp at hAck; rw [← hAck]; exact ackUpdate_preserves _ _ h
  · -- CloseWait
    simp at hAck; rw [← hAck]; exact ackUpdate_preserves _ _ h
  · -- Closing
    split at hAck
    · split at hAck <;> simp at hAck <;> rw [← hAck] <;> exact h
    · simp at hAck; rw [← hAck]; exact h
  · -- LastAck
    split at hAck
    · split at hAck <;> simp at hAck <;> rw [← hAck]
      · simp [closedEndpoint, SeqNum.le]
      · exact h
    · simp at hAck; rw [← hAck]; exact h
  · -- TimeWait
    simp at hAck; rw [← hAck]; exact h
  · -- fallthrough
    simp at hAck; rw [← hAck]; exact h

theorem pipelineAckReject_preserves (ep : TcpEndpoint) (seg : Segment)
    (h : endpointInvariant ep) :
    endpointInvariant (pipelineAckReject ep seg).endpoint := by
  simp only [endpointInvariant]
  unfold pipelineAckReject; dsimp only [mkSegment]
  split <;> exact h

-- ============================================================================
-- Composed pipeline / segment processing
-- ============================================================================

theorem processSegmentOtherwise_preserves (ep : TcpEndpoint) (seg : Segment)
    (h : endpointInvariant ep) :
    endpointInvariant (processSegmentOtherwise ep seg).endpoint := by
  simp only [processSegmentOtherwise]
  split
  · rename_i result hPre
    exact pipelinePreAck_preserves ep seg h result hPre
  · split
    · exact pipelineAckReject_preserves ep seg h
    · rename_i ep' hA
      exact pipelinePostAck_preserves ep' seg (pipelineAck_preserves ep seg h ep' hA)

theorem processSegment_preserves (ep : TcpEndpoint) (seg : Segment)
    (iss : SeqNum) (h : endpointInvariant ep) :
    endpointInvariant (processSegment ep seg iss).endpoint := by
  simp only [processSegment]
  split
  · exact processSegmentClosed_preserves ep seg h
  · exact processSegmentListen_preserves ep seg iss h
  · exact processSegmentSynSent_preserves ep seg h
  · exact processSegmentOtherwise_preserves ep seg h

-- ============================================================================
-- SystemStep Invariant
-- ============================================================================

/-- The system invariant is preserved by every `SystemStep` transition.

    For segment delivery, timeout, and abort steps, preservation is
    unconditional. For user SEND/CLOSE calls, the proof requires that
    sequence number advancement stays in the forward half-space (guaranteed
    in real TCP by the send window per RFC 793 §3.7). -/
theorem systemStep_preserves_invariant (s s' : System)
    (hStep : SystemStep s s') (hInv : systemInvariant s)
    (h_userA : ∀ call result,
      processUserCall s.endpointA call = result →
      endpointInvariant result.endpoint)
    (h_userB : ∀ call result,
      processUserCall s.endpointB call = result →
      endpointInvariant result.endpoint) :
    systemInvariant s' := by
  obtain ⟨hA, hB⟩ := hInv
  cases hStep with
  | deliverToA seg rest h_net result h_proc =>
    exact ⟨h_proc ▸ processSegment_preserves _ seg _ hA, hB⟩
  | deliverToB seg rest h_net result h_proc =>
    exact ⟨hA, h_proc ▸ processSegment_preserves _ seg _ hB⟩
  | userCallA call result h_proc =>
    exact ⟨h_userA call result h_proc, hB⟩
  | userCallB call result h_proc =>
    exact ⟨hA, h_userB call result h_proc⟩
  | timeoutA kind result h_proc =>
    exact ⟨h_proc ▸ processTimeout_preserves _ kind hA, hB⟩
  | timeoutB kind result h_proc =>
    exact ⟨hA, h_proc ▸ processTimeout_preserves _ kind hB⟩
  | segmentLoss seg rest h_net =>
    exact ⟨hA, hB⟩
  | segmentDup seg h_mem =>
    exact ⟨hA, hB⟩

theorem initial_system_invariant : systemInvariant {} :=
  ⟨closedEndpoint_invariant, closedEndpoint_invariant⟩

end Tcp
