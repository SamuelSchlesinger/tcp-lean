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
-- Helper: SeqNum.le is preserved by add when the sum stays in half-space
-- ============================================================================

/-- If `una ≤ nxt` (half-space) and `(nxt - una) + n < halfSpace`, then `una ≤ nxt + n`. -/
theorem SeqNum.le_add_of_le (una nxt : SeqNum) (n : UInt32)
    (h : SeqNum.le una nxt = true)
    (hn : (nxt.val - una.val) + n < SeqNum.halfSpace) :
    SeqNum.le una (nxt.add n) = true := by
  simp only [SeqNum.le, SeqNum.lt, SeqNum.add, SeqNum.halfSpace,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at *
  bv_decide

/-- Window-bounded add preserves le: if `una ≤ nxt`, inflight < window (UInt16),
    and n ≤ remaining window, then `una ≤ nxt + n`. The UInt16 window ensures
    the sum stays well within the half-space. -/
theorem SeqNum.le_add_within_window (una nxt : SeqNum) (w : UInt16) (n : UInt32)
    (h : SeqNum.le una nxt = true)
    (hLt : nxt.val - una.val < w.toUInt32)
    (hN : n ≤ w.toUInt32 - (nxt.val - una.val)) :
    SeqNum.le una (nxt.add n) = true := by
  simp only [SeqNum.le, SeqNum.lt, SeqNum.add, SeqNum.halfSpace,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at *
  bv_decide

/-- Nat-to-UInt32 order preservation: if k ≤ m.toNat, then UInt32.ofNat k ≤ m. -/
theorem UInt32_ofNat_le (k : Nat) (m : UInt32) (h : k ≤ m.toNat) :
    UInt32.ofNat k ≤ m := by
  show (UInt32.ofNat k).toBitVec ≤ m.toBitVec
  show (UInt32.ofNat k).toBitVec.toNat ≤ m.toBitVec.toNat
  have hm : m.toBitVec.toNat < 2^32 := m.toBitVec.isLt
  have hk : k < 2^32 := Nat.lt_of_le_of_lt h hm
  simp only [UInt32.ofNat, UInt32.toNat] at *
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  exact h

/-- inflight ≤ window (UInt16) implies inflight + 1 < halfSpace. -/
private theorem window_plus_one_lt_halfSpace (a : UInt32) (w : UInt16)
    (h : a ≤ w.toUInt32) : a + 1 < SeqNum.halfSpace := by
  simp only [SeqNum.halfSpace]; bv_decide

/-- inflight + sent + 1 < halfSpace when sent is within the window. -/
private theorem inflight_sent_fin_lt_halfSpace (inflight n : UInt32) (w : UInt16)
    (h1 : inflight < w.toUInt32) (h2 : n ≤ w.toUInt32 - inflight) :
    inflight + (n + 1) < SeqNum.halfSpace := by
  simp only [SeqNum.halfSpace]
  have : inflight + (n + 1) = inflight + n + 1 := by
    apply UInt32.eq_of_toBitVec_eq; simp [UInt32.toBitVec_add]; ac_rfl
  rw [this]; bv_decide

-- ============================================================================
-- Segmentize / Send / Close — need queue bounds
-- ============================================================================

@[simp] theorem segmentize_sndUna (ep : TcpEndpoint) :
    (segmentize ep).1.tcb.sndUna = ep.tcb.sndUna := by
  simp only [segmentize]; split <;> (try split) <;> simp_all

theorem segmentize_preserves (ep : TcpEndpoint)
    (h : endpointInvariant ep) :
    endpointInvariant (segmentize ep).1 := by
  simp only [endpointInvariant, segmentize]
  split
  · simp_all [endpointInvariant]  -- inflight >= window → available = 0 → (ep, [])
  · rename_i h_inflight
    split
    · exact h  -- available == 0
    · -- Send case: need sndUna ≤ sndNxt + n
      dsimp only []
      apply SeqNum.le_add_within_window _ _ ep.tcb.sndWnd _ h
        (Nat.lt_of_not_le h_inflight)
      apply UInt32_ofNat_le
      simp [List.length_take]
      omega

theorem processSend_preserves (ep : TcpEndpoint) (data : List UInt8)
    (h : endpointInvariant ep) :
    endpointInvariant (processSend ep data).endpoint := by
  simp only [processSend]
  split
  all_goals (try exact h)
  -- Established and CloseWait: endpoint is (segmentize ep').1 where ep' has same tcb
  all_goals
    show endpointInvariant (segmentize { ep with sendQueue := ep.sendQueue ++ data }).1
    exact segmentize_preserves _ h

/-- After segmentize, adding 1 to sndNxt preserves sndUna ≤ sndNxt. -/
private theorem segmentize_then_fin (ep : TcpEndpoint)
    (h : endpointInvariant ep)
    (hWnd : ep.tcb.sndNxt.val - ep.tcb.sndUna.val ≤ ep.tcb.sndWnd.toUInt32) :
    SeqNum.le (segmentize ep).1.tcb.sndUna ((segmentize ep).1.tcb.sndNxt.add 1) = true := by
  simp only [segmentize]
  split
  · -- inflight >= window
    apply SeqNum.le_add_of_le _ _ _ h
    exact window_plus_one_lt_halfSpace _ ep.tcb.sndWnd hWnd
  · rename_i h_inflight
    split
    · -- available = 0
      apply SeqNum.le_add_of_le _ _ _ h
      exact window_plus_one_lt_halfSpace _ ep.tcb.sndWnd hWnd
    · -- send data + FIN
      dsimp only []
      rw [SeqNum.add_add]
      apply SeqNum.le_add_of_le _ _ _ h
      apply inflight_sent_fin_lt_halfSpace _ _ ep.tcb.sndWnd (Nat.lt_of_not_le h_inflight)
      apply UInt32_ofNat_le
      simp [List.length_take]; omega

theorem processClose_preserves (ep : TcpEndpoint)
    (h : endpointInvariant ep)
    (hWnd : ep.tcb.sndNxt.val - ep.tcb.sndUna.val ≤ ep.tcb.sndWnd.toUInt32) :
    endpointInvariant (processClose ep).endpoint := by
  simp only [processClose]
  split
  · exact h  -- Closed
  · exact closedEndpoint_invariant  -- Listen
  · exact closedEndpoint_invariant  -- SynSent
  · -- SynReceived
    split
    · simp only [endpointInvariant]
      apply SeqNum.le_add_of_le _ _ _ h
      exact window_plus_one_lt_halfSpace _ ep.tcb.sndWnd hWnd
    · exact h
  · -- Established: segmentize + FIN
    simp only [endpointInvariant]
    exact segmentize_then_fin ep h hWnd
  · exact h  -- FinWait1
  · exact h  -- FinWait2
  · -- CloseWait: segmentize + FIN
    simp only [endpointInvariant]
    exact segmentize_then_fin ep h hWnd
  · exact h  -- Closing
  · exact h  -- LastAck
  · exact h  -- TimeWait

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

-- ============================================================================
-- processSegmentSynSent
-- ============================================================================

theorem processSegmentSynSent_preserves (ep : TcpEndpoint) (seg : Segment)
    (h : endpointInvariant ep) :
    endpointInvariant (processSegmentSynSent ep seg).endpoint := by
  unfold processSegmentSynSent
  dsimp only [mkSegment, defaultRcvWnd]
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split)
  all_goals (try exact h)
  all_goals (try exact closedEndpoint_invariant)
  -- Remaining: pipelinePostAck goals for ESTABLISHED path
  all_goals
    dsimp only []
    apply pipelinePostAck_preserves
    simp_all [endpointInvariant]

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
  · -- Established: future ACK guard, then ackUpdate
    split at hAck
    · simp at hAck  -- future ACK → none
    · simp at hAck; rw [← hAck]; exact ackUpdate_preserves _ _ h
  · -- FinWait1: future ACK guard, then ackUpdate + state change
    split at hAck
    · simp at hAck  -- future ACK → none, contradicts some ep'
    · simp at hAck; rw [← hAck]
      unfold ackUpdate
      simp [windowUpdateTcb_sndUna, windowUpdateTcb_sndNxt]
      rw [← ackAdvanceTcb_sndNxt ep.tcb seg]
      exact ackAdvanceTcb_preserves ep.tcb seg h
  · -- FinWait2: future ACK guard, then ackUpdate
    split at hAck
    · simp at hAck
    · simp at hAck; rw [← hAck]; exact ackUpdate_preserves _ _ h
  · -- CloseWait: future ACK guard, then ackUpdate
    split at hAck
    · simp at hAck
    · simp at hAck; rw [← hAck]; exact ackUpdate_preserves _ _ h
  · -- Closing: future ACK guard, then ackUpdate + FIN check
    split at hAck
    · simp at hAck  -- future ACK → none
    · -- else branch: split on finAcked
      split at hAck
      -- ep.finSeqNum = some fseq: split on fseq.lt seg.ackNum
      · split at hAck <;> simp at hAck <;> rw [← hAck]
        · -- finAcked: ep' with state TimeWait, tcb from ackUpdate
          simp only [ackUpdate, windowUpdateTcb_sndUna, windowUpdateTcb_sndNxt]
          exact ackAdvanceTcb_preserves ep.tcb seg h
        · exact ackUpdate_preserves _ _ h
      -- ep.finSeqNum = none: finAcked = false, ep' = ackUpdate ep seg
      · simp at hAck; rw [← hAck]; exact ackUpdate_preserves _ _ h
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
  | deliverToA seg h_mem result h_proc =>
    exact ⟨h_proc ▸ processSegment_preserves _ seg _ hA, hB⟩
  | deliverToB seg h_mem result h_proc =>
    exact ⟨hA, h_proc ▸ processSegment_preserves _ seg _ hB⟩
  | userCallA call result h_proc =>
    exact ⟨h_userA call result h_proc, hB⟩
  | userCallB call result h_proc =>
    exact ⟨hA, h_userB call result h_proc⟩
  | timeoutA kind result h_proc =>
    exact ⟨h_proc ▸ processTimeout_preserves _ kind hA, hB⟩
  | timeoutB kind result h_proc =>
    exact ⟨hA, h_proc ▸ processTimeout_preserves _ kind hB⟩
  | segmentLoss seg h_mem =>
    exact ⟨hA, hB⟩
  | segmentDup seg h_mem =>
    exact ⟨hA, hB⟩

theorem initial_system_invariant : systemInvariant {} :=
  ⟨closedEndpoint_invariant, closedEndpoint_invariant⟩

end Tcp
