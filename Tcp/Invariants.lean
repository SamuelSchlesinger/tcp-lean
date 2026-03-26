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

/-- Component: `SND.UNA ≤ SND.NXT`. -/
def leInvariant (ep : TcpEndpoint) : Prop :=
  SeqNum.le ep.tcb.sndUna ep.tcb.sndNxt = true

theorem closedEndpoint_leInvariant : leInvariant closedEndpoint := by
  simp [leInvariant, closedEndpoint, SeqNum.le]

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
    (hPre : leInvariant ep) :
    leInvariant (ackUpdate ep seg) := by
  simp only [leInvariant, ackUpdate, windowUpdateTcb_sndUna, windowUpdateTcb_sndNxt]
  exact ackAdvanceTcb_preserves ep.tcb seg hPre

-- ============================================================================
-- Simple function preservation
-- ============================================================================

theorem processOpen_preserves (ep : TcpEndpoint) (mode : OpenMode) (iss : SeqNum)
    (h : leInvariant ep) :
    leInvariant (processOpen ep mode iss).endpoint := by
  simp only [leInvariant, processOpen]
  split
  · split <;> simp [freshTcb, SeqNum.le, lt_add_one]
  · split
    · simp [SeqNum.le, lt_add_one]
    · exact h
  · exact h

theorem processReceive_preserves (ep : TcpEndpoint) (h : leInvariant ep) :
    leInvariant (processReceive ep).endpoint := by
  simp only [leInvariant, processReceive]
  split <;> (try split) <;> simp_all [leInvariant]

theorem processAbort_preserves (ep : TcpEndpoint) (h : leInvariant ep) :
    leInvariant (processAbort ep).endpoint := by
  simp only [leInvariant]
  unfold processAbort
  split <;> (first | exact h | (dsimp only []; simp [closedEndpoint, SeqNum.le]))

theorem processTimeout_preserves (ep : TcpEndpoint) (kind : TimeoutKind)
    (h : leInvariant ep) :
    leInvariant (processTimeout ep kind).endpoint := by
  simp only [leInvariant, processTimeout]
  split
  · simp [closedEndpoint, SeqNum.le]
  · split <;> exact h
  · split
    · simp [closedEndpoint, SeqNum.le]
    · exact h

theorem processSegmentClosed_preserves (ep : TcpEndpoint) (seg : Segment)
    (h : leInvariant ep) :
    leInvariant (processSegmentClosed ep seg).endpoint := by
  simp only [leInvariant, processSegmentClosed]
  split <;> (try split) <;> exact h

theorem processSegmentListen_preserves (ep : TcpEndpoint) (seg : Segment)
    (iss : SeqNum) (h : leInvariant ep) :
    leInvariant (processSegmentListen ep seg iss).endpoint := by
  simp only [leInvariant, processSegmentListen]
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
    (h : leInvariant ep) :
    leInvariant (segmentize ep).1 := by
  simp only [leInvariant, segmentize]
  split
  · simp_all [leInvariant]  -- inflight >= window → available = 0 → (ep, [])
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
    (h : leInvariant ep) :
    leInvariant (processSend ep data).endpoint := by
  simp only [processSend]
  split
  all_goals (try exact h)
  -- Established and CloseWait: endpoint is (segmentize ep').1 where ep' has same tcb
  all_goals
    show leInvariant (segmentize { ep with sendQueue := ep.sendQueue ++ data }).1
    exact segmentize_preserves _ h

/-- After segmentize, adding 1 to sndNxt preserves sndUna ≤ sndNxt. -/
private theorem segmentize_then_fin (ep : TcpEndpoint)
    (h : leInvariant ep)
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
    (h : leInvariant ep)
    (hWnd : ep.tcb.sndNxt.val - ep.tcb.sndUna.val ≤ ep.tcb.sndWnd.toUInt32) :
    leInvariant (processClose ep).endpoint := by
  simp only [processClose]
  split
  · exact h  -- Closed
  · exact closedEndpoint_leInvariant  -- Listen
  · exact closedEndpoint_leInvariant  -- SynSent
  · -- SynReceived
    split
    · simp only [leInvariant]
      apply SeqNum.le_add_of_le _ _ _ h
      exact window_plus_one_lt_halfSpace _ ep.tcb.sndWnd hWnd
    · exact h
  · -- Established: segmentize + FIN
    simp only [leInvariant]
    exact segmentize_then_fin ep h hWnd
  · exact h  -- FinWait1
  · exact h  -- FinWait2
  · -- CloseWait: segmentize + FIN
    simp only [leInvariant]
    exact segmentize_then_fin ep h hWnd
  · exact h  -- Closing
  · exact h  -- LastAck
  · exact h  -- TimeWait

-- ============================================================================
-- Pipeline preservation
-- ============================================================================

theorem pipelineUrg_preserves (ep : TcpEndpoint) (seg : Segment)
    (h : leInvariant ep) :
    leInvariant (pipelineUrg ep seg) := by
  simp only [leInvariant, pipelineUrg]
  split <;> (try split) <;> simp_all [leInvariant]

theorem pipelineText_preserves (ep : TcpEndpoint) (seg : Segment)
    (h : leInvariant ep) :
    leInvariant (pipelineText ep seg).1 := by
  simp only [leInvariant, pipelineText]
  split <;> (try split) <;> simp_all [leInvariant]

theorem pipelineFin_preserves (ep : TcpEndpoint) (seg : Segment) (needAck : Bool)
    (h : leInvariant ep) :
    leInvariant (pipelineFin ep seg needAck).endpoint := by
  simp only [leInvariant]
  unfold pipelineFin
  dsimp only [mkSegment]
  split <;> (try split) <;> (try split) <;> (try split) <;>
    first | exact h | simp_all

theorem pipelinePostAck_preserves (ep : TcpEndpoint) (seg : Segment)
    (h : leInvariant ep) :
    leInvariant (pipelinePostAck ep seg).endpoint := by
  simp only [pipelinePostAck]
  exact pipelineFin_preserves _ seg _
    (pipelineText_preserves _ seg (pipelineUrg_preserves ep seg h))

-- ============================================================================
-- processSegmentSynSent
-- ============================================================================

theorem processSegmentSynSent_preserves (ep : TcpEndpoint) (seg : Segment)
    (h : leInvariant ep) :
    leInvariant (processSegmentSynSent ep seg).endpoint := by
  unfold processSegmentSynSent
  dsimp only [mkSegment, defaultRcvWnd]
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split)
  all_goals (try exact h)
  all_goals (try exact closedEndpoint_leInvariant)
  -- Remaining: pipelinePostAck goals for ESTABLISHED path
  all_goals
    dsimp only []
    apply pipelinePostAck_preserves
    simp_all [leInvariant]

theorem pipelinePreAck_preserves (ep : TcpEndpoint) (seg : Segment)
    (h : leInvariant ep) (result : ProcessResult)
    (hPre : pipelinePreAck ep seg = some result) :
    leInvariant result.endpoint := by
  simp only [leInvariant]
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
    (h : leInvariant ep) (ep' : TcpEndpoint)
    (hAck : pipelineAck ep seg = some ep') :
    leInvariant ep' := by
  simp only [leInvariant]
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
    (h : leInvariant ep) :
    leInvariant (pipelineAckReject ep seg).endpoint := by
  simp only [leInvariant]
  unfold pipelineAckReject; dsimp only [mkSegment]
  split <;> exact h

-- ============================================================================
-- Composed pipeline / segment processing
-- ============================================================================

theorem processSegmentOtherwise_preserves (ep : TcpEndpoint) (seg : Segment)
    (h : leInvariant ep) :
    leInvariant (processSegmentOtherwise ep seg).endpoint := by
  simp only [processSegmentOtherwise]
  split
  · rename_i result hPre
    exact pipelinePreAck_preserves ep seg h result hPre
  · split
    · exact pipelineAckReject_preserves ep seg h
    · rename_i ep' hA
      exact pipelinePostAck_preserves ep' seg (pipelineAck_preserves ep seg h ep' hA)

theorem processSegment_preserves (ep : TcpEndpoint) (seg : Segment)
    (iss : SeqNum) (h : leInvariant ep) :
    leInvariant (processSegment ep seg iss).endpoint := by
  simp only [processSegment]
  split
  · exact processSegmentClosed_preserves ep seg h
  · exact processSegmentListen_preserves ep seg iss h
  · exact processSegmentSynSent_preserves ep seg h
  · exact processSegmentOtherwise_preserves ep seg h

-- ============================================================================
-- Window Invariant — inflight bytes bounded within half-space
-- ============================================================================

/-- The window invariant bounds inflight bytes with room for future advances.
    Pre-FIN states (where processClose may still send a FIN) need room for +2;
    post-FIN states (after FIN sent) need room for +1 only.
    Combined with `leInvariant`, this removes the `hWnd` hypothesis
    from `processClose_preserves`. -/
def windowInvariant (ep : TcpEndpoint) : Prop :=
  match ep.state with
  | .FinWait1 | .FinWait2 | .Closing | .LastAck | .TimeWait =>
    ep.tcb.sndNxt.val - ep.tcb.sndUna.val + 1 < SeqNum.halfSpace
  | _ =>
    ep.tcb.sndNxt.val - ep.tcb.sndUna.val + 2 < SeqNum.halfSpace

/-- In SYN-SENT, sndUna = iss (set by processOpen). This structural invariant
    is needed for the SYN-SENT → ESTABLISHED transition proof. -/
def issInvariant (ep : TcpEndpoint) : Prop :=
  ep.state = .SynSent → ep.tcb.sndUna = ep.tcb.iss

/-- The combined per-endpoint invariant: le + window + ISS. -/
def endpointInvariant (ep : TcpEndpoint) : Prop :=
  leInvariant ep ∧ windowInvariant ep ∧ issInvariant ep

def systemInvariant (s : System) : Prop :=
  endpointInvariant s.endpointA ∧ endpointInvariant s.endpointB

theorem closedEndpoint_invariant : endpointInvariant closedEndpoint := by
  refine ⟨?_, ?_, ?_⟩
  · simp [leInvariant, closedEndpoint, SeqNum.le]
  · simp [windowInvariant, closedEndpoint, SeqNum.halfSpace]
  · intro h; simp [closedEndpoint] at h

theorem closedEndpoint_windowInvariant : windowInvariant closedEndpoint := by
  simp [windowInvariant, closedEndpoint, SeqNum.halfSpace]

-- ============================================================================
-- Window Invariant: helper lemmas
-- ============================================================================

/-- Modular rearrangement: (a + n) - b + K = (a - b) + n + K in UInt32. -/
private theorem uint32_add_sub_rearrange (a b n K : UInt32) :
    (a + n) - b + K = (a - b) + n + K := by
  apply UInt32.eq_of_toBitVec_eq
  simp only [UInt32.toBitVec_add, UInt32.toBitVec_sub]
  bv_omega

/-- If `le una nxt` and `nxt - una + 2 < halfSpace`, then `le una (nxt + 1)`. -/
theorem SeqNum.le_add_one_of_room (una nxt : SeqNum)
    (hLE : SeqNum.le una nxt = true)
    (hRoom : nxt.val - una.val + 2 < SeqNum.halfSpace) :
    SeqNum.le una (nxt.add 1) = true := by
  simp only [SeqNum.le, SeqNum.lt, SeqNum.add, SeqNum.halfSpace,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at *
  bv_decide

/-- Window-bounded data: inflight + n + K < halfSpace when n fits in window. -/
private theorem segmentize_data_bound (inflight : UInt32) (w : UInt16) (n K : UInt32)
    (hLt : inflight < w.toUInt32) (hN : n ≤ w.toUInt32 - inflight)
    (hK : K ≤ 2) :
    inflight + n + K < SeqNum.halfSpace := by
  simp only [SeqNum.halfSpace]; bv_decide

/-- ackAdvanceTcb preserves window bound (K=2). -/
private theorem ackAdvanceTcb_preserves_window_2 (tcb : Tcb) (seg : Segment)
    (hLE : SeqNum.le tcb.sndUna tcb.sndNxt = true)
    (hw : tcb.sndNxt.val - tcb.sndUna.val + 2 < SeqNum.halfSpace) :
    (ackAdvanceTcb tcb seg).sndNxt.val - (ackAdvanceTcb tcb seg).sndUna.val + 2
      < SeqNum.halfSpace := by
  simp only [ackAdvanceTcb]; split
  · rename_i hCond; simp only [Bool.and_eq_true, SeqNum.lt, SeqNum.le, SeqNum.halfSpace,
      Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at *; bv_decide
  · exact hw

/-- ackAdvanceTcb preserves window bound (K=1). -/
private theorem ackAdvanceTcb_preserves_window_1 (tcb : Tcb) (seg : Segment)
    (hLE : SeqNum.le tcb.sndUna tcb.sndNxt = true)
    (hw : tcb.sndNxt.val - tcb.sndUna.val + 1 < SeqNum.halfSpace) :
    (ackAdvanceTcb tcb seg).sndNxt.val - (ackAdvanceTcb tcb seg).sndUna.val + 1
      < SeqNum.halfSpace := by
  simp only [ackAdvanceTcb]; split
  · rename_i hCond; simp only [Bool.and_eq_true, SeqNum.lt, SeqNum.le, SeqNum.halfSpace,
      Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at *; bv_decide
  · exact hw

/-- SynReceived ACK bound: inflight decreases after ACK advance. -/
private theorem inflight_decreases_le_2 (sndUna ack sndNxt : UInt32)
    (hLE : SeqNum.le ⟨sndUna⟩ ⟨sndNxt⟩ = true)
    (hAck : SeqNum.le ⟨sndUna⟩ ⟨ack⟩ && SeqNum.le ⟨ack⟩ ⟨sndNxt⟩ = true)
    (hRoom : sndNxt - sndUna + 2 < SeqNum.halfSpace) :
    sndNxt - ack + 2 < SeqNum.halfSpace := by
  simp only [SeqNum.lt, SeqNum.le, SeqNum.halfSpace, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at *; bv_decide

-- ============================================================================
-- Window Invariant: simp lemmas for pipeline projections
-- ============================================================================

@[simp] theorem pipelineUrg_sndNxt (ep : TcpEndpoint) (seg : Segment) :
    (pipelineUrg ep seg).tcb.sndNxt = ep.tcb.sndNxt := by
  simp only [pipelineUrg]; split <;> (try split) <;> simp_all

@[simp] theorem pipelineUrg_sndUna (ep : TcpEndpoint) (seg : Segment) :
    (pipelineUrg ep seg).tcb.sndUna = ep.tcb.sndUna := by
  simp only [pipelineUrg]; split <;> (try split) <;> simp_all

@[simp] theorem pipelineText_sndNxt (ep : TcpEndpoint) (seg : Segment) :
    (pipelineText ep seg).1.tcb.sndNxt = ep.tcb.sndNxt := by
  simp only [pipelineText]; split <;> (try split) <;> simp_all

@[simp] theorem pipelineText_sndUna (ep : TcpEndpoint) (seg : Segment) :
    (pipelineText ep seg).1.tcb.sndUna = ep.tcb.sndUna := by
  simp only [pipelineText]; split <;> (try split) <;> simp_all

@[simp] theorem segmentize_state (ep : TcpEndpoint) :
    (segmentize ep).1.state = ep.state := by
  simp only [segmentize]; split <;> (try split) <;> simp_all

@[simp] theorem ackUpdate_state (ep : TcpEndpoint) (seg : Segment) :
    (ackUpdate ep seg).state = ep.state := by
  simp only [ackUpdate]

-- ============================================================================
-- Key helper: segmentize bound (after sndUna rewrite)
-- ============================================================================

/-- After segmentize, the inflight+K bound is preserved. -/
private theorem segmentize_bound' (ep : TcpEndpoint) (K : UInt32) (hK : K ≤ 2)
    (hw : ep.tcb.sndNxt.val - ep.tcb.sndUna.val + K < SeqNum.halfSpace) :
    (segmentize ep).1.tcb.sndNxt.val - ep.tcb.sndUna.val + K < SeqNum.halfSpace := by
  have h : (segmentize ep).1.tcb.sndUna = ep.tcb.sndUna := segmentize_sndUna ep
  rw [← h]
  simp only [segmentize]
  split
  · exact hw
  · rename_i h_inflight
    split
    · exact hw
    · dsimp only [SeqNum.add]
      rw [uint32_add_sub_rearrange]
      exact segmentize_data_bound _ ep.tcb.sndWnd _ _
        (Nat.lt_of_not_le h_inflight)
        (UInt32_ofNat_le _ _ (by simp [List.length_take]; omega))
        hK

-- ============================================================================
-- Window Invariant transfer helper
-- ============================================================================

/-- windowInvariant transfers when state, sndNxt, sndUna are unchanged. -/
private theorem windowInvariant_of_same_fields (ep ep' : TcpEndpoint)
    (hState : ep'.state = ep.state)
    (hNxt : ep'.tcb.sndNxt = ep.tcb.sndNxt)
    (hUna : ep'.tcb.sndUna = ep.tcb.sndUna)
    (hw : windowInvariant ep) :
    windowInvariant ep' := by
  simp only [windowInvariant] at *; rw [hState, hNxt, hUna]; exact hw

-- ============================================================================
-- Window Invariant: per-function preservation
-- ============================================================================

theorem processOpen_preserves_window (ep : TcpEndpoint) (mode : OpenMode) (iss : SeqNum)
    (hw : windowInvariant ep) :
    windowInvariant (processOpen ep mode iss).endpoint := by
  simp only [processOpen]
  split
  · split
    · simp [windowInvariant, freshTcb, SeqNum.halfSpace]
    · -- Active: SynSent
      simp only [windowInvariant, freshTcb, SeqNum.add, SeqNum.halfSpace]
      show (iss.val + 1) - iss.val + 2 < 2147483648
      rw [UInt32.add_sub_self]; simp
  · split
    · -- Listen → SynSent (Active)
      simp only [windowInvariant, SeqNum.add, SeqNum.halfSpace]
      show (iss.val + 1) - iss.val + 2 < 2147483648
      rw [UInt32.add_sub_self]; simp
    · exact hw
  · exact hw

theorem processReceive_preserves_window (ep : TcpEndpoint)
    (hw : windowInvariant ep) :
    windowInvariant (processReceive ep).endpoint := by
  simp only [processReceive]
  split <;> (try split) <;> (first
    | exact hw
    | (apply windowInvariant_of_same_fields ep <;> (first | rfl | simp_all)))

theorem processAbort_preserves_window (ep : TcpEndpoint)
    (hw : windowInvariant ep) :
    windowInvariant (processAbort ep).endpoint := by
  unfold processAbort; dsimp only [mkSegment]
  split <;> (first | exact hw | exact closedEndpoint_windowInvariant)

theorem processTimeout_preserves_window (ep : TcpEndpoint) (kind : TimeoutKind)
    (hw : windowInvariant ep) :
    windowInvariant (processTimeout ep kind).endpoint := by
  simp only [processTimeout]
  split
  · exact closedEndpoint_windowInvariant
  · split <;> exact hw
  · split
    · exact closedEndpoint_windowInvariant
    · exact hw

theorem processSegmentClosed_preserves_window (ep : TcpEndpoint) (seg : Segment)
    (hw : windowInvariant ep) :
    windowInvariant (processSegmentClosed ep seg).endpoint := by
  simp only [processSegmentClosed]
  split <;> (try split) <;> exact hw

theorem processSegmentListen_preserves_window (ep : TcpEndpoint) (seg : Segment)
    (iss : SeqNum) (hw : windowInvariant ep) :
    windowInvariant (processSegmentListen ep seg iss).endpoint := by
  simp only [processSegmentListen]
  split
  · exact hw
  · split
    · exact hw
    · split
      · simp only [windowInvariant, SeqNum.add, SeqNum.halfSpace]
        show (iss.val + 1) - iss.val + 2 < 2147483648
        rw [UInt32.add_sub_self]; simp
      · exact hw

@[simp] theorem segmentize_iss (ep : TcpEndpoint) :
    (segmentize ep).1.tcb.iss = ep.tcb.iss := by
  simp only [segmentize]; split <;> (try split) <;> simp_all

theorem segmentize_preserves_window (ep : TcpEndpoint)
    (hw : windowInvariant ep) :
    windowInvariant (segmentize ep).1 := by
  unfold windowInvariant
  rw [segmentize_state, segmentize_sndUna]
  cases hState : ep.state <;> simp only [windowInvariant, hState] at hw ⊢ <;>
    (first
      | exact segmentize_bound' ep 2 (by decide) hw
      | exact segmentize_bound' ep 1 (by decide) hw)

theorem processSend_preserves_window (ep : TcpEndpoint) (data : List UInt8)
    (hw : windowInvariant ep) :
    windowInvariant (processSend ep data).endpoint := by
  simp only [processSend]
  split
  all_goals (try exact hw)
  all_goals
    show windowInvariant (segmentize { ep with sendQueue := ep.sendQueue ++ data }).1
    exact segmentize_preserves_window _ hw

-- ============================================================================
-- processClose: segmentize + FIN helpers
-- ============================================================================

/-- After segmentize, adding 1 to sndNxt preserves sndUna ≤ sndNxt
    (using windowInvariant to provide the room bound). -/
private theorem segmentize_then_fin' (ep : TcpEndpoint)
    (h : leInvariant ep)
    (hw2 : ep.tcb.sndNxt.val - ep.tcb.sndUna.val + 2 < SeqNum.halfSpace) :
    SeqNum.le (segmentize ep).1.tcb.sndUna ((segmentize ep).1.tcb.sndNxt.add 1) = true := by
  exact SeqNum.le_add_one_of_room _ _ (segmentize_preserves _ h)
    (by rw [segmentize_sndUna]; exact segmentize_bound' ep 2 (by decide) hw2)

/-- Window invariant for the post-FIN endpoint after segmentize + FIN.
    (sndNxt + 1) - sndUna + 1 = (sndNxt - sndUna) + 2 < halfSpace. -/
private theorem segmentize_then_fin_window (ep : TcpEndpoint)
    (hw2 : ep.tcb.sndNxt.val - ep.tcb.sndUna.val + 2 < SeqNum.halfSpace) :
    ((segmentize ep).1.tcb.sndNxt.add 1).val - (segmentize ep).1.tcb.sndUna.val + 1
      < SeqNum.halfSpace := by
  rw [segmentize_sndUna]
  simp only [SeqNum.add]
  rw [uint32_add_sub_rearrange]
  have h12 : ∀ (x : UInt32), x + 1 + 1 = x + 2 := by
    intro x; apply UInt32.eq_of_toBitVec_eq
    simp [UInt32.toBitVec_add]; bv_omega
  rw [h12]
  exact segmentize_bound' ep 2 (by decide) hw2

theorem processClose_preserves_window (ep : TcpEndpoint)
    (h : leInvariant ep)
    (hw : windowInvariant ep) :
    windowInvariant (processClose ep).endpoint := by
  simp only [processClose]
  split
  · exact hw  -- Closed
  · exact closedEndpoint_windowInvariant  -- Listen
  · exact closedEndpoint_windowInvariant  -- SynSent
  · -- SynReceived → FinWait1 (post-FIN)
    split
    · -- (sndNxt + 1) - sndUna + 1 = inflight + 2 < halfSpace
      simp only [windowInvariant, SeqNum.add]
      -- ep.state = SynReceived (pre-FIN), so hw gives +2 bound
      -- Need: (sndNxt + 1) - sndUna + 1 < halfSpace
      -- = inflight + 2 < halfSpace (from hw)
      have hw2 : ep.tcb.sndNxt.val - ep.tcb.sndUna.val + 2 < SeqNum.halfSpace := by
        simp only [windowInvariant, ‹ep.state = _›] at hw; exact hw
      simp only [SeqNum.halfSpace] at *; bv_decide
    · exact hw
  · -- Established → FinWait1: segmentize + FIN
    simp only [windowInvariant]
    exact segmentize_then_fin_window ep (by simp only [windowInvariant, ‹ep.state = _›] at hw; exact hw)
  · exact hw  -- FinWait1
  · exact hw  -- FinWait2
  · -- CloseWait → LastAck: segmentize + FIN
    simp only [windowInvariant]
    exact segmentize_then_fin_window ep (by simp only [windowInvariant, ‹ep.state = _›] at hw; exact hw)
  · exact hw  -- Closing
  · exact hw  -- LastAck
  · exact hw  -- TimeWait

/-- processClose preserves leInvariant (without hWnd hypothesis). -/
theorem processClose_preserves' (ep : TcpEndpoint)
    (h : leInvariant ep)
    (hw : windowInvariant ep) :
    leInvariant (processClose ep).endpoint := by
  simp only [processClose]
  split
  · exact h
  · exact closedEndpoint_leInvariant
  · exact closedEndpoint_leInvariant
  · split
    · simp only [leInvariant]
      exact SeqNum.le_add_one_of_room _ _ h
        (by simp only [windowInvariant, ‹ep.state = _›] at hw; exact hw)
    · exact h
  · simp only [leInvariant]
    exact segmentize_then_fin' ep h (by simp only [windowInvariant, ‹ep.state = _›] at hw; exact hw)
  · exact h
  · exact h
  · simp only [leInvariant]
    exact segmentize_then_fin' ep h (by simp only [windowInvariant, ‹ep.state = _›] at hw; exact hw)
  · exact h
  · exact h
  · exact h

-- ============================================================================
-- Window Invariant: pipeline preservation
-- ============================================================================

@[simp] theorem pipelineUrg_iss (ep : TcpEndpoint) (seg : Segment) :
    (pipelineUrg ep seg).tcb.iss = ep.tcb.iss := by
  simp only [pipelineUrg]; split <;> (try split) <;> simp_all

@[simp] theorem pipelineText_iss (ep : TcpEndpoint) (seg : Segment) :
    (pipelineText ep seg).1.tcb.iss = ep.tcb.iss := by
  simp only [pipelineText]; split <;> (try split) <;> simp_all

theorem pipelineUrg_preserves_window (ep : TcpEndpoint) (seg : Segment)
    (hw : windowInvariant ep) :
    windowInvariant (pipelineUrg ep seg) := by
  exact windowInvariant_of_same_fields ep _
    (pipelineUrg_state ep seg) (pipelineUrg_sndNxt ep seg)
    (pipelineUrg_sndUna ep seg) hw

theorem pipelineText_preserves_window (ep : TcpEndpoint) (seg : Segment)
    (hw : windowInvariant ep) :
    windowInvariant (pipelineText ep seg).1 := by
  exact windowInvariant_of_same_fields ep _
    (pipelineText_state ep seg) (pipelineText_sndNxt ep seg)
    (pipelineText_sndUna ep seg) hw

theorem pipelineFin_preserves_window (ep : TcpEndpoint) (seg : Segment) (needAck : Bool)
    (hw : windowInvariant ep) :
    windowInvariant (pipelineFin ep seg needAck).endpoint := by
  -- pipelineFin doesn't change sndNxt/sndUna.
  -- All state transitions stay in same bound category (pre→pre or post→post).
  cases hState : ep.state <;> (
    unfold pipelineFin; dsimp only [mkSegment]; simp only [hState]
    split <;> (try split) <;> (try split) <;> (try split)
    all_goals (first
      | exact hw  -- endpoint unchanged
      | (dsimp only []; simp only [windowInvariant, hState] at hw;
         simp only [windowInvariant]; exact hw)  -- state changed but same bound
      | simp at *))

theorem pipelinePostAck_preserves_window (ep : TcpEndpoint) (seg : Segment)
    (hw : windowInvariant ep) :
    windowInvariant (pipelinePostAck ep seg).endpoint := by
  simp only [pipelinePostAck]
  exact pipelineFin_preserves_window _ seg _
    (pipelineText_preserves_window _ seg (pipelineUrg_preserves_window ep seg hw))

-- ackUpdate preserves window invariant
theorem ackUpdate_preserves_window (ep : TcpEndpoint) (seg : Segment)
    (h : leInvariant ep) (hw : windowInvariant ep) :
    windowInvariant (ackUpdate ep seg) := by
  unfold windowInvariant
  simp only [ackUpdate, windowUpdateTcb_sndUna, windowUpdateTcb_sndNxt]
  cases hState : ep.state <;> simp only [windowInvariant, hState] at hw <;>
    (first | exact ackAdvanceTcb_preserves_window_2 ep.tcb seg h hw
           | exact ackAdvanceTcb_preserves_window_1 ep.tcb seg h hw)

-- pipelinePreAck preserves window invariant
theorem pipelinePreAck_preserves_window (ep : TcpEndpoint) (seg : Segment)
    (hw : windowInvariant ep) (result : ProcessResult)
    (hPre : pipelinePreAck ep seg = some result) :
    windowInvariant result.endpoint := by
  unfold pipelinePreAck at hPre; dsimp only [mkSegment] at hPre
  split at hPre
  · split at hPre <;> simp at hPre <;> rw [← hPre] <;> exact hw
  · split at hPre
    · split at hPre
      · -- SynReceived RST: passive → Listen, active → closedEndpoint
        split at hPre <;> simp at hPre <;> rw [← hPre]
        · -- Listen: same tcb, state Listen (pre-FIN like SynReceived)
          simp only [windowInvariant]
          simp only [windowInvariant, ‹ep.state = _›] at hw; exact hw
        · exact closedEndpoint_windowInvariant
      -- Remaining RST state cases: closedEndpoint or ep
      all_goals (first
        | (simp at hPre; rw [← hPre]; exact closedEndpoint_windowInvariant)
        | (simp at hPre; rw [← hPre]; exact hw))
    · split at hPre
      · simp at hPre; rw [← hPre]; exact closedEndpoint_windowInvariant
      · split at hPre
        · simp at hPre; rw [← hPre]; exact hw
        · simp at hPre

-- pipelineAck preserves window invariant
theorem pipelineAck_preserves_window (ep : TcpEndpoint) (seg : Segment)
    (h : leInvariant ep) (hw : windowInvariant ep) (ep' : TcpEndpoint)
    (hAck : pipelineAck ep seg = some ep') :
    windowInvariant ep' := by
  simp only [pipelineAck] at hAck
  split at hAck
  · -- SynReceived → Established (pre→pre)
    split at hAck
    · simp at hAck; rw [← hAck]
      simp only [windowInvariant]
      have hw2 : ep.tcb.sndNxt.val - ep.tcb.sndUna.val + 2 < SeqNum.halfSpace := by
        simp only [windowInvariant, ‹ep.state = _›] at hw; exact hw
      simp only [leInvariant, SeqNum.le, SeqNum.lt, SeqNum.halfSpace,
        Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
        decide_eq_true_eq] at *; bv_decide
    · simp at hAck
  · -- Established: ackUpdate (pre→pre)
    split at hAck
    · simp at hAck
    · simp at hAck; rw [← hAck]; exact ackUpdate_preserves_window _ _ h hw
  · -- FinWait1: ackUpdate + state change (post→post)
    split at hAck
    · simp at hAck
    · simp at hAck; rw [← hAck]
      -- Result has state = if finAcked then .FinWait2 else .FinWait1 (both post-FIN, +1)
      -- and tcb from ackUpdate. Use ackUpdate_preserves_window then adjust state.
      have hw1 : ep.tcb.sndNxt.val - ep.tcb.sndUna.val + 1 < SeqNum.halfSpace := by
        simp only [windowInvariant, ‹ep.state = _›] at hw; exact hw
      have hBound := ackAdvanceTcb_preserves_window_1 ep.tcb seg h hw1
      -- Result state is if finAcked then FW2 else FW1 (both post-FIN, +1)
      -- Case split on ep.finSeqNum to resolve the inner match, then the if
      cases ep.finSeqNum with
      | some fseq =>
        unfold windowInvariant
        simp only [ackUpdate, windowUpdateTcb_sndNxt, windowUpdateTcb_sndUna]
        simp only [ackAdvanceTcb_sndNxt] at hBound
        split <;> (first | (simp; exact hBound) | simp_all)
      | none =>
        simp only [windowInvariant, ackUpdate, windowUpdateTcb_sndNxt, windowUpdateTcb_sndUna,
          ackAdvanceTcb_sndNxt] at hBound ⊢
        exact hBound
  · -- FinWait2: ackUpdate (post→post)
    split at hAck
    · simp at hAck
    · simp at hAck; rw [← hAck]; exact ackUpdate_preserves_window _ _ h hw
  · -- CloseWait: ackUpdate (pre→pre)
    split at hAck
    · simp at hAck
    · simp at hAck; rw [← hAck]; exact ackUpdate_preserves_window _ _ h hw
  · -- Closing: ackUpdate + FIN check (post→post)
    split at hAck
    · simp at hAck
    · split at hAck
      · split at hAck <;> simp at hAck <;> rw [← hAck]
        · -- TimeWait (post)
          have hw1 : ep.tcb.sndNxt.val - ep.tcb.sndUna.val + 1 < SeqNum.halfSpace := by
            simp only [windowInvariant, ‹ep.state = _›] at hw; exact hw
          simp only [windowInvariant, ackUpdate, windowUpdateTcb_sndUna, windowUpdateTcb_sndNxt]
          exact ackAdvanceTcb_preserves_window_1 ep.tcb seg h hw1
        · exact ackUpdate_preserves_window _ _ h hw
      · simp at hAck; rw [← hAck]; exact ackUpdate_preserves_window _ _ h hw
  · -- LastAck (post)
    split at hAck
    · split at hAck <;> simp at hAck <;> rw [← hAck]
      · exact closedEndpoint_windowInvariant
      · exact hw
    · simp at hAck; rw [← hAck]; exact hw
  · -- TimeWait (post)
    simp at hAck; rw [← hAck]; exact hw
  · -- fallthrough
    simp at hAck; rw [← hAck]; exact hw

-- pipelineAckReject preserves window
theorem pipelineAckReject_preserves_window (ep : TcpEndpoint) (seg : Segment)
    (hw : windowInvariant ep) :
    windowInvariant (pipelineAckReject ep seg).endpoint := by
  unfold pipelineAckReject; dsimp only [mkSegment]
  split <;> exact hw

-- Composed pipeline
theorem processSegmentOtherwise_preserves_window (ep : TcpEndpoint) (seg : Segment)
    (h : leInvariant ep) (hw : windowInvariant ep) :
    windowInvariant (processSegmentOtherwise ep seg).endpoint := by
  simp only [processSegmentOtherwise]
  split
  · rename_i result hPre
    exact pipelinePreAck_preserves_window ep seg hw result hPre
  · split
    · exact pipelineAckReject_preserves_window ep seg hw
    · rename_i ep' hA
      exact pipelinePostAck_preserves_window ep' seg
        (pipelineAck_preserves_window ep seg h hw ep' hA)

-- processSegmentSynSent
theorem processSegmentSynSent_preserves_window (ep : TcpEndpoint) (seg : Segment)
    (h : leInvariant ep) (hw : windowInvariant ep)
    (hState : ep.state = .SynSent)
    (hISS : issInvariant ep) :
    windowInvariant (processSegmentSynSent ep seg).endpoint := by
  have hIss := hISS hState  -- ep.tcb.sndUna = ep.tcb.iss
  unfold processSegmentSynSent; dsimp only [mkSegment, defaultRcvWnd]
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split)
  all_goals (try exact hw)
  all_goals (try exact closedEndpoint_windowInvariant)
  -- Remaining: SynReceived (simultaneous open) and ESTABLISHED (pipelinePostAck)
  all_goals first
    -- SynReceived: same sndNxt/sndUna as ep, state SynReceived (pre-FIN, +2 bound)
    | (simp only [windowInvariant]; simp only [windowInvariant, hState] at hw; exact hw)
    -- ESTABLISHED path: pipelinePostAck on newly established endpoint
    -- Use ISS invariant: sndUna = iss → lt iss ack gives lt sndUna ack
    | (apply pipelinePostAck_preserves_window
       simp only [windowInvariant]
       simp only [windowInvariant, hState] at hw
       simp only [leInvariant, SeqNum.le, SeqNum.lt, SeqNum.halfSpace,
         Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
         decide_eq_true_eq, hIss] at *
       bv_decide)

-- Full segment processing
theorem processSegment_preserves_window (ep : TcpEndpoint) (seg : Segment) (iss : SeqNum)
    (h : leInvariant ep) (hw : windowInvariant ep)
    (hISS : issInvariant ep) :
    windowInvariant (processSegment ep seg iss).endpoint := by
  simp only [processSegment]
  split
  · exact processSegmentClosed_preserves_window ep seg hw
  · exact processSegmentListen_preserves_window ep seg iss hw
  · exact processSegmentSynSent_preserves_window ep seg h hw (by assumption) hISS
  · exact processSegmentOtherwise_preserves_window ep seg h hw

-- ============================================================================
-- ISS Invariant: per-function preservation
-- ============================================================================

theorem closedEndpoint_issInvariant : issInvariant closedEndpoint := by
  intro h; simp [closedEndpoint] at h

/-- Helper: if output state ≠ SynSent, then issInvariant holds vacuously. -/
private theorem issInvariant_of_not_synSent {ep : TcpEndpoint}
    (h : ep.state ≠ .SynSent) : issInvariant ep :=
  fun hState => absurd hState h

theorem processOpen_preserves_iss (ep : TcpEndpoint) (mode : OpenMode) (iss : SeqNum)
    (hISS : issInvariant ep) :
    issInvariant (processOpen ep mode iss).endpoint := by
  unfold issInvariant processOpen
  split
  · split <;> simp [freshTcb]  -- Closed: Passive→Listen(vacuous), Active→SynSent(iss=iss)
  · intro h; cases mode <;> simp_all [issInvariant]  -- Listen
  · intro h; exact hISS h  -- wildcard: ep unchanged

theorem processReceive_preserves_iss (ep : TcpEndpoint)
    (hISS : issInvariant ep) :
    issInvariant (processReceive ep).endpoint := by
  simp only [issInvariant, processReceive]
  split <;> (try split)
  all_goals (first | exact hISS | (intro h; simp at h))

theorem processAbort_preserves_iss (ep : TcpEndpoint)
    (hISS : issInvariant ep) :
    issInvariant (processAbort ep).endpoint := by
  simp only [issInvariant]; unfold processAbort; dsimp only [mkSegment]
  split
  · exact hISS  -- Closed: ep unchanged
  all_goals (intro h; simp [closedEndpoint] at h)  -- all others: closedEndpoint

theorem processTimeout_preserves_iss (ep : TcpEndpoint) (kind : TimeoutKind)
    (hISS : issInvariant ep) :
    issInvariant (processTimeout ep kind).endpoint := by
  simp only [issInvariant, processTimeout]
  split
  · intro h; simp [closedEndpoint] at h  -- UserTimeout
  · split <;> exact hISS  -- Retransmission
  · split
    · intro h; simp [closedEndpoint] at h  -- TimeWait → closedEndpoint
    · exact hISS  -- not TimeWait → unchanged

theorem processSegmentClosed_preserves_iss (ep : TcpEndpoint) (seg : Segment)
    (hISS : issInvariant ep) :
    issInvariant (processSegmentClosed ep seg).endpoint := by
  simp only [issInvariant, processSegmentClosed]
  split <;> (try split) <;> exact hISS

theorem processSegmentListen_preserves_iss (ep : TcpEndpoint) (seg : Segment)
    (iss : SeqNum) (hISS : issInvariant ep) :
    issInvariant (processSegmentListen ep seg iss).endpoint := by
  simp only [issInvariant, processSegmentListen]
  split
  · exact hISS  -- RST, unchanged
  · split
    · exact hISS  -- ACK, unchanged
    · split
      · intro h; simp at h  -- SynReceived, not SynSent
      · exact hISS  -- unchanged

-- Pipeline functions: never produce SynSent, so issInvariant is vacuous
theorem pipelinePreAck_preserves_iss (ep : TcpEndpoint) (seg : Segment)
    (hISS : issInvariant ep) (result : ProcessResult)
    (hPre : pipelinePreAck ep seg = some result) :
    issInvariant result.endpoint := by
  simp only [issInvariant]
  unfold pipelinePreAck at hPre; dsimp only [mkSegment] at hPre
  split at hPre
  · -- acceptability
    split at hPre <;> simp at hPre <;> subst hPre <;> exact hISS
  · split at hPre
    · -- RST
      split at hPre
      · -- SynReceived
        split at hPre <;> simp at hPre <;> subst hPre
        · intro h; simp at h  -- Listen ≠ SynSent
        · intro h; simp [closedEndpoint] at h
      · simp at hPre; subst hPre; intro h; simp [closedEndpoint] at h  -- Est RST
      · simp at hPre; subst hPre; intro h; simp [closedEndpoint] at h  -- FW1
      · simp at hPre; subst hPre; intro h; simp [closedEndpoint] at h  -- FW2
      · simp at hPre; subst hPre; intro h; simp [closedEndpoint] at h  -- CW
      · simp at hPre; subst hPre; intro h; simp [closedEndpoint] at h  -- Closing
      · simp at hPre; subst hPre; intro h; simp [closedEndpoint] at h  -- LA
      · simp at hPre; subst hPre; intro h; simp [closedEndpoint] at h  -- TW
      · simp at hPre; subst hPre; dsimp only []; exact hISS  -- wildcard: ep unchanged
    · -- SYN / ACK check
      split at hPre
      · simp at hPre; subst hPre; intro h; simp [closedEndpoint] at h
      · split at hPre
        · simp at hPre; subst hPre; dsimp only []; exact hISS
        · simp at hPre

theorem pipelineAck_preserves_iss (ep : TcpEndpoint) (seg : Segment)
    (hISS : issInvariant ep)
    (ep' : TcpEndpoint) (hAck : pipelineAck ep seg = some ep') :
    issInvariant ep' := by
  -- pipelineAck handles non-SynSent states. All outputs either have non-SynSent state
  -- (Established, FinWait1/2, TimeWait, closedEndpoint) or are ep unchanged.
  -- In all cases, issInvariant transfers from hISS.
  intro hState
  simp only [pipelineAck] at hAck
  -- Use split at hAck to match on ep.state
  split at hAck
  · -- SynReceived
    split at hAck <;> simp at hAck; subst hAck; simp at hState
  · -- Established
    split at hAck <;> simp at hAck; subst hAck; rw [ackUpdate_state] at hState; simp_all
  · -- FinWait1
    split at hAck
    · simp at hAck  -- None (future ACK)
    · simp at hAck; subst hAck
      -- State is `if finAcked then FW2 else FW1`, neither is SynSent
      revert hState; split <;> (intro h; split at h <;> simp at h)
  · -- FinWait2
    split at hAck <;> simp at hAck; subst hAck; rw [ackUpdate_state] at hState; simp_all
  · -- CloseWait
    split at hAck <;> simp at hAck; subst hAck; rw [ackUpdate_state] at hState; simp_all
  · -- Closing
    split at hAck
    · simp at hAck
    · split at hAck
      · split at hAck <;> simp at hAck <;> (subst hAck; first
          | (rw [ackUpdate_state] at hState; simp_all)
          | simp_all)
      · simp at hAck; subst hAck; rw [ackUpdate_state] at hState; simp_all
  · -- LastAck
    split at hAck
    · split at hAck <;> simp at hAck <;> subst hAck
      · simp [closedEndpoint] at hState
      · exact hISS hState
    · simp at hAck; subst hAck; exact hISS hState
  · -- TimeWait
    simp at hAck; subst hAck; exact hISS hState
  · -- fallthrough
    simp at hAck; subst hAck; exact hISS hState

theorem pipelineAckReject_preserves_iss (ep : TcpEndpoint) (seg : Segment)
    (hISS : issInvariant ep) :
    issInvariant (pipelineAckReject ep seg).endpoint := by
  simp only [issInvariant]; unfold pipelineAckReject; dsimp only [mkSegment]
  split <;> exact hISS

theorem pipelineUrg_preserves_iss (ep : TcpEndpoint) (seg : Segment)
    (hISS : issInvariant ep) :
    issInvariant (pipelineUrg ep seg) := by
  intro hState
  rw [pipelineUrg_state ep seg] at hState
  rw [pipelineUrg_sndUna ep seg, pipelineUrg_iss ep seg]
  exact hISS hState

theorem pipelineText_preserves_iss (ep : TcpEndpoint) (seg : Segment)
    (hISS : issInvariant ep) :
    issInvariant (pipelineText ep seg).1 := by
  intro hState
  rw [pipelineText_state ep seg] at hState
  rw [pipelineText_sndUna ep seg, pipelineText_iss ep seg]
  exact hISS hState

theorem pipelineFin_preserves_iss (ep : TcpEndpoint) (seg : Segment) (needAck : Bool)
    (hISS : issInvariant ep) :
    issInvariant (pipelineFin ep seg needAck).endpoint := by
  simp only [issInvariant]
  -- pipelineFin: if FIN, state changes to non-SynSent; if no FIN, ep unchanged.
  -- For SynSent inputs, the endpoint may keep SynSent state but preserves sndUna/iss.
  intro hState
  unfold pipelineFin at hState ⊢; dsimp only [mkSegment] at hState ⊢
  split at hState <;> (try split at hState) <;> (try split at hState) <;>
    (try split at hState) <;> (try split at hState)
  all_goals (first
    | exact hISS hState  -- unchanged ep or SynSent preserved
    | (exfalso; exact absurd hState (by decide))  -- non-SynSent output states
    | simp_all [issInvariant])

theorem pipelinePostAck_preserves_iss (ep : TcpEndpoint) (seg : Segment)
    (hISS : issInvariant ep) :
    issInvariant (pipelinePostAck ep seg).endpoint := by
  simp only [pipelinePostAck]
  exact pipelineFin_preserves_iss _ seg _
    (pipelineText_preserves_iss _ seg (pipelineUrg_preserves_iss ep seg hISS))

-- processSegmentSynSent: stays as ep or transitions to non-SynSent
theorem processSegmentSynSent_preserves_iss (ep : TcpEndpoint) (seg : Segment)
    (hISS : issInvariant ep) :
    issInvariant (processSegmentSynSent ep seg).endpoint := by
  simp only [issInvariant]
  unfold processSegmentSynSent; dsimp only [mkSegment, defaultRcvWnd]
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
    (try split) <;> (try split)
  -- Most goals: either ep unchanged or concrete non-SynSent state
  any_goals exact hISS
  any_goals (intro h; simp [closedEndpoint] at h)
  -- Remaining: pipelinePostAck on Established (h already introduced)
  all_goals exact (pipelinePostAck_preserves_iss _ seg (fun h' => absurd h' (by simp))) h

theorem processSegmentOtherwise_preserves_iss (ep : TcpEndpoint) (seg : Segment)
    (hISS : issInvariant ep) :
    issInvariant (processSegmentOtherwise ep seg).endpoint := by
  simp only [processSegmentOtherwise]
  split
  · rename_i result hPre
    exact pipelinePreAck_preserves_iss ep seg hISS result hPre
  · split
    · exact pipelineAckReject_preserves_iss ep seg hISS
    · rename_i ep' hA
      exact pipelinePostAck_preserves_iss ep' seg
        (pipelineAck_preserves_iss ep seg hISS ep' hA)

theorem processSegment_preserves_iss (ep : TcpEndpoint) (seg : Segment)
    (iss : SeqNum) (hISS : issInvariant ep) :
    issInvariant (processSegment ep seg iss).endpoint := by
  simp only [processSegment]
  split
  · exact processSegmentClosed_preserves_iss ep seg hISS
  · exact processSegmentListen_preserves_iss ep seg iss hISS
  · exact processSegmentSynSent_preserves_iss ep seg hISS
  · exact processSegmentOtherwise_preserves_iss ep seg hISS

theorem segmentize_preserves_iss (ep : TcpEndpoint)
    (hISS : issInvariant ep) :
    issInvariant (segmentize ep).1 := by
  intro hState
  rw [segmentize_state] at hState
  rw [segmentize_sndUna, segmentize_iss]
  exact hISS hState

theorem processSend_preserves_iss (ep : TcpEndpoint) (data : List UInt8)
    (hISS : issInvariant ep) :
    issInvariant (processSend ep data).endpoint := by
  simp only [issInvariant, processSend]
  split
  all_goals (first
    | exact hISS  -- unchanged ep
    | (show issInvariant (segmentize _).1
       exact segmentize_preserves_iss _ hISS)
    | (intro h; simp at h))

theorem processClose_preserves_iss (ep : TcpEndpoint)
    (hISS : issInvariant ep) :
    issInvariant (processClose ep).endpoint := by
  simp only [issInvariant, processClose]
  split
  · exact hISS  -- Closed
  · intro h; simp [closedEndpoint] at h  -- Listen → closedEndpoint
  · intro h; simp [closedEndpoint] at h  -- SynSent → closedEndpoint
  · split  -- SynReceived
    · intro h; simp at h  -- FinWait1
    · exact hISS  -- unchanged
  · intro h; simp at h  -- Established → FinWait1
  · exact hISS  -- FinWait1
  · exact hISS  -- FinWait2
  · intro h; simp at h  -- CloseWait → LastAck
  · exact hISS  -- Closing
  · exact hISS  -- LastAck
  · exact hISS  -- TimeWait

-- ============================================================================
-- Combined endpointInvariant: per-function preservation
-- ============================================================================

theorem processOpen_preserves_combined (ep : TcpEndpoint) (mode : OpenMode) (iss : SeqNum)
    (h : endpointInvariant ep) :
    endpointInvariant (processOpen ep mode iss).endpoint := by
  obtain ⟨hLE, hW, hI⟩ := h
  exact ⟨processOpen_preserves ep mode iss hLE,
         processOpen_preserves_window ep mode iss hW,
         processOpen_preserves_iss ep mode iss hI⟩

theorem processReceive_preserves_combined (ep : TcpEndpoint) (h : endpointInvariant ep) :
    endpointInvariant (processReceive ep).endpoint := by
  obtain ⟨hLE, hW, hI⟩ := h
  exact ⟨processReceive_preserves ep hLE,
         processReceive_preserves_window ep hW,
         processReceive_preserves_iss ep hI⟩

theorem processSend_preserves_combined (ep : TcpEndpoint) (data : List UInt8)
    (h : endpointInvariant ep) :
    endpointInvariant (processSend ep data).endpoint := by
  obtain ⟨hLE, hW, hI⟩ := h
  exact ⟨processSend_preserves ep data hLE,
         processSend_preserves_window ep data hW,
         processSend_preserves_iss ep data hI⟩

theorem processClose_preserves_combined (ep : TcpEndpoint)
    (h : endpointInvariant ep) :
    endpointInvariant (processClose ep).endpoint := by
  obtain ⟨hLE, hW, hI⟩ := h
  exact ⟨processClose_preserves' ep hLE hW,
         processClose_preserves_window ep hLE hW,
         processClose_preserves_iss ep hI⟩

theorem processAbort_preserves_combined (ep : TcpEndpoint)
    (h : endpointInvariant ep) :
    endpointInvariant (processAbort ep).endpoint := by
  obtain ⟨hLE, hW, hI⟩ := h
  exact ⟨processAbort_preserves ep hLE,
         processAbort_preserves_window ep hW,
         processAbort_preserves_iss ep hI⟩

theorem processUserCall_preserves (ep : TcpEndpoint) (call : UserCall)
    (h : endpointInvariant ep) :
    endpointInvariant (processUserCall ep call).endpoint := by
  simp only [processUserCall]
  cases call with
  | Open mode iss => exact processOpen_preserves_combined ep mode iss h
  | Send data => exact processSend_preserves_combined ep data h
  | Receive => exact processReceive_preserves_combined ep h
  | Close => exact processClose_preserves_combined ep h
  | Abort => exact processAbort_preserves_combined ep h
  | Status => exact h

theorem processTimeout_preserves_combined (ep : TcpEndpoint) (kind : TimeoutKind)
    (h : endpointInvariant ep) :
    endpointInvariant (processTimeout ep kind).endpoint := by
  obtain ⟨hLE, hW, hI⟩ := h
  exact ⟨processTimeout_preserves ep kind hLE,
         processTimeout_preserves_window ep kind hW,
         processTimeout_preserves_iss ep kind hI⟩

theorem processSegment_preserves_combined (ep : TcpEndpoint) (seg : Segment)
    (iss : SeqNum) (h : endpointInvariant ep) :
    endpointInvariant (processSegment ep seg iss).endpoint := by
  obtain ⟨hLE, hW, hI⟩ := h
  exact ⟨processSegment_preserves ep seg iss hLE,
         processSegment_preserves_window ep seg iss hLE hW hI,
         processSegment_preserves_iss ep seg iss hI⟩

-- ============================================================================
-- SystemStep Invariant
-- ============================================================================

/-- The system invariant is preserved by every `SystemStep` transition.
    This is now fully unconditional — no blanket hypotheses needed. -/
theorem systemStep_preserves_invariant (s s' : System)
    (hStep : SystemStep s s') (hInv : systemInvariant s) :
    systemInvariant s' := by
  obtain ⟨hA, hB⟩ := hInv
  cases hStep with
  | deliverToA seg h_mem result h_proc =>
    exact ⟨h_proc ▸ processSegment_preserves_combined _ seg _ hA, hB⟩
  | deliverToB seg h_mem result h_proc =>
    exact ⟨hA, h_proc ▸ processSegment_preserves_combined _ seg _ hB⟩
  | userCallA call result h_proc =>
    exact ⟨h_proc ▸ processUserCall_preserves _ call hA, hB⟩
  | userCallB call result h_proc =>
    exact ⟨hA, h_proc ▸ processUserCall_preserves _ call hB⟩
  | timeoutA kind result h_proc =>
    exact ⟨h_proc ▸ processTimeout_preserves_combined _ kind hA, hB⟩
  | timeoutB kind result h_proc =>
    exact ⟨hA, h_proc ▸ processTimeout_preserves_combined _ kind hB⟩
  | segmentLoss seg h_mem =>
    exact ⟨hA, hB⟩
  | segmentDup seg h_mem =>
    exact ⟨hA, hB⟩

theorem initial_system_invariant : systemInvariant {} :=
  ⟨closedEndpoint_invariant, closedEndpoint_invariant⟩

-- ============================================================================
-- SND.UNA Monotonicity (Checklist 2.3)
-- ============================================================================

/-- ackAdvanceTcb either advances sndUna or keeps it: monotone. -/
theorem ackAdvanceTcb_sndUna_monotone (tcb : Tcb) (seg : Segment) :
    SeqNum.le tcb.sndUna (ackAdvanceTcb tcb seg).sndUna = true := by
  simp only [ackAdvanceTcb]
  split
  · rename_i hCond
    simp only [Bool.and_eq_true, SeqNum.le, SeqNum.lt, SeqNum.halfSpace,
      Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at *
    bv_decide
  · exact SeqNum.le_refl _

/-- windowUpdateTcb doesn't change sndUna. -/
theorem windowUpdateTcb_sndUna_eq (tcb : Tcb) (seg : Segment) :
    (windowUpdateTcb tcb seg).sndUna = tcb.sndUna :=
  windowUpdateTcb_sndUna tcb seg

/-- ackUpdate is monotone in sndUna. -/
theorem ackUpdate_sndUna_monotone (ep : TcpEndpoint) (seg : Segment) :
    SeqNum.le ep.tcb.sndUna (ackUpdate ep seg).tcb.sndUna = true := by
  simp only [ackUpdate, windowUpdateTcb_sndUna]
  exact ackAdvanceTcb_sndUna_monotone ep.tcb seg

/-- pipelineUrg doesn't change sndUna (already have simp lemma, this wraps it as le). -/
theorem pipelineUrg_sndUna_monotone (ep : TcpEndpoint) (seg : Segment) :
    SeqNum.le ep.tcb.sndUna (pipelineUrg ep seg).tcb.sndUna = true := by
  rw [pipelineUrg_sndUna]; exact SeqNum.le_refl _

/-- pipelineText doesn't change sndUna. -/
theorem pipelineText_sndUna_monotone (ep : TcpEndpoint) (seg : Segment) :
    SeqNum.le ep.tcb.sndUna (pipelineText ep seg).1.tcb.sndUna = true := by
  rw [pipelineText_sndUna]; exact SeqNum.le_refl _

/-- pipelineFin doesn't change sndUna. -/
@[simp] theorem pipelineFin_sndUna (ep : TcpEndpoint) (seg : Segment) (needAck : Bool) :
    (pipelineFin ep seg needAck).endpoint.tcb.sndUna = ep.tcb.sndUna := by
  unfold pipelineFin; dsimp only [mkSegment]
  split
  · split <;> (try split) <;> (try split) <;> simp_all
  · split <;> simp_all

theorem pipelineFin_sndUna_monotone (ep : TcpEndpoint) (seg : Segment) (needAck : Bool) :
    SeqNum.le ep.tcb.sndUna (pipelineFin ep seg needAck).endpoint.tcb.sndUna = true := by
  rw [pipelineFin_sndUna]; exact SeqNum.le_refl _

/-- pipelinePostAck doesn't change sndUna. -/
@[simp] theorem pipelinePostAck_sndUna (ep : TcpEndpoint) (seg : Segment) :
    (pipelinePostAck ep seg).endpoint.tcb.sndUna = ep.tcb.sndUna := by
  simp only [pipelinePostAck, pipelineFin_sndUna, pipelineText_sndUna, pipelineUrg_sndUna]

theorem pipelinePostAck_sndUna_monotone (ep : TcpEndpoint) (seg : Segment) :
    SeqNum.le ep.tcb.sndUna (pipelinePostAck ep seg).endpoint.tcb.sndUna = true := by
  rw [pipelinePostAck_sndUna]; exact SeqNum.le_refl _

/-- pipelineAck is monotone in sndUna, or transitions to Closed with sndUna = 0. -/
theorem pipelineAck_sndUna_monotone (ep : TcpEndpoint) (seg : Segment)
    (ep' : TcpEndpoint) (hAck : pipelineAck ep seg = some ep') :
    SeqNum.le ep.tcb.sndUna ep'.tcb.sndUna = true ∨ (ep'.state = .Closed ∧ ep'.tcb.sndUna = ⟨0⟩) := by
  simp only [pipelineAck] at hAck
  split at hAck
  · -- SynReceived
    split at hAck
    · simp at hAck; left; rw [← hAck]
      rename_i hCond
      simp only [Bool.and_eq_true, SeqNum.le, SeqNum.lt, SeqNum.halfSpace,
        Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at *
      bv_decide
    · simp at hAck
  · -- Established
    split at hAck
    · simp at hAck
    · simp at hAck; left; rw [← hAck]; exact ackUpdate_sndUna_monotone _ _
  · -- FinWait1
    split at hAck
    · simp at hAck
    · simp at hAck; left; rw [← hAck]
      simp only [ackUpdate, windowUpdateTcb_sndUna]
      exact ackAdvanceTcb_sndUna_monotone _ _
  · -- FinWait2
    split at hAck
    · simp at hAck
    · simp at hAck; left; rw [← hAck]; exact ackUpdate_sndUna_monotone _ _
  · -- CloseWait
    split at hAck
    · simp at hAck
    · simp at hAck; left; rw [← hAck]; exact ackUpdate_sndUna_monotone _ _
  · -- Closing
    split at hAck
    · simp at hAck
    · split at hAck
      · split at hAck <;> simp at hAck <;> rw [← hAck]
        · left; simp only [ackUpdate, windowUpdateTcb_sndUna]
          exact ackAdvanceTcb_sndUna_monotone _ _
        · left; exact ackUpdate_sndUna_monotone _ _
      · simp at hAck; rw [← hAck]; left; exact ackUpdate_sndUna_monotone _ _
  · -- LastAck
    split at hAck
    · split at hAck <;> simp at hAck <;> rw [← hAck]
      · right; exact ⟨rfl, rfl⟩
      · left; exact SeqNum.le_refl _
    · simp at hAck; rw [← hAck]; left; exact SeqNum.le_refl _
  · -- TimeWait
    simp at hAck; rw [← hAck]; left; exact SeqNum.le_refl _
  · -- fallthrough
    simp at hAck; rw [← hAck]; left; exact SeqNum.le_refl _

/-- pipelinePreAck is monotone in sndUna, or transitions to Closed with sndUna = 0. -/
theorem pipelinePreAck_sndUna_monotone (ep : TcpEndpoint) (seg : Segment)
    (result : ProcessResult) (hPre : pipelinePreAck ep seg = some result) :
    SeqNum.le ep.tcb.sndUna result.endpoint.tcb.sndUna = true
    ∨ (result.endpoint.state = .Closed ∧ result.endpoint.tcb.sndUna = ⟨0⟩) := by
  unfold pipelinePreAck at hPre; dsimp only [mkSegment] at hPre
  split at hPre
  · split at hPre <;> simp at hPre <;> rw [← hPre]
    · left; exact SeqNum.le_refl _
    · left; exact SeqNum.le_refl _
  · split at hPre
    · split at hPre
      · -- SynReceived RST
        split at hPre <;> simp at hPre <;> rw [← hPre]
        · left; exact SeqNum.le_refl _  -- Listen: same tcb
        · right; simp [closedEndpoint]
      -- Remaining RST cases: closedEndpoint (right) or ep unchanged (left)
      all_goals (simp at hPre; rw [← hPre]; first
        | (left; exact SeqNum.le_refl _)
        | (right; simp [closedEndpoint]))
    · split at hPre
      · simp at hPre; rw [← hPre]; right; simp [closedEndpoint]
      · split at hPre
        · simp at hPre; rw [← hPre]; left; exact SeqNum.le_refl _
        · simp at hPre

/-- pipelineAckReject doesn't change the endpoint. -/
theorem pipelineAckReject_sndUna_monotone (ep : TcpEndpoint) (seg : Segment) :
    SeqNum.le ep.tcb.sndUna (pipelineAckReject ep seg).endpoint.tcb.sndUna = true := by
  unfold pipelineAckReject; dsimp only [mkSegment]
  split <;> exact SeqNum.le_refl _

/-- processSegmentOtherwise: sndUna is monotone or endpoint transitions to Closed. -/
theorem processSegmentOtherwise_sndUna_monotone (ep : TcpEndpoint) (seg : Segment) :
    SeqNum.le ep.tcb.sndUna (processSegmentOtherwise ep seg).endpoint.tcb.sndUna = true
    ∨ ((processSegmentOtherwise ep seg).endpoint.state = .Closed
       ∧ (processSegmentOtherwise ep seg).endpoint.tcb.sndUna = ⟨0⟩) := by
  simp only [processSegmentOtherwise]
  split
  · rename_i result hPre
    exact pipelinePreAck_sndUna_monotone ep seg result hPre
  · split
    · left; exact pipelineAckReject_sndUna_monotone ep seg
    · rename_i ep' hA
      -- pipelineAck gives us ep' with le or (Closed, sndUna = 0)
      rcases pipelineAck_sndUna_monotone ep seg ep' hA with hMono | ⟨hState, hUna⟩
      · -- ep' has monotone sndUna, now pipelinePostAck preserves it
        left; rw [pipelinePostAck_sndUna]; exact hMono
      · -- ep' has Closed state and sndUna = 0
        -- pipelinePostAck preserves state = Closed and sndUna = 0
        have hS1 : (pipelineUrg ep' seg).state = .Closed := by
          rw [pipelineUrg_state, hState]
        have hS2 : (pipelineText (pipelineUrg ep' seg) seg).1.state = .Closed := by
          rw [pipelineText_state, hS1]
        have hPostState : (pipelinePostAck ep' seg).endpoint.state = .Closed := by
          simp only [pipelinePostAck]
          unfold pipelineFin; dsimp only [mkSegment]
          split
          · rw [hS2]
          · split <;> rw [hS2]
        right; exact ⟨hPostState, by rw [pipelinePostAck_sndUna, hUna]⟩

/-- processSegmentClosed doesn't change the endpoint. -/
theorem processSegmentClosed_sndUna_monotone (ep : TcpEndpoint) (seg : Segment) :
    SeqNum.le ep.tcb.sndUna (processSegmentClosed ep seg).endpoint.tcb.sndUna = true := by
  simp only [processSegmentClosed]
  split <;> (try split) <;> exact SeqNum.le_refl _

/-- processSegmentSynSent: sndUna is monotone or endpoint transitions to Closed. -/
theorem processSegmentSynSent_sndUna_monotone (ep : TcpEndpoint) (seg : Segment)
    (hISS : issInvariant ep) (hState : ep.state = .SynSent) :
    SeqNum.le ep.tcb.sndUna (processSegmentSynSent ep seg).endpoint.tcb.sndUna = true
    ∨ ((processSegmentSynSent ep seg).endpoint.state = .Closed
       ∧ (processSegmentSynSent ep seg).endpoint.tcb.sndUna = ⟨0⟩) := by
  have hIss := hISS hState  -- ep.tcb.sndUna = ep.tcb.iss
  unfold processSegmentSynSent; dsimp only [mkSegment, defaultRcvWnd]
  -- Use same split approach as processSegmentSynSent_preserves
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
    (try split) <;> (try split)
  -- Handle each case:
  -- ep unchanged → left, le_refl
  -- closedEndpoint → right, ⟨rfl, rfl⟩
  -- ESTABLISHED path → left, pipelinePostAck_sndUna + issInvariant
  all_goals first
    | (left; exact SeqNum.le_refl _)
    | (right; exact ⟨rfl, rfl⟩)
    | -- ESTABLISHED path: sndUna after pipelinePostAck
      (left; rw [pipelinePostAck_sndUna]; dsimp only []
       -- In ACK case: sndUna = seg.ackNum, need le iss seg.ackNum from ackOk
       -- In no-ACK case: impossible (lt iss iss contradicts lt_irrefl)
       simp only [hIss, SeqNum.le, SeqNum.lt, SeqNum.halfSpace,
         Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
         Bool.not_eq_true, decide_eq_true_eq] at *
       bv_decide)

/-- processSegmentListen: sndUna is monotone or endpoint is new (SYN case). -/
theorem processSegmentListen_sndUna_monotone (ep : TcpEndpoint) (seg : Segment) (iss : SeqNum) :
    SeqNum.le ep.tcb.sndUna (processSegmentListen ep seg iss).endpoint.tcb.sndUna = true
    ∨ (processSegmentListen ep seg iss).endpoint.state = .SynReceived := by
  simp only [processSegmentListen]
  split
  · left; exact SeqNum.le_refl _  -- RST
  · split
    · left; exact SeqNum.le_refl _  -- ACK
    · split
      · right; rfl  -- SYN → SynReceived
      · left; exact SeqNum.le_refl _  -- other

/-- sndUna is monotone unless the connection was reset or freshly initialized. -/
def sndUnaMonotone (old new : TcpEndpoint) : Prop :=
  SeqNum.le old.tcb.sndUna new.tcb.sndUna = true
  ∨ (new.state = .Closed ∧ new.tcb.sndUna = ⟨0⟩)
  ∨ old.state ∈ [.Closed, .Listen]

/-- processSegment: sndUna is monotone unless connection was reset or freshly initialized. -/
theorem processSegment_sndUna_monotone (ep : TcpEndpoint) (seg : Segment) (iss : SeqNum)
    (hInv : endpointInvariant ep) :
    sndUnaMonotone ep (processSegment ep seg iss).endpoint := by
  simp only [sndUnaMonotone, processSegment]
  split
  · left; exact processSegmentClosed_sndUna_monotone ep seg
  · -- Listen
    right; right; simp_all [List.mem_cons]
  · -- SynSent
    obtain ⟨_, _, hI⟩ := hInv
    rcases processSegmentSynSent_sndUna_monotone ep seg hI ‹ep.state = _› with h | h
    · left; exact h
    · right; left; exact h
  · -- Otherwise
    rcases processSegmentOtherwise_sndUna_monotone ep seg with h | h
    · left; exact h
    · right; left; exact h

theorem processOpen_sndUna_monotone (ep : TcpEndpoint) (mode : OpenMode) (iss : SeqNum) :
    sndUnaMonotone ep (processOpen ep mode iss).endpoint := by
  simp only [sndUnaMonotone, processOpen]
  split
  · split
    · -- Closed + Passive → Listen: freshTcb
      right; right; simp_all [List.mem_cons]
    · -- Closed + Active → SynSent: freshTcb
      right; right; simp_all [List.mem_cons]
  · split
    · -- Listen + Active → SynSent
      right; right; simp_all [List.mem_cons]
    · -- Listen + Passive → error, ep unchanged
      left; exact SeqNum.le_refl _
  · -- Other → ep unchanged
    left; exact SeqNum.le_refl _

theorem processSend_sndUna_monotone (ep : TcpEndpoint) (data : List UInt8) :
    sndUnaMonotone ep (processSend ep data).endpoint := by
  simp only [sndUnaMonotone, processSend]
  split
  all_goals first
    | (left; exact SeqNum.le_refl _)
    | (left; show SeqNum.le ep.tcb.sndUna (segmentize _).1.tcb.sndUna = true
       rw [segmentize_sndUna]; exact SeqNum.le_refl _)

theorem processReceive_sndUna_monotone (ep : TcpEndpoint) :
    sndUnaMonotone ep (processReceive ep).endpoint := by
  simp only [sndUnaMonotone, processReceive]
  split <;> (try split) <;> (left; exact SeqNum.le_refl _)

theorem processClose_sndUna_monotone (ep : TcpEndpoint) :
    sndUnaMonotone ep (processClose ep).endpoint := by
  simp only [sndUnaMonotone, processClose]
  split
  · left; exact SeqNum.le_refl _  -- Closed
  · right; left; simp [closedEndpoint]  -- Listen → closedEndpoint
  · right; left; simp [closedEndpoint]  -- SynSent → closedEndpoint
  · -- SynReceived
    split
    · left; dsimp only [mkSegment]; exact SeqNum.le_refl _  -- FIN: sndUna unchanged
    · left; exact SeqNum.le_refl _
  · -- Established: segmentize + FIN — sndUna from segmentize = ep.tcb.sndUna
    left; dsimp only [mkSegment]; rw [segmentize_sndUna]; exact SeqNum.le_refl _
  · left; exact SeqNum.le_refl _  -- FinWait1
  · left; exact SeqNum.le_refl _  -- FinWait2
  · -- CloseWait: segmentize + FIN
    left; dsimp only [mkSegment]; rw [segmentize_sndUna]; exact SeqNum.le_refl _
  · left; exact SeqNum.le_refl _  -- Closing
  · left; exact SeqNum.le_refl _  -- LastAck
  · left; exact SeqNum.le_refl _  -- TimeWait

theorem processAbort_sndUna_monotone (ep : TcpEndpoint) :
    sndUnaMonotone ep (processAbort ep).endpoint := by
  simp only [sndUnaMonotone]; unfold processAbort; dsimp only [mkSegment]
  split
  · left; exact SeqNum.le_refl _  -- Closed
  all_goals (right; left; simp [closedEndpoint])

/-- For user calls, sndUna is monotone unless connection was reset or freshly initialized. -/
theorem processUserCall_sndUna_monotone (ep : TcpEndpoint) (call : UserCall) :
    sndUnaMonotone ep (processUserCall ep call).endpoint := by
  simp only [processUserCall]
  cases call with
  | Open mode iss => exact processOpen_sndUna_monotone ep mode iss
  | Send data => exact processSend_sndUna_monotone ep data
  | Receive => exact processReceive_sndUna_monotone ep
  | Close => exact processClose_sndUna_monotone ep
  | Abort => exact processAbort_sndUna_monotone ep
  | Status => simp [sndUnaMonotone, SeqNum.le_refl]

/-- For timeouts, sndUna is monotone unless connection was reset. -/
theorem processTimeout_sndUna_monotone (ep : TcpEndpoint) (kind : TimeoutKind) :
    sndUnaMonotone ep (processTimeout ep kind).endpoint := by
  simp only [sndUnaMonotone, processTimeout]
  split
  · -- UserTimeout → closedEndpoint
    right; left; simp [closedEndpoint]
  · -- Retransmission
    split <;> (left; exact SeqNum.le_refl _)
  · -- TimeWait
    split
    · right; left; simp [closedEndpoint]
    · left; exact SeqNum.le_refl _

/-- System-level SND.UNA monotonicity: for any SystemStep, each endpoint's SND.UNA
    either stays the same or increases, or the endpoint was reset to Closed (with
    sndUna = 0), or the endpoint was in Closed/Listen before the step. -/
theorem systemStep_sndUna_monotone (s s' : System)
    (hStep : SystemStep s s') (hInv : systemInvariant s) :
    sndUnaMonotone s.endpointA s'.endpointA ∧ sndUnaMonotone s.endpointB s'.endpointB := by
  obtain ⟨hA, hB⟩ := hInv
  cases hStep with
  | deliverToA seg h_mem result h_proc =>
    constructor
    · exact h_proc ▸ processSegment_sndUna_monotone _ seg _ hA
    · left; exact SeqNum.le_refl _
  | deliverToB seg h_mem result h_proc =>
    constructor
    · left; exact SeqNum.le_refl _
    · exact h_proc ▸ processSegment_sndUna_monotone _ seg _ hB
  | userCallA call result h_proc =>
    constructor
    · exact h_proc ▸ processUserCall_sndUna_monotone _ call
    · left; exact SeqNum.le_refl _
  | userCallB call result h_proc =>
    constructor
    · left; exact SeqNum.le_refl _
    · exact h_proc ▸ processUserCall_sndUna_monotone _ call
  | timeoutA kind result h_proc =>
    constructor
    · exact h_proc ▸ processTimeout_sndUna_monotone _ kind
    · left; exact SeqNum.le_refl _
  | timeoutB kind result h_proc =>
    constructor
    · left; exact SeqNum.le_refl _
    · exact h_proc ▸ processTimeout_sndUna_monotone _ kind
  | segmentLoss seg h_mem =>
    exact ⟨Or.inl (SeqNum.le_refl _), Or.inl (SeqNum.le_refl _)⟩
  | segmentDup seg h_mem =>
    exact ⟨Or.inl (SeqNum.le_refl _), Or.inl (SeqNum.le_refl _)⟩

-- ============================================================================
-- RCV.NXT Monotonicity (Checklist 2.4)
-- ============================================================================

/-- rcvNxt is monotone unless the connection was reset or freshly initialized. -/
def rcvNxtMonotone (old new : TcpEndpoint) : Prop :=
  SeqNum.le old.tcb.rcvNxt new.tcb.rcvNxt = true
  ∨ new.state = .Closed
  ∨ old.state = .Closed ∨ old.state = .Listen ∨ old.state = .SynSent

-- ============================================================================
-- RCV.NXT simp lemmas for pipeline projections
-- ============================================================================

@[simp] theorem pipelineUrg_rcvNxt (ep : TcpEndpoint) (seg : Segment) :
    (pipelineUrg ep seg).tcb.rcvNxt = ep.tcb.rcvNxt := by
  simp only [pipelineUrg]; split <;> (try split) <;> simp_all

@[simp] theorem ackAdvanceTcb_rcvNxt (tcb : Tcb) (seg : Segment) :
    (ackAdvanceTcb tcb seg).rcvNxt = tcb.rcvNxt := by
  simp only [ackAdvanceTcb]; split <;> simp_all

@[simp] theorem windowUpdateTcb_rcvNxt (tcb : Tcb) (seg : Segment) :
    (windowUpdateTcb tcb seg).rcvNxt = tcb.rcvNxt := by
  simp only [windowUpdateTcb]; split <;> simp_all

@[simp] theorem ackUpdate_rcvNxt (ep : TcpEndpoint) (seg : Segment) :
    (ackUpdate ep seg).tcb.rcvNxt = ep.tcb.rcvNxt := by
  simp only [ackUpdate, windowUpdateTcb_rcvNxt, ackAdvanceTcb_rcvNxt]

@[simp] theorem segmentize_rcvNxt (ep : TcpEndpoint) :
    (segmentize ep).1.tcb.rcvNxt = ep.tcb.rcvNxt := by
  simp only [segmentize]; split <;> (try split) <;> simp_all

-- ============================================================================
-- RCV.NXT monotonicity: SeqNum.le a (a.add n) for UInt32 n
-- ============================================================================

/-- Adding a small UInt32 to a SeqNum yields a result that is le-comparable. -/
private theorem SeqNum.le_add_small (a : SeqNum) (n : UInt32)
    (hn : n < SeqNum.halfSpace) :
    SeqNum.le a (a.add n) = true := by
  simp only [SeqNum.le, SeqNum.lt, SeqNum.add, SeqNum.halfSpace,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at *
  bv_decide

-- ============================================================================
-- RCV.NXT: Segment well-formedness
-- ============================================================================

/-- A segment is well-formed for RCV.NXT monotonicity if its data length < 2^31 - 1.
    This holds for all practical TCP segments (max segment size << 2^31). -/
def segmentRcvSmall (seg : Segment) : Prop :=
  seg.data.length < 2147483647  -- 2^31 - 1

/-- segmentRcvSmall implies data.length.toUInt32 + 1 < halfSpace. -/
private theorem segmentRcvSmall_add_one (seg : Segment) (h : segmentRcvSmall seg) :
    seg.data.length.toUInt32 + 1 < SeqNum.halfSpace := by
  simp only [segmentRcvSmall, SeqNum.halfSpace] at *
  unfold Nat.toUInt32 UInt32.ofNat
  show ((BitVec.ofNat 32 seg.data.length + BitVec.ofNat 32 1 : BitVec 32).toNat
        < (BitVec.ofNat 32 2147483648 : BitVec 32).toNat)
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have hLt : seg.data.length < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hLt, Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 32)]
  rw [Nat.mod_eq_of_lt (by omega : seg.data.length + 1 < 2 ^ 32)]
  rw [Nat.mod_eq_of_lt (by decide : 2147483648 < 2 ^ 32)]
  omega

/-- segmentRcvSmall implies data.length.toUInt32 < halfSpace. -/
private theorem segmentRcvSmall_data_lt (seg : Segment) (h : segmentRcvSmall seg) :
    seg.data.length.toUInt32 < SeqNum.halfSpace := by
  simp only [segmentRcvSmall, SeqNum.halfSpace] at *
  unfold Nat.toUInt32 UInt32.ofNat
  show ((BitVec.ofNat 32 seg.data.length : BitVec 32).toNat
        < (BitVec.ofNat 32 2147483648 : BitVec 32).toNat)
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : seg.data.length < 2 ^ 32)]
  rw [Nat.mod_eq_of_lt (by decide : 2147483648 < 2 ^ 32)]
  omega

-- ============================================================================
-- RCV.NXT: combined pipelinePostAck monotonicity (direct)
-- ============================================================================

/-- pipelineFin rcvNxt is either ep.rcvNxt or ep.rcvNxt + 1. -/
private theorem pipelineFin_rcvNxt_cases (ep : TcpEndpoint) (seg : Segment) (needAck : Bool) :
    (pipelineFin ep seg needAck).endpoint.tcb.rcvNxt = ep.tcb.rcvNxt
    ∨ (pipelineFin ep seg needAck).endpoint.tcb.rcvNxt = ep.tcb.rcvNxt.add 1 := by
  unfold pipelineFin; dsimp only [mkSegment]
  split
  · -- FIN: rcvNxt = ep.rcvNxt + 1
    split <;> (try split) <;> (try split) <;> right <;> rfl
  · -- no FIN: rcvNxt = ep.rcvNxt
    split <;> left <;> rfl

/-- pipelineText rcvNxt is either ep.rcvNxt or ep.rcvNxt + data.length. -/
private theorem pipelineText_rcvNxt_cases (ep : TcpEndpoint) (seg : Segment) :
    (pipelineText ep seg).1.tcb.rcvNxt = ep.tcb.rcvNxt
    ∨ (pipelineText ep seg).1.tcb.rcvNxt = ep.tcb.rcvNxt.add seg.data.length.toUInt32 := by
  simp only [pipelineText]
  -- 4 cases: Established, FinWait1, FinWait2, other
  split <;> (try split)
  all_goals first
    | (right; rfl)  -- data non-empty: rcvNxt = ep.rcvNxt + data.len
    | (left; rfl)   -- data empty or other state: rcvNxt = ep.rcvNxt

/-- pipelinePostAck advances rcvNxt monotonically when the segment is small. -/
theorem pipelinePostAck_rcvNxt_monotone (ep : TcpEndpoint) (seg : Segment)
    (hSeg : segmentRcvSmall seg) :
    SeqNum.le ep.tcb.rcvNxt (pipelinePostAck ep seg).endpoint.tcb.rcvNxt = true := by
  have hDataPlusOne := segmentRcvSmall_add_one seg hSeg
  have hDataLt := segmentRcvSmall_data_lt seg hSeg
  simp only [pipelinePostAck]
  -- Get the text result
  rcases pipelineText_rcvNxt_cases (pipelineUrg ep seg) seg with hT | hT
  · -- pipelineText didn't advance rcvNxt
    rw [pipelineUrg_rcvNxt] at hT
    rcases pipelineFin_rcvNxt_cases _ seg _ with hF | hF
    · rw [hF, hT]; exact SeqNum.le_refl _
    · rw [hF, hT]; exact SeqNum.le_add_one _
  · -- pipelineText advanced rcvNxt by data.length
    rw [pipelineUrg_rcvNxt] at hT
    rcases pipelineFin_rcvNxt_cases _ seg _ with hF | hF
    · rw [hF, hT]; exact SeqNum.le_add_small _ _ hDataLt
    · rw [hF, hT, SeqNum.add_add]; exact SeqNum.le_add_small _ _ hDataPlusOne

-- ============================================================================
-- RCV.NXT: pipelineAck doesn't change rcvNxt
-- ============================================================================

theorem pipelineAck_rcvNxt (ep : TcpEndpoint) (seg : Segment)
    (ep' : TcpEndpoint) (hAck : pipelineAck ep seg = some ep') :
    ep'.tcb.rcvNxt = ep.tcb.rcvNxt
    ∨ (ep'.state = .Closed ∧ ep'.tcb.rcvNxt = ⟨0⟩) := by
  simp only [pipelineAck] at hAck
  split at hAck
  · -- SynReceived
    split at hAck <;> simp at hAck; left; rw [← hAck]
  · -- Established
    split at hAck <;> simp at hAck; left; rw [← hAck]; simp [ackUpdate_rcvNxt]
  · -- FinWait1
    split at hAck <;> simp at hAck; left; rw [← hAck]
    simp [ackUpdate, windowUpdateTcb_rcvNxt, ackAdvanceTcb_rcvNxt]
  · -- FinWait2
    split at hAck <;> simp at hAck; left; rw [← hAck]; simp [ackUpdate_rcvNxt]
  · -- CloseWait
    split at hAck <;> simp at hAck; left; rw [← hAck]; simp [ackUpdate_rcvNxt]
  · -- Closing
    split at hAck
    · simp at hAck
    · split at hAck
      · split at hAck <;> simp at hAck <;> rw [← hAck]
        · left; simp [ackUpdate, windowUpdateTcb_rcvNxt, ackAdvanceTcb_rcvNxt]
        · left; simp [ackUpdate_rcvNxt]
      · simp at hAck; left; rw [← hAck]; simp [ackUpdate_rcvNxt]
  · -- LastAck
    split at hAck
    · split at hAck <;> simp at hAck <;> rw [← hAck]
      · right; simp [closedEndpoint]
      · left; rfl
    · simp at hAck; left; rw [← hAck]
  · -- TimeWait
    simp at hAck; left; rw [← hAck]
  · -- fallthrough
    simp at hAck; left; rw [← hAck]

-- ============================================================================
-- RCV.NXT: pipelinePreAck doesn't change rcvNxt (or goes to Closed)
-- ============================================================================

theorem pipelinePreAck_rcvNxt_monotone (ep : TcpEndpoint) (seg : Segment)
    (result : ProcessResult) (hPre : pipelinePreAck ep seg = some result) :
    SeqNum.le ep.tcb.rcvNxt result.endpoint.tcb.rcvNxt = true
    ∨ (result.endpoint.state = .Closed ∧ result.endpoint.tcb.rcvNxt = ⟨0⟩) := by
  unfold pipelinePreAck at hPre; dsimp only [mkSegment] at hPre
  split at hPre
  · split at hPre <;> simp at hPre <;> rw [← hPre]
    · left; exact SeqNum.le_refl _
    · left; exact SeqNum.le_refl _
  · split at hPre
    · split at hPre
      · split at hPre <;> simp at hPre <;> rw [← hPre]
        · left; exact SeqNum.le_refl _  -- Listen: same tcb
        · right; simp [closedEndpoint]
      all_goals (simp at hPre; rw [← hPre]; first
        | (left; exact SeqNum.le_refl _)
        | (right; simp [closedEndpoint]))
    · split at hPre
      · simp at hPre; rw [← hPre]; right; simp [closedEndpoint]
      · split at hPre
        · simp at hPre; rw [← hPre]; left; exact SeqNum.le_refl _
        · simp at hPre

-- ============================================================================
-- RCV.NXT: processSegmentOtherwise monotonicity
-- ============================================================================

theorem processSegmentOtherwise_rcvNxt_monotone (ep : TcpEndpoint) (seg : Segment)
    (hSeg : segmentRcvSmall seg) :
    SeqNum.le ep.tcb.rcvNxt (processSegmentOtherwise ep seg).endpoint.tcb.rcvNxt = true
    ∨ (processSegmentOtherwise ep seg).endpoint.state = .Closed := by
  simp only [processSegmentOtherwise]
  split
  · rename_i result hPre
    rcases pipelinePreAck_rcvNxt_monotone ep seg result hPre with h | ⟨hS, _⟩
    · left; exact h
    · right; exact hS
  · split
    · -- pipelineAckReject: ep unchanged
      left; unfold pipelineAckReject; dsimp only [mkSegment]
      split <;> exact SeqNum.le_refl _
    · rename_i ep' hA
      rcases pipelineAck_rcvNxt ep seg ep' hA with hRcv | ⟨hState, _⟩
      · -- rcvNxt unchanged: pipelinePostAck advances from ep.rcvNxt
        left
        have := pipelinePostAck_rcvNxt_monotone ep' seg hSeg
        rw [hRcv] at this; exact this
      · -- Closed: pipelinePostAck on Closed ep' — state stays Closed
        right
        have hS1 : (pipelineUrg ep' seg).state = .Closed := by
          rw [pipelineUrg_state, hState]
        have hS2 : (pipelineText (pipelineUrg ep' seg) seg).1.state = .Closed := by
          rw [pipelineText_state, hS1]
        simp only [pipelinePostAck]
        unfold pipelineFin; dsimp only [mkSegment]
        split
        · rw [hS2]
        · split <;> rw [hS2]

-- ============================================================================
-- RCV.NXT: full processing functions
-- ============================================================================

theorem processSegmentClosed_rcvNxt_monotone (ep : TcpEndpoint) (seg : Segment) :
    SeqNum.le ep.tcb.rcvNxt (processSegmentClosed ep seg).endpoint.tcb.rcvNxt = true := by
  simp only [processSegmentClosed]
  split <;> (try split) <;> exact SeqNum.le_refl _

theorem processSegment_rcvNxt_monotone (ep : TcpEndpoint) (seg : Segment) (iss : SeqNum)
    (hSeg : segmentRcvSmall seg) :
    rcvNxtMonotone ep (processSegment ep seg iss).endpoint := by
  simp only [rcvNxtMonotone, processSegment]
  split
  · left; exact processSegmentClosed_rcvNxt_monotone ep seg
  · -- Listen
    right; right; right; left; assumption
  · -- SynSent
    right; right; right; right; assumption
  · -- Otherwise
    rcases processSegmentOtherwise_rcvNxt_monotone ep seg hSeg with h | h
    · left; exact h
    · right; left; exact h

theorem processUserCall_rcvNxt_monotone (ep : TcpEndpoint) (call : UserCall) :
    rcvNxtMonotone ep (processUserCall ep call).endpoint := by
  simp only [rcvNxtMonotone, processUserCall]
  cases call with
  | Open mode iss =>
    simp only [processOpen]
    split
    · -- Closed
      right; right; left; assumption
    · split
      · -- Listen + Active
        right; right; right; left; assumption
      · -- Listen + Passive → ep unchanged
        left; exact SeqNum.le_refl _
    · -- Other → ep unchanged
      left; exact SeqNum.le_refl _
  | Send data =>
    left; simp only [processSend]
    split
    all_goals first
      | exact SeqNum.le_refl _
      | (show SeqNum.le _ (segmentize _).1.tcb.rcvNxt = true
         rw [segmentize_rcvNxt]; exact SeqNum.le_refl _)
  | Receive =>
    left; simp only [processReceive]
    split <;> (try split) <;> exact SeqNum.le_refl _
  | Close =>
    simp only [processClose]
    split
    · left; exact SeqNum.le_refl _
    · right; left; rfl
    · right; left; rfl
    · -- SynReceived
      split
      · left; dsimp only [mkSegment]; exact SeqNum.le_refl _
      · left; exact SeqNum.le_refl _
    · -- Established: segmentize + FIN
      left; dsimp only [mkSegment]; rw [segmentize_rcvNxt]; exact SeqNum.le_refl _
    · left; exact SeqNum.le_refl _  -- FinWait1
    · left; exact SeqNum.le_refl _  -- FinWait2
    · -- CloseWait: segmentize + FIN
      left; dsimp only [mkSegment]; rw [segmentize_rcvNxt]; exact SeqNum.le_refl _
    · left; exact SeqNum.le_refl _  -- Closing
    · left; exact SeqNum.le_refl _  -- LastAck
    · left; exact SeqNum.le_refl _  -- TimeWait
  | Abort =>
    unfold processAbort; dsimp only [mkSegment]
    split
    · left; exact SeqNum.le_refl _
    all_goals (right; left; rfl)
  | Status => left; exact SeqNum.le_refl _

theorem processTimeout_rcvNxt_monotone (ep : TcpEndpoint) (kind : TimeoutKind) :
    rcvNxtMonotone ep (processTimeout ep kind).endpoint := by
  simp only [rcvNxtMonotone, processTimeout]
  split
  · right; left; rfl
  · split <;> (left; exact SeqNum.le_refl _)
  · split
    · right; left; rfl
    · left; exact SeqNum.le_refl _

/-- System-level RCV.NXT monotonicity: for any SystemStep with well-formed segments,
    each endpoint's RCV.NXT either stays the same or increases, or the endpoint was
    reset to Closed, or the endpoint was in Closed/Listen/SynSent before the step. -/
theorem systemStep_rcvNxt_monotone (s s' : System)
    (hStep : SystemStep s s')
    (hSegs : ∀ seg ∈ s.network, segmentRcvSmall seg) :
    rcvNxtMonotone s.endpointA s'.endpointA ∧ rcvNxtMonotone s.endpointB s'.endpointB := by
  cases hStep with
  | deliverToA seg h_mem result h_proc =>
    constructor
    · exact h_proc ▸ processSegment_rcvNxt_monotone _ seg _ (hSegs seg h_mem)
    · left; exact SeqNum.le_refl _
  | deliverToB seg h_mem result h_proc =>
    constructor
    · left; exact SeqNum.le_refl _
    · exact h_proc ▸ processSegment_rcvNxt_monotone _ seg _ (hSegs seg h_mem)
  | userCallA call result h_proc =>
    constructor
    · exact h_proc ▸ processUserCall_rcvNxt_monotone _ call
    · left; exact SeqNum.le_refl _
  | userCallB call result h_proc =>
    constructor
    · left; exact SeqNum.le_refl _
    · exact h_proc ▸ processUserCall_rcvNxt_monotone _ call
  | timeoutA kind result h_proc =>
    constructor
    · exact h_proc ▸ processTimeout_rcvNxt_monotone _ kind
    · left; exact SeqNum.le_refl _
  | timeoutB kind result h_proc =>
    constructor
    · left; exact SeqNum.le_refl _
    · exact h_proc ▸ processTimeout_rcvNxt_monotone _ kind
  | segmentLoss seg h_mem =>
    exact ⟨Or.inl (SeqNum.le_refl _), Or.inl (SeqNum.le_refl _)⟩
  | segmentDup seg h_mem =>
    exact ⟨Or.inl (SeqNum.le_refl _), Or.inl (SeqNum.le_refl _)⟩

-- ============================================================================
-- Phase 3.1: ESTABLISHED Requires Handshake
-- ============================================================================

/-! ### Per-function lemmas: which transitions can produce ESTABLISHED

We prove that ESTABLISHED is only reachable by processing a segment, never by
a user call or timeout, and that the segment must carry specific control bits.
Together these lemmas show that a three-way handshake (SYN → SYN-ACK → ACK)
is the *only* path to ESTABLISHED. -/

-- --------------------------------------------------------------------------
-- User calls never enter ESTABLISHED from a non-ESTABLISHED state
-- --------------------------------------------------------------------------

/-- `processOpen` never transitions to ESTABLISHED. -/
theorem processOpen_not_established (ep : TcpEndpoint) (mode : OpenMode) (iss : SeqNum)
    (hPre : ep.state ≠ .Established) :
    (processOpen ep mode iss).endpoint.state ≠ .Established := by
  simp only [processOpen]
  split
  · split <;> simp_all [TcpState.noConfusion]
  · split <;> simp_all [TcpState.noConfusion]
  · exact hPre

/-- `processSend` preserves the connection state. -/
theorem processSend_state (ep : TcpEndpoint) (data : List UInt8) :
    (processSend ep data).endpoint.state = ep.state ∨
    (processSend ep data).endpoint.state = .Closed := by
  simp only [processSend]
  split <;> simp_all
  all_goals (try (left; rfl))
  -- Established / CloseWait: segmentize preserves state
  all_goals
    left; show (segmentize _).1.state = _
    simp only [segmentize]; split <;> (try split) <;> simp_all

/-- `processSend` never transitions to ESTABLISHED from non-ESTABLISHED. -/
theorem processSend_not_established (ep : TcpEndpoint) (data : List UInt8)
    (hPre : ep.state ≠ .Established) :
    (processSend ep data).endpoint.state ≠ .Established := by
  have h := processSend_state ep data
  cases h with
  | inl h => rw [h]; exact hPre
  | inr h => rw [h]; exact TcpState.noConfusion

/-- `processReceive` preserves state. -/
theorem processReceive_state (ep : TcpEndpoint) :
    (processReceive ep).endpoint.state = ep.state := by
  simp only [processReceive]; split <;> (try split) <;> simp_all

/-- `processReceive` never transitions to ESTABLISHED from non-ESTABLISHED. -/
theorem processReceive_not_established (ep : TcpEndpoint)
    (hPre : ep.state ≠ .Established) :
    (processReceive ep).endpoint.state ≠ .Established := by
  rw [processReceive_state]; exact hPre

/-- `processClose` never transitions to ESTABLISHED. -/
theorem processClose_not_established (ep : TcpEndpoint)
    (hPre : ep.state ≠ .Established) :
    (processClose ep).endpoint.state ≠ .Established := by
  simp only [processClose]
  cases hState : ep.state <;> simp_all [closedEndpoint, TcpState.noConfusion]
  -- SynReceived: split on sendQueue.isEmpty
  split
  · simp [TcpState.noConfusion]
  · rw [hState]; exact TcpState.noConfusion

/-- `processAbort` never transitions to ESTABLISHED. -/
theorem processAbort_not_established (ep : TcpEndpoint)
    (hPre : ep.state ≠ .Established) :
    (processAbort ep).endpoint.state ≠ .Established := by
  simp only [processAbort]
  split <;> simp_all [closedEndpoint, TcpState.noConfusion]

/-- No user call can transition to ESTABLISHED from a non-ESTABLISHED state. -/
theorem processUserCall_not_established (ep : TcpEndpoint) (call : UserCall)
    (hPre : ep.state ≠ .Established) :
    (processUserCall ep call).endpoint.state ≠ .Established := by
  simp only [processUserCall]
  cases call with
  | Open mode iss => exact processOpen_not_established ep mode iss hPre
  | Send data => exact processSend_not_established ep data hPre
  | Receive => exact processReceive_not_established ep hPre
  | Close => exact processClose_not_established ep hPre
  | Abort => exact processAbort_not_established ep hPre
  | Status => simp; exact hPre

-- --------------------------------------------------------------------------
-- Timeouts never enter ESTABLISHED
-- --------------------------------------------------------------------------

/-- No timeout can transition to ESTABLISHED. -/
theorem processTimeout_not_established (ep : TcpEndpoint)
    (kind : TimeoutKind)
    (hPre : ep.state ≠ .Established) :
    (processTimeout ep kind).endpoint.state ≠ .Established := by
  simp only [processTimeout]
  split
  · simp [closedEndpoint, TcpState.noConfusion]
  · split <;> exact hPre
  · split
    · simp [closedEndpoint, TcpState.noConfusion]
    · exact hPre

-- --------------------------------------------------------------------------
-- Segment processing in CLOSED state never enters ESTABLISHED
-- --------------------------------------------------------------------------

/-- Segment arrival in CLOSED state never transitions to ESTABLISHED. -/
theorem processSegmentClosed_not_established (ep : TcpEndpoint) (seg : Segment)
    (hPre : ep.state ≠ .Established) :
    (processSegmentClosed ep seg).endpoint.state ≠ .Established := by
  simp only [processSegmentClosed]
  split <;> (try split) <;> exact hPre

-- --------------------------------------------------------------------------
-- LISTEN → SYN-RECEIVED requires SYN
-- --------------------------------------------------------------------------

/-- If `processSegmentListen` changes the state from LISTEN, the new state
    is SYN-RECEIVED and the segment had SYN set. -/
theorem processSegmentListen_syn (ep : TcpEndpoint) (seg : Segment) (iss : SeqNum)
    (hState : ep.state = .Listen)
    (hChanged : (processSegmentListen ep seg iss).endpoint.state ≠ .Listen) :
    (processSegmentListen ep seg iss).endpoint.state = .SynReceived ∧
    seg.ctl.syn = true := by
  unfold processSegmentListen at hChanged ⊢
  -- Simplify each if-then-else by splitting on the control bits
  by_cases hRst : seg.ctl.rst = true
  · simp [hRst, hState] at hChanged
  · by_cases hAck : seg.ctl.ack = true
    · simp [hRst, hAck, hState] at hChanged
    · by_cases hSyn : seg.ctl.syn = true
      · simp [hRst, hAck, hSyn]
      · simp [hRst, hAck, hSyn, hState] at hChanged

/-- `processSegmentListen` never enters ESTABLISHED. -/
theorem processSegmentListen_not_established (ep : TcpEndpoint) (seg : Segment)
    (iss : SeqNum) (hState : ep.state = .Listen) :
    (processSegmentListen ep seg iss).endpoint.state ≠ .Established := by
  simp only [processSegmentListen]
  split
  · -- RST: state = ep.state = LISTEN
    rw [hState]; exact TcpState.noConfusion
  · split
    · -- ACK: state = ep.state = LISTEN
      rw [hState]; exact TcpState.noConfusion
    · split
      · -- SYN: state = SynReceived
        exact TcpState.noConfusion
      · -- else: state = ep.state = LISTEN
        rw [hState]; exact TcpState.noConfusion

-- --------------------------------------------------------------------------
-- SYN-SENT → ESTABLISHED requires SYN ∧ ACK
-- --------------------------------------------------------------------------

-- --------------------------------------------------------------------------
-- The 8-check pipeline: ESTABLISHED only from SYN-RECEIVED
-- --------------------------------------------------------------------------

/-- `pipelinePreAck` never produces ESTABLISHED from a non-ESTABLISHED state.
    It either terminates with LISTEN, CLOSED, or the original state, or returns
    `none` to continue. -/
theorem pipelinePreAck_not_established (ep : TcpEndpoint) (seg : Segment)
    (hPre : ep.state ≠ .Established) (result : ProcessResult)
    (hSome : pipelinePreAck ep seg = some result) :
    result.endpoint.state ≠ .Established := by
  intro hEst
  have h := hSome
  unfold pipelinePreAck at h
  revert h
  split
  · -- not acceptable
    split
    · intro h; cases h; exact hPre hEst
    · dsimp only [mkSegment]; intro h; cases h; exact hPre hEst
  · split  -- rst=true: state match
    · split  -- SynReceived / openMode
      · split  -- Passive
        · intro h; simp only [Option.some.injEq] at h; rw [← h] at hEst
          exact TcpState.noConfusion hEst
        · intro h; simp only [Option.some.injEq] at h; rw [← h] at hEst
          simp [closedEndpoint] at hEst
      -- Established
      · intro h; simp only [Option.some.injEq] at h; rw [← h] at hEst
        simp [closedEndpoint] at hEst
      -- FW1
      · intro h; simp only [Option.some.injEq] at h; rw [← h] at hEst
        simp [closedEndpoint] at hEst
      -- FW2
      · intro h; simp only [Option.some.injEq] at h; rw [← h] at hEst
        simp [closedEndpoint] at hEst
      -- CloseWait
      · intro h; simp only [Option.some.injEq] at h; rw [← h] at hEst
        simp [closedEndpoint] at hEst
      -- Closing
      · intro h; simp only [Option.some.injEq] at h; rw [← h] at hEst
        simp [closedEndpoint] at hEst
      -- LastAck
      · intro h; simp only [Option.some.injEq] at h; rw [← h] at hEst
        simp [closedEndpoint] at hEst
      -- TimeWait
      · intro h; simp only [Option.some.injEq] at h; rw [← h] at hEst
        simp [closedEndpoint] at hEst
      -- wildcard
      · intro h; simp only [Option.some.injEq] at h; rw [← h] at hEst
        exact hPre hEst
    · split
      · -- syn=true
        dsimp only [mkSegment]; intro h; cases h; simp [closedEndpoint] at hEst
      · -- syn=false: if (!seg.ctl.ack)
        split
        · intro h; cases h; exact hPre hEst
        · intro h; exact absurd h (by simp)

/-- `pipelineAck` enters ESTABLISHED only from SYN-RECEIVED. -/
theorem pipelineAck_established_only_from_synReceived
    (ep : TcpEndpoint) (seg : Segment) (ep' : TcpEndpoint)
    (hPre : ep.state ≠ .Established)
    (hAck : pipelineAck ep seg = some ep')
    (hEst : ep'.state = .Established) :
    ep.state = .SynReceived := by
  simp only [pipelineAck] at hAck
  split at hAck
  · -- SynReceived
    rename_i heq; exact heq
  · -- Established: contradicts hPre
    rename_i heq; exact absurd heq hPre
  · -- FinWait1: future ACK guard, then state is FW1 or FW2
    split at hAck
    · simp at hAck
    · simp only [Option.some.injEq] at hAck; rw [← hAck] at hEst
      dsimp at hEst; split at hEst <;> (split at hEst <;> exact TcpState.noConfusion hEst)
  · -- FinWait2
    split at hAck
    · simp at hAck
    · simp only [Option.some.injEq] at hAck; rw [← hAck] at hEst
      exact absurd hEst hPre
  · -- CloseWait
    split at hAck
    · simp at hAck
    · simp only [Option.some.injEq] at hAck; rw [← hAck] at hEst
      exact absurd hEst hPre
  · -- Closing
    split at hAck
    · simp at hAck
    · split at hAck  -- match ep.finSeqNum
      · split at hAck  -- if finAcked
        · simp only [Option.some.injEq] at hAck; rw [← hAck] at hEst
          exact TcpState.noConfusion hEst
        · simp only [Option.some.injEq] at hAck; rw [← hAck] at hEst
          exact absurd hEst hPre
      · -- finSeqNum = none, finAcked = false
        simp at hAck; rw [← hAck] at hEst
        exact absurd hEst hPre
  · -- LastAck
    split at hAck  -- match ep.finSeqNum
    · split at hAck  -- if finAcked
      · simp only [Option.some.injEq] at hAck; rw [← hAck] at hEst
        simp [closedEndpoint] at hEst
      · simp only [Option.some.injEq] at hAck; rw [← hAck] at hEst
        exact absurd hEst hPre
    · -- finSeqNum = none
      simp at hAck; rw [← hAck] at hEst
      exact absurd hEst hPre
  · -- TimeWait
    simp only [Option.some.injEq] at hAck; rw [← hAck] at hEst
    exact absurd hEst hPre
  · -- wildcard
    simp only [Option.some.injEq] at hAck; rw [← hAck] at hEst
    exact absurd hEst hPre

/-- `pipelinePostAck` starting from ESTABLISHED can only produce ESTABLISHED
    or CloseWait (if the segment has FIN set). -/
theorem pipelinePostAck_from_established (ep : TcpEndpoint) (seg : Segment)
    (hState : ep.state = .Established) :
    (pipelinePostAck ep seg).endpoint.state = .Established ∨
    (pipelinePostAck ep seg).endpoint.state = .CloseWait := by
  simp only [pipelinePostAck, pipelineFin]
  split
  · -- FIN set: match on state of (pipelineText (pipelineUrg ep seg) seg).1
    simp only [pipelineUrg_state, pipelineText_state, hState]
    right; trivial
  · -- FIN not set: needAck branch
    split
    · left; simp [pipelineUrg_state, pipelineText_state, hState]
    · left; simp [pipelineUrg_state, pipelineText_state, hState]

/-- `pipelinePostAck` from a non-ESTABLISHED state never produces ESTABLISHED.
    pipelineFin's only Established-related transition is SynReceived|Established → CloseWait.
    pipelineUrg and pipelineText preserve state. -/
theorem pipelinePostAck_not_established (ep : TcpEndpoint) (seg : Segment)
    (hState : ep.state ≠ .Established) :
    (pipelinePostAck ep seg).endpoint.state ≠ .Established := by
  simp only [pipelinePostAck, pipelineFin]
  split
  · -- FIN set: match on state after pipelineUrg/pipelineText
    simp only [pipelineUrg_state, pipelineText_state]
    split
    · exact TcpState.noConfusion  -- SynReceived → CloseWait
    · exact TcpState.noConfusion  -- Established → CloseWait
    · -- FW1 → TimeWait or Closing depending on finAcked
      intro h; split at h <;> (split at h <;> exact TcpState.noConfusion h)
    · exact TcpState.noConfusion  -- FW2 → TimeWait
    · -- others: state unchanged (rcvNxt bumped but state = ep.state)
      intro h; simp [pipelineUrg_state, pipelineText_state] at h; exact hState h
  · -- FIN not set
    split
    · intro h; simp [pipelineUrg_state, pipelineText_state] at h; exact hState h
    · intro h; simp [pipelineUrg_state, pipelineText_state] at h; exact hState h

-- --------------------------------------------------------------------------
-- The precondition states for reaching ESTABLISHED
-- --------------------------------------------------------------------------

/-- The precondition states of an endpoint that can transition to ESTABLISHED
    in one segment-processing step. -/
inductive PreEstablishedState : TcpState → Prop where
  | synSent : PreEstablishedState .SynSent
  | synReceived : PreEstablishedState .SynReceived

/-- `processSegmentSynSent` only leaves state SynSent if SYN is set.
    Without SYN, the only possible transitions are to SynSent or Closed. -/
theorem processSegmentSynSent_not_established_without_syn
    (ep : TcpEndpoint) (seg : Segment)
    (hSyn : seg.ctl.syn = false) :
    (processSegmentSynSent ep seg).endpoint.state = ep.state ∨
    (processSegmentSynSent ep seg).endpoint.state = .Closed := by
  unfold processSegmentSynSent
  simp only [hSyn, ite_false]
  -- After simp, the SYN branch is eliminated. Now case split on remaining conditions.
  split  -- if seg.ctl.ack
  all_goals (simp only [Bool.not_eq_true', ite_true, ite_false]; try (left; rfl))
  all_goals split  -- if !ackOk
  all_goals (try split)  -- if seg.ctl.rst etc
  all_goals (first | (left; rfl) | (right; simp [closedEndpoint]) | (left; simp))

/-- An endpoint can only enter ESTABLISHED from SYN-SENT or SYN-RECEIVED
    via segment processing. No user call, timeout, or other state leads
    to ESTABLISHED. -/
theorem established_only_from_pre_established (ep : TcpEndpoint) (seg : Segment)
    (iss : SeqNum)
    (hPre : ep.state ≠ .Established)
    (hEst : (processSegment ep seg iss).endpoint.state = .Established) :
    PreEstablishedState ep.state := by
  simp only [processSegment] at hEst
  cases hState : ep.state <;> simp only [hState] at hEst
  · -- Closed: processSegmentClosed always returns ep unchanged
    simp only [processSegmentClosed] at hEst
    split at hEst <;> (try (split at hEst)) <;>
      (dsimp only [mkSegment] at hEst; exact absurd hEst (hState ▸ hPre))
  · -- Listen
    exact absurd hEst (processSegmentListen_not_established ep seg iss hState)
  · -- SynSent
    exact PreEstablishedState.synSent
  · -- SynReceived
    exact PreEstablishedState.synReceived
  · -- Established: contradicts hPre
    exact absurd hState hPre
  -- All remaining states (FW1, FW2, CW, Closing, LA, TW) go through processSegmentOtherwise.
  all_goals (
    have hPreOrig : ep.state ≠ .Established := hPre
    simp only [processSegmentOtherwise] at hEst
    cases hPreAck : pipelinePreAck ep seg with
    | some result =>
      simp only [hPreAck] at hEst
      exact absurd hEst (pipelinePreAck_not_established ep seg hPreOrig result hPreAck)
    | none =>
      simp only [hPreAck] at hEst
      cases hAck2 : pipelineAck ep seg with
      | none =>
        simp only [hAck2, pipelineAckReject] at hEst
        split at hEst <;> (dsimp only [mkSegment] at hEst; exact absurd hEst (hState ▸ hPreOrig))
      | some ep' =>
        simp only [hAck2] at hEst
        have hEp'NotEst : ep'.state ≠ .Established := by
          intro hContra
          have := pipelineAck_established_only_from_synReceived ep seg ep' hPreOrig hAck2 hContra
          rw [hState] at this; exact TcpState.noConfusion this
        exact absurd hEst (pipelinePostAck_not_established ep' seg hEp'NotEst)
  )

/-- Combined handshake theorem: any SystemStep that changes endpoint A
    to ESTABLISHED must deliver a segment and the endpoint must have been in
    SYN-SENT or SYN-RECEIVED beforehand. Since entering SYN-SENT requires
    an active OPEN, entering SYN-RECEIVED requires receiving a SYN, and
    entering ESTABLISHED from SYN-SENT requires a SYN+ACK, the three-way
    handshake is the only path. -/
theorem established_requires_handshake_step (s s' : System)
    (hStep : SystemStep s s')
    (hPreA : s.endpointA.state ≠ .Established)
    (hEstA : s'.endpointA.state = .Established) :
    ∃ seg, seg ∈ s.network ∧
    PreEstablishedState s.endpointA.state := by
  cases hStep with
  | deliverToA seg h_mem result h_proc =>
    simp at hEstA
    rw [← h_proc] at hEstA
    exact ⟨seg, h_mem, established_only_from_pre_established _ seg _ hPreA hEstA⟩
  | deliverToB seg h_mem result h_proc =>
    simp at hEstA; exact absurd hEstA hPreA
  | userCallA call result h_proc =>
    simp at hEstA
    rw [← h_proc] at hEstA
    cases call with
    | Open mode iss =>
      simp only [processUserCall, processOpen] at hEstA
      split at hEstA <;> (try split at hEstA) <;> simp_all [closedEndpoint, mkSegment]
    | Send data =>
      simp only [processUserCall, processSend] at hEstA
      split at hEstA <;> (try simp_all [segmentize])
      -- Established/CloseWait: segmentize preserves state; state is CloseWait in both branches
      all_goals (split at hEstA <;> (dsimp only [mkSegment] at hEstA; exact TcpState.noConfusion hEstA))
    | Receive =>
      simp only [processUserCall, processReceive] at hEstA
      split at hEstA <;> (try split at hEstA) <;> simp_all
    | Close =>
      simp only [processUserCall, processClose] at hEstA
      split at hEstA <;> (try split at hEstA) <;> simp_all [closedEndpoint, segmentize, mkSegment]
    | Abort =>
      simp only [processUserCall, processAbort] at hEstA
      split at hEstA <;> simp_all [closedEndpoint, mkSegment]
    | Status =>
      simp only [processUserCall] at hEstA
      exact absurd hEstA hPreA
  | userCallB call result h_proc =>
    simp at hEstA; exact absurd hEstA hPreA
  | timeoutA kind result h_proc =>
    simp at hEstA; rw [← h_proc] at hEstA
    simp only [processTimeout] at hEstA
    split at hEstA
    · simp [closedEndpoint] at hEstA
    · split at hEstA <;> simp_all
    · split at hEstA <;> simp_all [closedEndpoint]
  | timeoutB kind result h_proc =>
    simp at hEstA; exact absurd hEstA hPreA
  | segmentLoss seg h_mem =>
    simp at hEstA; exact absurd hEstA hPreA
  | segmentDup seg h_mem =>
    simp at hEstA; exact absurd hEstA hPreA

end Tcp
