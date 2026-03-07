import Tcp.SeqNum
import Tcp.Types

/-!
# Segment and ACK Acceptability

Predicates and lemmas for segment acceptability and ACK validation.

RFC 793 §3.3 specifies when an incoming segment is acceptable based on the
receive window and sequence numbers. This module defines the acceptability
predicates for both segments and acknowledgments, along with lemmas
establishing key properties of these predicates over the modular sequence
number space.

The segment acceptability test is a four-case table depending on whether the
segment carries data (`SEG.LEN > 0`) and whether the receive window is open
(`RCV.WND > 0`). The ACK acceptability test has two variants: strict left
inequality for ESTABLISHED and later states, and non-strict for SYN-RECEIVED.
-/

namespace Tcp

open SeqNum

-- ============================================================================
-- Segment Acceptability — RFC 793 §3.3
-- ============================================================================

/-- Segment acceptability predicate implementing the four-case table from
    RFC 793 §3.3:

    | SEG.LEN | RCV.WND | Test                                              |
    |---------|---------|---------------------------------------------------|
    | 0       | 0       | `SEG.SEQ = RCV.NXT`                               |
    | 0       | > 0     | `RCV.NXT ≤ SEG.SEQ < RCV.NXT + RCV.WND`           |
    | > 0     | 0       | not acceptable                                    |
    | > 0     | > 0     | start or end of segment falls within the window   |

    All comparisons use `SeqNum.le` / `SeqNum.lt` (modular, circular). -/
def segmentAcceptable (tcb : Tcb) (seg : Segment) : Bool :=
  let segLen := seg.len
  let wnd := tcb.rcvWnd
  if segLen == 0 then
    if wnd == 0 then
      -- Zero-length segment, zero window: must be exactly at RCV.NXT
      seg.seq == tcb.rcvNxt
    else
      -- Zero-length segment, open window: SEG.SEQ in [RCV.NXT, RCV.NXT + RCV.WND)
      SeqNum.le tcb.rcvNxt seg.seq && SeqNum.lt seg.seq (tcb.rcvNxt.add wnd.toUInt32)
  else
    if wnd == 0 then
      -- Data-bearing segment, zero window: never acceptable
      false
    else
      -- Data-bearing segment, open window: start or end in window
      let wndEnd := tcb.rcvNxt.add wnd.toUInt32
      let startInWnd := SeqNum.le tcb.rcvNxt seg.seq && SeqNum.lt seg.seq wndEnd
      let lastSeq := seg.seq.add (segLen - 1)
      let endInWnd := SeqNum.le tcb.rcvNxt lastSeq && SeqNum.lt lastSeq wndEnd
      startInWnd || endInWnd

-- ============================================================================
-- ACK Acceptability — RFC 793 §3.9 fifth check
-- ============================================================================

/-- ACK acceptability for ESTABLISHED and later states.
    RFC 793 §3.9 fifth check, ESTABLISHED:
    `SND.UNA < SEG.ACK ≤ SND.NXT`

    Strict inequality on the left: `SEG.ACK = SND.UNA` is a duplicate ACK. -/
def ackAcceptable (tcb : Tcb) (seg : Segment) : Bool :=
  SeqNum.lt tcb.sndUna seg.ackNum && SeqNum.le seg.ackNum tcb.sndNxt

/-- ACK acceptability for SYN-RECEIVED state.
    RFC 793 §3.9 fifth check, SYN-RECEIVED:
    `SND.UNA ≤ SEG.ACK ≤ SND.NXT`

    Non-strict inequality on the left: the ACK may equal `SND.UNA` (which is
    ISS in SYN-RECEIVED). -/
def ackAcceptableSynRecv (tcb : Tcb) (seg : Segment) : Bool :=
  SeqNum.le tcb.sndUna seg.ackNum && SeqNum.le seg.ackNum tcb.sndNxt

-- ============================================================================
-- Lemmas
-- ============================================================================

/-- A zero-length segment with zero window is acceptable iff `SEG.SEQ = RCV.NXT`.
    RFC 793 §3.3 table, row 1. -/
theorem segmentAcceptable_zero_zero (tcb : Tcb) (seg : Segment)
    (hLen : seg.len = 0) (hWnd : tcb.rcvWnd = 0) :
    segmentAcceptable tcb seg = (seg.seq == tcb.rcvNxt) := by
  simp [segmentAcceptable, hLen, hWnd]

/-- A data-bearing segment is never acceptable when the receive window is zero.
    RFC 793 §3.3 table, row 3. -/
theorem segmentAcceptable_data_zeroWnd (tcb : Tcb) (seg : Segment)
    (hLen : seg.len ≠ 0) (hWnd : tcb.rcvWnd = 0) :
    segmentAcceptable tcb seg = false := by
  simp [segmentAcceptable, hWnd]
  intro h
  exact absurd h hLen

/-- If an ESTABLISHED-style ACK is acceptable and `SND.UNA` is advanced to
    `SEG.ACK`, the new `SND.UNA ≤ SND.NXT` still holds. -/
theorem ackAcceptable_preserves_invariant (tcb : Tcb) (seg : Segment)
    (h : ackAcceptable tcb seg = true) :
    SeqNum.le seg.ackNum tcb.sndNxt = true := by
  simp [ackAcceptable] at h
  exact h.2

/-- SYN-RECEIVED ACK acceptability implies the ACK does not exceed SND.NXT. -/
theorem ackAcceptableSynRecv_le_sndNxt (tcb : Tcb) (seg : Segment)
    (h : ackAcceptableSynRecv tcb seg = true) :
    SeqNum.le seg.ackNum tcb.sndNxt = true := by
  simp [ackAcceptableSynRecv] at h
  exact h.2

end Tcp
