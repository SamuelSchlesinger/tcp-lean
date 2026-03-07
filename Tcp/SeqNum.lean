import Std.Tactic.BVDecide

/-!
# Sequence Number Arithmetic

Modular 32-bit sequence number type and arithmetic operations for TCP.

RFC 793 §3.3 defines sequence numbers as unsigned 32-bit integers with modular
arithmetic. The comparison relation uses a circular half-space: `a < b` iff
`b` is strictly ahead of `a` within the forward 2³¹ window. This makes the
relation a strict partial order (irreflexive, transitive within the half-space)
that is decidable but not total — when two numbers differ by exactly 2³¹,
neither is "less than" the other.
-/

namespace Tcp

/-- A TCP sequence number: a 32-bit unsigned integer with modular arithmetic.
    RFC 793 §3.3: "It is essential to remember that the actual sequence number
    space is finite, though very large." -/
structure SeqNum where
  val : UInt32
deriving DecidableEq, Repr, BEq

instance : Inhabited SeqNum where
  default := ⟨0⟩

namespace SeqNum

/-- Half the sequence number space: 2³¹. Used for the circular comparison. -/
def halfSpace : UInt32 := 2147483648  -- 2^31

/-- Advance a sequence number by `n` positions (modular addition).
    RFC 793 §3.3: all arithmetic on sequence numbers is modulo 2³². -/
def add (a : SeqNum) (n : UInt32) : SeqNum :=
  ⟨a.val + n⟩

/-- The unsigned distance from `a` to `b` in the forward direction (modular).
    `diff b a` gives how far `b` is ahead of `a` modulo 2³². -/
def diff (b a : SeqNum) : UInt32 :=
  b.val - a.val

/-- Circular less-than: `a < b` iff `b` is strictly ahead of `a` within the
    forward half-space. Equivalently, `(b.val - a.val) mod 2³²` is in the
    range `(0, 2³¹)`.

    RFC 793 §3.3: "A new acknowledgment (called an 'acceptable ack'), is one
    for which the inequality below holds: SND.UNA < SEG.ACK =< SND.NXT"
    — these comparisons use the circular order. -/
def lt (a b : SeqNum) : Bool :=
  let d := b.val - a.val
  d != 0 && d < halfSpace

/-- Circular less-than-or-equal: `a ≤ b` iff `a < b` or `a = b`. -/
def le (a b : SeqNum) : Bool :=
  a.val == b.val || lt a b

instance : LT SeqNum where
  lt a b := lt a b = true

instance : LE SeqNum where
  le a b := le a b = true

instance instDecLt (a b : SeqNum) : Decidable (a < b) :=
  inferInstanceAs (Decidable (lt a b = true))

instance instDecLe (a b : SeqNum) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (le a b = true))

-- ============================================================================
-- UInt32 helper lemma for modular arithmetic reasoning
-- ============================================================================

/-- `(a + b) - a = b` in modular arithmetic. -/
@[simp]
theorem UInt32.add_sub_self (a b : UInt32) : (a + b) - a = b := by
  apply UInt32.eq_of_toBitVec_eq
  simp [UInt32.toBitVec_add, UInt32.toBitVec_sub]
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

-- ============================================================================
-- Properties of the circular less-than relation
-- ============================================================================

/-- `SeqNum.lt` is irreflexive: no sequence number is less than itself.
    This follows because `a.val - a.val = 0`, and `lt` requires `d ≠ 0`. -/
theorem lt_irrefl (a : SeqNum) : lt a a = false := by
  simp [lt]

/-- `a < b` implies `a ≠ b`. -/
theorem ne_of_lt {a b : SeqNum} (h : lt a b = true) : a ≠ b := by
  intro hab
  subst hab
  simp [lt_irrefl] at h

/-- `le a a` for all sequence numbers. -/
theorem le_refl (a : SeqNum) : le a a = true := by
  simp [le]

/-- If `a = b` then `le a b`. -/
theorem le_of_eq {a b : SeqNum} (h : a = b) : le a b = true := by
  subst h; exact le_refl a

/-- `lt a b → le a b`. -/
theorem le_of_lt {a b : SeqNum} (h : lt a b = true) : le a b = true := by
  simp [le, h]

-- ============================================================================
-- Arithmetic interaction lemmas
-- ============================================================================

/-- Adding zero is the identity. -/
@[simp]
theorem add_zero (a : SeqNum) : a.add 0 = a := by
  simp [add]

/-- `diff a a = 0`. -/
@[simp]
theorem diff_self (a : SeqNum) : diff a a = 0 := by
  simp [diff]

/-- Adding 1 moves strictly forward in the circular space. -/
@[simp]
theorem lt_add_one (a : SeqNum) : lt a (a.add 1) = true := by
  simp only [lt, add, halfSpace]
  simp [UInt32.add_sub_self]

/-- `le a (a.add 1)` for all sequence numbers. -/
@[simp]
theorem le_add_one (a : SeqNum) : le a (a.add 1) = true := by
  simp [le, lt_add_one]

-- ============================================================================
-- Transitivity within the half-space
-- ============================================================================

/-- `SeqNum.lt` is transitive within the half-space: if `a < b` and `b < c`
    and the total forward span from `a` to `c` fits within the half-space,
    then `a < c`.

    The span condition is necessary because the circular space can wrap:
    without it, `a < b < c` could have `c` behind `a` in the full circle.
    RFC 793 §3.3. -/
theorem lt_trans {a b c : SeqNum}
    (hab : lt a b = true) (hbc : lt b c = true)
    (hspan : diff c a < halfSpace) :
    lt a c = true := by
  simp only [lt, diff, halfSpace,
    Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at *
  bv_decide

-- ============================================================================
-- Trichotomy within the half-space
-- ============================================================================

/-- `SeqNum.lt` is trichotomous within the half-space: for any `a, b` where
    neither `a - b` nor `b - a` equals exactly `2³¹`, exactly one of
    `a < b`, `a = b`, `b < a` holds.

    The exclusion of the `2³¹` case is necessary because at exactly half the
    circle, neither direction is "forward." RFC 793 §3.3. -/
theorem lt_trichotomy (a b : SeqNum)
    (hne1 : diff a b ≠ halfSpace)
    (hne2 : diff b a ≠ halfSpace) :
    lt a b = true ∨ a = b ∨ lt b a = true := by
  simp only [lt, diff, halfSpace,
    Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at *
  bv_decide

end SeqNum

end Tcp
