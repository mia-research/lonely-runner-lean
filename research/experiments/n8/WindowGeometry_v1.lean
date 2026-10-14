import Mathlib

/-!
# The window geometry of the divisor-closed problem

Two facts underlie the whole divisor-closed picture, and both are proved here.

**The clear set is a single interval.** A candidate `q` clears modulus `b` iff
`b ≤ 8*(q mod b) + 1 ≤ 7b`, i.e. iff the residue lies in `[L(b), U(b)]` with
`L(b) = ⌈(b-1)/8⌉` and `U(b) = ⌊(7b-1)/8⌋`. So the *blocked* set is its complement
`[0, L-1] ∪ [U+1, b-1]` — a single **cyclic interval centred on 0**, of radius about `b/8`.
Every obstacle in the problem sits at `0`.

**A window covers a full period of any proper divisor.** The window has width
`w(b) = U(b) - L(b) + 1`, and `2*w(b) ≥ b` for every `b ≥ 2`. Since a proper divisor satisfies
`b' ≤ b/2`, we get `b' ≤ w(b)`: the clear window of `b` always contains a complete period of
`b'`. That is what makes a nested, greedy construction down a divisor tower possible at all.

*(`2*w(b) ≥ b` checked for `b = 2..50000` before proving.)*

**What this does not yet give.** Greedy nesting down a divisor tower succeeds on
200,000/200,000 random towers and 50,894/50,894 exhaustive divisor towers, but the induction
is **not** closed: two length-only invariants were tried and both are refuted —
`|I| ≥ w(b)-1` fails at `b = 18, b' = 9`, and `|I| ≥ ⌈b/2⌉` fails at `b = 6, b' = 3`. The
surviving interval that greedy produces has a specific *position* inside `[L(b), U(b)]`, and a
length-only invariant discards precisely the information that makes the step work. The owed
piece is a **positional** invariant.

Ceilings and floors are carried as characterising inequalities, so no division convention is
relied on and the arithmetic stays inside `omega`.
-/

namespace WindowGeometry

/-- `Lb = ⌈(b-1)/8⌉`. -/
def IsCeilL (b Lb : ℤ) : Prop := 8 * Lb - 7 ≤ b - 1 ∧ b - 1 ≤ 8 * Lb

/-- `Ub = ⌊(7b-1)/8⌋`. -/
def IsFloorU (b Ub : ℤ) : Prop := 8 * Ub ≤ 7 * b - 1 ∧ 7 * b - 1 < 8 * Ub + 8

/-- **Clearing is exactly membership of the window.**  `b ≤ 8r+1 ≤ 7b ↔ L(b) ≤ r ≤ U(b)`. -/
theorem clear_iff_window {b Lb Ub r : ℤ} (hb : 2 ≤ b)
    (hL : IsCeilL b Lb) (hU : IsFloorU b Ub) :
    (b ≤ 8 * r + 1 ∧ 8 * r + 1 ≤ 7 * b) ↔ (Lb ≤ r ∧ r ≤ Ub) := by
  obtain ⟨hL1, hL2⟩ := hL
  obtain ⟨hU1, hU2⟩ := hU
  constructor <;> (intro h; omega)

/-- **So the blocked set is the cyclic ball around `0`.**  A residue is blocked exactly when it
is below `L(b)` or above `U(b)` — that is, within about `b/8` of `0` cyclically. -/
theorem blocked_iff_near_zero {b Lb Ub r : ℤ} (hb : 2 ≤ b)
    (hL : IsCeilL b Lb) (hU : IsFloorU b Ub) (hr : 0 ≤ r) (hrb : r < b) :
    ¬ (Lb ≤ r ∧ r ≤ Ub) ↔ (r < Lb ∨ Ub < r) := by
  constructor
  · intro h; by_contra hc; push_neg at hc; exact h ⟨hc.1, hc.2⟩
  · rintro (h | h) ⟨h1, h2⟩ <;> omega

/-- **The window is at least half the modulus.**  `2*w(b) ≥ b` for every `b ≥ 2`. -/
theorem window_ge_half {b Lb Ub : ℤ} (hb : 2 ≤ b)
    (hL : IsCeilL b Lb) (hU : IsFloorU b Ub) :
    b ≤ 2 * (Ub - Lb + 1) := by
  obtain ⟨hL1, hL2⟩ := hL
  obtain ⟨hU1, hU2⟩ := hU
  by_cases h : b ≤ 3
  · interval_cases b <;> omega
  · omega

/-- A proper divisor is at most half. -/
theorem proper_divisor_le_half {b b' : ℤ} (hb' : 0 < b') (hlt : b' < b) (hdvd : b' ∣ b) :
    2 * b' ≤ b := by
  obtain ⟨k, rfl⟩ := hdvd
  have hk : 2 ≤ k := by nlinarith
  nlinarith

/-- **A window covers a full period of any proper divisor.**  This is the geometric fact that
makes a nested construction down a divisor tower possible: the clear interval of `b` is wide
enough to contain a complete residue cycle of `b'`. -/
theorem window_covers_divisor {b b' Lb Ub : ℤ} (hb : 2 ≤ b) (hb' : 0 < b')
    (hlt : b' < b) (hdvd : b' ∣ b) (hL : IsCeilL b Lb) (hU : IsFloorU b Ub) :
    b' ≤ Ub - Lb + 1 := by
  have h1 : 2 * b' ≤ b := proper_divisor_le_half hb' hlt hdvd
  have h2 : b ≤ 2 * (Ub - Lb + 1) := window_ge_half hb hL hU
  omega

end WindowGeometry

#print axioms WindowGeometry.clear_iff_window
#print axioms WindowGeometry.blocked_iff_near_zero
#print axioms WindowGeometry.window_ge_half
#print axioms WindowGeometry.proper_divisor_le_half
#print axioms WindowGeometry.window_covers_divisor
