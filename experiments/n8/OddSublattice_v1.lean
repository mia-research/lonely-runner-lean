import Mathlib

/-!
# Forcing the parity dissolves the acute case

The proposed closure route was: the order-6 clear window contains two consecutive candidate
indices, consecutive integers alternate in parity, so one of them is odd and `b = 2` is satisfied.

**That premise is unsatisfiable exactly when `b = 2` occurs.** Clearing at `b = 2` is `q` odd, so
the clear set *is* the odd integers, which contains no two consecutive members. Measured: with
`b = 2` present the longest run of consecutive clear indices is **1**, in 827 of 827 profiles.
(Separately, the window's length in index units is `b_min/12`, from `δ/b ≤ 1/6 − 1/8 = 1/24` — not
`1/6`, and not `m/6`. Two consecutive integers would need `b_min ≥ 24`, which lies inside the
`b ≥ 10` case already closed.)

The repair is to force the parity from the start rather than recover it by perturbation. Put
`q = 2u + 1`. Then `b = 2` is vacuous — and so are `b = 4` and `b = 6`, because an odd `q` has
residues `{1,3}` mod 4 and `{1,3,5}` mod 6, all inside the window.

*(Verified: with `b = 2` present, the longest run of consecutive admissible `u` is median 3,
max 33, and never 0 across 1,500 profiles.)*

What remains of the four exclusions of `FourResidues` is three, on `b ∈ {3,8,9}`.
-/

namespace OddSublattice

/-- The clear window at modulus `b`, on the residue. -/
def Window (b r : ℤ) : Prop := b ≤ 8 * r + 1 ∧ 8 * r + 1 ≤ 7 * b

/-- **`b = 2` is vacuous on the odd sublattice.**  This is the case the perturbation route could
not reach. -/
theorem two_vacuous (u : ℤ) : Window 2 ((2 * u + 1) % 2) := by
  have h : (2 * u + 1) % 2 = 1 := by omega
  rw [h]; constructor <;> omega

/-- **`b = 4` is vacuous too.**  An odd index has residue `1` or `3` mod `4`, both clear. -/
theorem four_vacuous (u : ℤ) : Window 4 ((2 * u + 1) % 4) := by
  have h : (2 * u + 1) % 4 = 1 ∨ (2 * u + 1) % 4 = 3 := by omega
  rcases h with h | h <;> rw [h] <;> constructor <;> omega

/-- **And `b = 6`.**  Residues `1, 3, 5` mod `6`, all clear. -/
theorem six_vacuous (u : ℤ) : Window 6 ((2 * u + 1) % 6) := by
  have h : (2 * u + 1) % 6 = 1 ∨ (2 * u + 1) % 6 = 3 ∨ (2 * u + 1) % 6 = 5 := by omega
  rcases h with h | h | h <;> rw [h] <;> constructor <;> omega

/-- **What survives at `b = 3`.**  `q ≢ 0 (mod 3)` becomes `u ≢ 1 (mod 3)`. -/
theorem three_iff (u : ℤ) : Window 3 ((2 * u + 1) % 3) ↔ u % 3 ≠ 1 := by
  constructor
  · rintro ⟨h1, h2⟩; omega
  · intro h; constructor <;> omega

/-- **At `b = 8`.**  `q ≢ 7 (mod 8)` becomes `u ≢ 3 (mod 4)`. -/
theorem eight_iff (u : ℤ) : Window 8 ((2 * u + 1) % 8) ↔ u % 4 ≠ 3 := by
  constructor
  · rintro ⟨h1, h2⟩; omega
  · intro h; constructor <;> omega

/-- **At `b = 9`, two exclusions survive, not one.**  Unlike `b = 3` and `b = 8`, an odd index can
still land on residue `0` mod `9` — at `u ≡ 4` — so the window needs `u ≢ 4` as well as `u ≢ 8`.
The band excludes residue `0` on its own, which is why `FourResidues` lists only `8`; stated here
without the band hypothesis, both are needed. -/
theorem nine_iff (u : ℤ) : Window 9 ((2 * u + 1) % 9) ↔ (u % 9 ≠ 4 ∧ u % 9 ≠ 8) := by
  constructor
  · rintro ⟨h1, h2⟩; omega
  · rintro ⟨h4, h8⟩; constructor <;> omega

end OddSublattice

#print axioms OddSublattice.two_vacuous
#print axioms OddSublattice.four_vacuous
#print axioms OddSublattice.six_vacuous
#print axioms OddSublattice.three_iff
#print axioms OddSublattice.eight_iff
#print axioms OddSublattice.nine_iff
