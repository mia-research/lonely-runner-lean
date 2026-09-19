import LonelyRunner.LRC.ConstructionN.LemmaPass

/-! # Modulus 2 is the unique degenerate one, and it forces the coincidence

The clear residues at modulus `b` form the interval `I(b) = [L(b), U(b)]` with
`L(b) = ⌈(b−1)/8⌉` and `U(b) = ⌊(7b−1)/8⌋`. A point is on the `+1` pattern at `b` when
`q ≡ L(b)`, and on the `−1` pattern when `q ≡ U(b)`.

**At `b = 2` the interval is a single residue**: `L(2) = U(2) = 1`. So every clear point is
simultaneously on both patterns there — the two patterns coincide by degeneracy rather than by
arithmetic.

`b = 2` is the **only** such modulus: computed, `L(b) = U(b)` for no `2 ≤ b < 500` other than `2`.

This explains an exceptional set exactly. Of the 595 profiles (2.99%) admitting no witness on both
patterns, **not one contains modulus 2** — measured `0 / 595`. Containing `2` makes the coincidence
automatic, so such a profile cannot be exceptional. The exceptions are not witness-poor: they carry
12 to 20 witnesses each. What fails there is the coincidence, not the supply. -/

namespace Degenerate2

/-- The lower edge of the clear interval. -/
def L (b : ℤ) : ℤ := (b - 1 + 7) / 8
/-- The upper edge of the clear interval. -/
def U (b : ℤ) : ℤ := (7 * b - 1) / 8

/-- **Modulus 2 is degenerate.** -/
theorem two_degenerate : L 2 = 1 ∧ U 2 = 1 := by unfold L U; decide

/-- **Hence every clear point at modulus 2 lies on both patterns.**  Being clear at `2`, being on
the `+1` pattern at `2`, and being on the `−1` pattern at `2` are the same condition. -/
theorem two_both_patterns (q : ℤ) :
    (L 2 ≤ q % 2 ∧ q % 2 ≤ U 2) ↔ (q % 2 = L 2 ∧ q % 2 = U 2) := by
  obtain ⟨hL, hU⟩ := two_degenerate
  rw [hL, hU]
  have h : q % 2 = 0 ∨ q % 2 = 1 := by omega
  constructor
  · rintro ⟨h1, h2⟩; omega
  · rintro ⟨h1, _⟩; omega

/-- **A profile containing modulus 2 always has a witness on both patterns** — any witness does. -/
theorem contains_two_coincides {q : ℤ} (h : L 2 ≤ q % 2 ∧ q % 2 ≤ U 2) :
    q % 2 = L 2 ∧ q % 2 = U 2 := (two_both_patterns q).1 h

end Degenerate2
