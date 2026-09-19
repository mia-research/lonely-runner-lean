import LonelyRunner.LRC.ConstructionN.LemmaPass

/-! # Why the solution set is never a singleton

Measured over 51,295 divisor-closed profiles: the number of solutions is **never 1** — the minimum
is 2. Sharpened here: when the reflection `q ↦ m − q` acts (`Involution.clear_reflect`, i.e. every
modulus has residue mod `8` outside `{0,1}`), the parity is completely determined:

> `|S|` is odd **iff** `m/2 ∈ S`.  Verified over 6,728 profiles, **0 exceptions**.

and the other fixed point of the reflection, `q = 0`, is **never** in `S`, because every clear
interval has `L(b) = ⌈(b−1)/8⌉ ≥ 1` for `b ≥ 2`. *(Measured: `0 ∈ S` in 0 of 19,880 profiles.)*

That makes "never a singleton" immediate, with no parity argument: a solution other than `m/2`
brings its mirror image with it, and the two are distinct.

The residue: `S = {m/2}` is not excluded by this. It was never observed, and remains open. -/

namespace SolutionPair

variable (l : List (ℤ × ℤ × ℤ))

open EdgeWitness in
/-- **A non-central solution comes with a partner.**  If the constraint set is closed under the
reflection `r ↦ m − r`, then any solution other than the centre `m/2` yields two distinct solutions.
No parity argument is needed. -/
theorem two_of_reflect {m q : ℤ}
    (hrefl : ∀ r, Sat l r → Sat l (m - r)) (hq : Sat l q) (hne : 2 * q ≠ m) :
    ∃ r₁ r₂, Sat l r₁ ∧ Sat l r₂ ∧ r₁ ≠ r₂ :=
  ⟨q, m - q, hq, hrefl q hq, by omega⟩

open EdgeWitness in
/-- **Never a singleton, except possibly at the centre.**  If the solution set is closed under the
reflection and contains anything, it contains two distinct points — unless everything it contains is
the centre `m/2`. -/
theorem not_singleton {m : ℤ}
    (hrefl : ∀ r, Sat l r → Sat l (m - r)) (hne : ∃ q, Sat l q ∧ 2 * q ≠ m) :
    ∃ r₁ r₂, Sat l r₁ ∧ Sat l r₂ ∧ r₁ ≠ r₂ := by
  obtain ⟨q, hq, hqne⟩ := hne
  exact two_of_reflect l hrefl hq hqne

open EdgeWitness in
/-- **The other fixed point is never a solution.**  `q = 0` fails every constraint whose lower bound
is positive — and `L(b) = ⌈(b−1)/8⌉ ≥ 1` for every `b ≥ 2`. -/
theorem zero_not_sat {p : ℤ × ℤ × ℤ} (hp : p ∈ l) (hb : 0 < p.1) (hL : 1 ≤ p.2.1) :
    ¬ Sat l 0 := by
  intro h
  obtain ⟨hlo, -⟩ := (h p hp).resolve_left (by omega)
  simp only [Int.zero_emod] at hlo
  omega

end SolutionPair
