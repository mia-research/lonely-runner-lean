import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Defs
import LonelyRunner.LRC.SmallN.IntLRC_7_BS.PrimeFiltering

/-!
# n = 7 (Barajas–Serra) — Supporting Lemmas 5–9

Source: `sources_barajas_serra_2008.txt`, lines 364–506.

These lemmas provide the combinatorial tools used by the §6 case analysis
(|A|=5). Lemma 5 is the main pigeonhole for `ℓ(A₁)+ℓ(A₂)+ℓ(A₄) ≤ 5`.
-/

open Finset

namespace IntLRC7BS

/-- An interval `{a, a+1, ..., a+ℓ-1}` in `ZMod 7` avoids `{0, 6}` under shift `s·k`:
for each `j < ℓ`, `(a + j + s·k) ∉ {0, 6}`. -/
def intervalAvoids (a : ZMod 7) (ℓ : ℕ) (s k : ZMod 7) : Prop :=
  ∀ j : Fin ℓ, (a + (j.val : ZMod 7) + s * k) ∉ ({0, 6} : Finset (ZMod 7))

instance (a : ZMod 7) (ℓ : ℕ) (s k : ZMod 7) : Decidable (intervalAvoids a ℓ s k) :=
  inferInstanceAs (Decidable (∀ j : Fin ℓ, _))

set_option maxHeartbeats 3200000 in
/-- **Lemma 5, safe version (BS L388, sum ≤ 5, excluding 3 exceptional triples).**
Three intervals in ZMod 7 with total length ≤ 5 can be simultaneously shifted
(by `k`, `2k`, `4k`) to avoid `{0,6}`, unless `(ℓ₁,ℓ₂,ℓ₄) ∈ {(3,1,1),(1,3,1),(1,1,3)}`.
The excluded triples are BS's Lemma 5 exception; handled by Lemma 6. -/
theorem lemma5_avoids (a₁ a₂ a₄ : ZMod 7) (ℓ₁ ℓ₂ ℓ₄ : ℕ)
    (h₁ : ℓ₁ ≤ 5) (h₂ : ℓ₂ ≤ 5) (h₄ : ℓ₄ ≤ 5) (hsum : ℓ₁ + ℓ₂ + ℓ₄ ≤ 5)
    (hexc : ¬ (ℓ₁ = 3 ∧ ℓ₂ = 1 ∧ ℓ₄ = 1))
    (hexc2 : ¬ (ℓ₁ = 1 ∧ ℓ₂ = 3 ∧ ℓ₄ = 1))
    (hexc3 : ¬ (ℓ₁ = 1 ∧ ℓ₂ = 1 ∧ ℓ₄ = 3)) :
    ∃ k : ZMod 7,
      intervalAvoids a₁ ℓ₁ 1 k ∧
      intervalAvoids a₂ ℓ₂ 2 k ∧
      intervalAvoids a₄ ℓ₄ 4 k := by
  interval_cases ℓ₁ <;> interval_cases ℓ₂ <;> interval_cases ℓ₄ <;>
    simp_all (config := { decide := true }) [intervalAvoids] <;>
    revert a₁ a₂ a₄ <;> decide

/-- **Lemma 5 exceptional triple (3,1,1).** BS shows the `(ℓ₁,ℓ₂,ℓ₄)=(3,1,1)`
case fails only when `ẽ(d,d') = 2i - j ∈ {2,4}` (where `i = q(A₂)`, `j = q(A₄)`).
With that exception ruled out (`2·a₂ - a₄ ∉ {2,4}`), the avoidance holds. -/
theorem lemma5_avoids_311 (a₁ a₂ a₄ : ZMod 7)
    (hexc : (2 * a₂ - a₄) ∉ ({2, 4} : Finset (ZMod 7))) :
    ∃ k : ZMod 7,
      intervalAvoids a₁ 3 1 k ∧
      intervalAvoids a₂ 1 2 k ∧
      intervalAvoids a₄ 1 4 k := by
  revert hexc; revert a₁ a₂ a₄; decide

end IntLRC7BS
