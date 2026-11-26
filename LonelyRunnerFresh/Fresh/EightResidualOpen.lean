import Mathlib
import Fresh.Framework
import Fresh.EightResidualNative
import Fresh.ResidualDischarge
import Fresh.Nv_ResidueCasesTwoN

/-!
# The sharper whole-number residual: residue counts and the real chain/fixed-instant types removed

Written 2026-10-25.  New file.  `Nv_ResidueCasesTwoN` (ported; the owner's residue-count cases T1 to T10 and the `OottCase8` case) removes from `EightResidual` the sets whose residue counts are settled.
`ResidualRest2` is `ResidualLonely8` restricted to the `EightResidual` sets for which `SettledCounts8'` fails on their counts, `OottCase8` fails, and the set is in neither real class of `ResidualDischarge`
(`ChainSet`, `FixedRSet`).  `residualLonely8_of_rest2`: `ResidualRest2 → ResidualLonely8`.  Integer/commensurable statement.  `-- STANDING: OWED`.  Grade [L] modulo `ResidualRest2`.
-/

open Classical

namespace Fresh.EightResidualOpen

open Fresh Fresh.EightResidualNative Fresh.ResidualDischarge LRC.OrderEightN LRC.ParityDescent

-- STANDING: OWED
def ResidualRest2 : Prop :=
  ∀ R : Finset ℕ, (∀ d ∈ R, 0 < d) → EightResidual R →
    ¬ SettledCounts8' (R.filter (fun d => 8 ∣ d)).card (R.filter (fun d => ¬ 2 ∣ d)).card
        (R.filter (fun d => d % 4 = 2)).card (R.filter (fun d => d % 8 = 4)).card →
    ¬ OottCase8 R → ¬ ChainSet (R.image (fun d : ℕ => (d : ℝ))) → ¬ FixedRSet (R.image (fun d : ℕ => (d : ℝ))) →
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ R, (1 / 8 : ℝ) ≤ distInt ((d : ℝ) * t)

theorem residualRest_of_rest2 (h : ResidualRest2) : ResidualRest := by
  intro R hpos hR hc hf
  by_cases hs : SettledCounts8' (R.filter (fun d => 8 ∣ d)).card (R.filter (fun d => ¬ 2 ∣ d)).card
      (R.filter (fun d => d % 4 = 2)).card (R.filter (fun d => d % 8 = 4)).card ∨ OottCase8 R
  · obtain ⟨t, ht, hl⟩ := lonely_eight_of_settled_counts' hpos hs
    refine ⟨t, ht, fun d hd => ?_⟩
    have := hl d hd
    rw [Fresh.NativeOrders.circDist_eq] at this
    simpa using this
  · exact h R hpos hR (fun h1 => hs (Or.inl h1)) (fun h2 => hs (Or.inr h2)) hc hf

theorem residualLonely8_of_rest2 (h : ResidualRest2) : ResidualLonely8 :=
  residualLonely8_of_rest (residualRest_of_rest2 h)

theorem isolation_of_rest2 (h : ResidualRest2) {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) (k : Fin 8) : Isolation v k :=
  isolation_of_residual (residualLonely8_of_rest2 h) hv k

#print axioms residualLonely8_of_rest2
#print axioms isolation_of_rest2

end Fresh.EightResidualOpen
