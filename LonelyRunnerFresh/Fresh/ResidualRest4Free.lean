import Mathlib
import Fresh.Framework
import Fresh.ClusterWindowFree
import Fresh.CoreCoverFree

/-!
# The whole-number residual with the 53 frozen cores removed

Written 2026-10-26.  New file.  `ResidualRest4` is `ResidualRest3` restricted to the `EightResidual` sets that contain none of the 53 six-element cores of `CoreCover.coreList`
(`-- STANDING: OWED`).  `residualRest3_of_rest4`, `isolation_of_rest4`: with it, every ordered arrangement is isolated for every subject.
The 53 cores are those chosen to cover the 142 left-over sets of E639 at `N = 28` (`experiments/n8/core_cover_v1.out`); for each, every set containing it is lonely (`CoreCover.core_lonely_*`, from the generated families, `x ≥ 1` arbitrary).
Integer/commensurable statement.  Grade [L] modulo `ResidualRest4`.
-/

open Classical

namespace Fresh.ResidualRest4

open Fresh Fresh.ClusterWindow Fresh.CoreCover Fresh.ResidualDischarge Fresh.EightResidualOpen Fresh.EightResidualNative LRC.OrderEightN LRC.ParityDescent

-- STANDING: OWED
def ResidualRest4 : Prop :=
  ∀ R : Finset ℕ, (∀ d ∈ R, 0 < d) → EightResidual R →
    ¬ SettledCounts8' (R.filter (fun d => 8 ∣ d)).card (R.filter (fun d => ¬ 2 ∣ d)).card
        (R.filter (fun d => d % 4 = 2)).card (R.filter (fun d => d % 8 = 4)).card →
    ¬ OottCase8 R → ¬ ChainSet (R.image (fun d : ℕ => (d : ℝ))) → ¬ FixedRSet (R.image (fun d : ℕ => (d : ℝ))) →
    ¬ WindowChainSet (R.image (fun d : ℕ => (d : ℝ))) → ¬ CoversCore R →
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ R, (1 / 8 : ℝ) ≤ distInt ((d : ℝ) * t)

theorem residualRest3_of_rest4 (h : ResidualRest4) : ResidualRest3 := by
  intro R hpos hR hs ho hc hf hw
  by_cases hcv : CoversCore R
  · exact coversCore_lonely R hpos (by have := hR.card_eq; omega) hcv
  · exact h R hpos hR hs ho hc hf hw hcv

theorem isolation_of_rest4 (h : ResidualRest4) {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) (k : Fin 8) : Isolation v k :=
  isolation_of_rest3 (residualRest3_of_rest4 h) hv k

#print axioms residualRest3_of_rest4
#print axioms isolation_of_rest4

end Fresh.ResidualRest4
