import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.ResidualRest4Free

/-!
# Isolation at a flank instant with a bounded wrap, and the residual it removes

Written 2026-10-26.  New file.  Worklist tags: A07, G01, G02, H01 to H03 (the opener of a cascade is the flank of one disparity).  `FlankBandSet ds`: for some `e ∈ ds` and `n ≤ 12` every `d ∈ ds` has, at the flank
instant `t = (n + 1/8)/e`, the phase `p = d (8n + 1)/(8e)` in a clear band `N + 1/8 ≤ p ≤ N + 7/8` with `0 ≤ N ≤ n`.  Then `t` clears everything (`flankBandSet_lonely`).  The parameters are finite (`e` one of seven disparities, `n ≤ 12`,
`N ≤ n`), the instant is fixed by `e` and `n`, and membership is a finite inequality check, so this is a type and not the definition of isolation (E636 caution: a free real parameter would be).  It generalises `FirstLapClass` (all `N = 0`).
Observation (E641, whole-number sets, proxy): among the 224 sets left at `N = 36` (E639), 191 are in a `FlankBandSet`; with the 53 cores of E640 all but 5 are covered.
`ResidualRest5` is `ResidualRest4` with `FlankBandSet` also excluded (`-- STANDING: OWED`); `residualRest4_of_rest5`, `isolation_of_rest5`.  Integer/commensurable statement.  Grade [L] modulo `ResidualRest5`.
-/

open Classical

namespace Fresh.FlankBand

open Fresh Fresh.ClusterWindow Fresh.CoreCover Fresh.ResidualDischarge Fresh.EightResidualOpen Fresh.ResidualRest4 LRC.OrderEightN LRC.ParityDescent

-- STANDING: DEFINITION
def FlankBandSet (ds : Finset ℝ) : Prop :=
  ∃ e ∈ ds, 0 < e ∧ ∃ n : ℕ, n ≤ 12 ∧ ∀ d ∈ ds, ∃ N : ℕ, N ≤ n ∧ (N : ℝ) + 1 / 8 ≤ d * (8 * n + 1) / (8 * e) ∧
    d * (8 * n + 1) / (8 * e) ≤ (N : ℝ) + 7 / 8

theorem flankBandSet_lonely {ds : Finset ℝ} (h : FlankBandSet ds) : ∃ t : ℝ, 0 < t ∧ ∀ d ∈ ds, (1 / 8 : ℝ) ≤ distInt (d * t) := by
  obtain ⟨e, _, he, n, _, hall⟩ := h
  refine ⟨(8 * n + 1) / (8 * e), by positivity, fun d hd => ?_⟩
  obtain ⟨N, _, h1, h2⟩ := hall d hd
  have : d * ((8 * (n : ℝ) + 1) / (8 * e)) = d * (8 * n + 1) / (8 * e) := by ring
  rw [this]
  exact Fresh.Localisation.clear_of_window (N : ℤ) (by simpa using h1) (by simpa using h2)

-- STANDING: OWED
def ResidualRest5 : Prop :=
  ∀ R : Finset ℕ, (∀ d ∈ R, 0 < d) → EightResidual R →
    ¬ SettledCounts8' (R.filter (fun d => 8 ∣ d)).card (R.filter (fun d => ¬ 2 ∣ d)).card
        (R.filter (fun d => d % 4 = 2)).card (R.filter (fun d => d % 8 = 4)).card →
    ¬ OottCase8 R → ¬ ChainSet (R.image (fun d : ℕ => (d : ℝ))) → ¬ FixedRSet (R.image (fun d : ℕ => (d : ℝ))) →
    ¬ WindowChainSet (R.image (fun d : ℕ => (d : ℝ))) → ¬ CoversCore R → ¬ FlankBandSet (R.image (fun d : ℕ => (d : ℝ))) →
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ R, (1 / 8 : ℝ) ≤ distInt ((d : ℝ) * t)

theorem residualRest4_of_rest5 (h : ResidualRest5) : ResidualRest4 := by
  intro R hpos hR hs ho hc hf hw hcv
  by_cases hb : FlankBandSet (R.image (fun d : ℕ => (d : ℝ)))
  · obtain ⟨t, ht, hl⟩ := flankBandSet_lonely hb
    exact ⟨t, ht, fun d hd => hl (d : ℝ) (Finset.mem_image.2 ⟨d, hd, rfl⟩)⟩
  · exact h R hpos hR hs ho hc hf hw hcv hb

theorem isolation_of_rest5 (h : ResidualRest5) {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) (k : Fin 8) : Isolation v k :=
  isolation_of_rest4 (residualRest4_of_rest5 h) hv k

#print axioms flankBandSet_lonely
#print axioms isolation_of_rest5

-- STANDING: DEFINITION
def FlankListSet (ds : Finset ℝ) : Prop :=
  ∃ e ∈ ds, 0 < e ∧ ∃ n : ℕ, n ≤ 12 ∧ ∀ d ∈ ds, (1 / 8 : ℝ) ≤ distInt (d * ((8 * n + 1) / (8 * e)))

theorem flankListSet_lonely {ds : Finset ℝ} (h : FlankListSet ds) : ∃ t : ℝ, 0 < t ∧ ∀ d ∈ ds, (1 / 8 : ℝ) ≤ distInt (d * t) := by
  obtain ⟨e, _, he, n, _, hall⟩ := h
  exact ⟨(8 * n + 1) / (8 * e), by positivity, hall⟩

/-- `FlankListSet` is the flank instant `(n + 1/8)/e` of one disparity `e` with `n ≤ 12`, wraps unrestricted: a list of at most `7 * 13` instants per arrangement, fixed by the arrangement. -/
theorem flankBandSet_imp_flankListSet {ds : Finset ℝ} (h : FlankBandSet ds) : FlankListSet ds := by
  obtain ⟨e, he, hpos, n, hn, hall⟩ := h
  refine ⟨e, he, hpos, n, hn, fun d hd => ?_⟩
  obtain ⟨N, _, h1, h2⟩ := hall d hd
  have : d * ((8 * (n : ℝ) + 1) / (8 * e)) = d * (8 * n + 1) / (8 * e) := by ring
  rw [this]
  exact Fresh.Localisation.clear_of_window (N : ℤ) (by simpa using h1) (by simpa using h2)

-- STANDING: OWED
def ResidualRest6 : Prop :=
  ∀ R : Finset ℕ, (∀ d ∈ R, 0 < d) → EightResidual R →
    ¬ SettledCounts8' (R.filter (fun d => 8 ∣ d)).card (R.filter (fun d => ¬ 2 ∣ d)).card
        (R.filter (fun d => d % 4 = 2)).card (R.filter (fun d => d % 8 = 4)).card →
    ¬ OottCase8 R → ¬ ChainSet (R.image (fun d : ℕ => (d : ℝ))) → ¬ FixedRSet (R.image (fun d : ℕ => (d : ℝ))) →
    ¬ WindowChainSet (R.image (fun d : ℕ => (d : ℝ))) → ¬ CoversCore R → ¬ FlankListSet (R.image (fun d : ℕ => (d : ℝ))) →
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ R, (1 / 8 : ℝ) ≤ distInt ((d : ℝ) * t)

theorem residualRest5_of_rest6 (h : ResidualRest6) : ResidualRest5 := by
  intro R hpos hR hs ho hc hf hw hcv _
  by_cases hl : FlankListSet (R.image (fun d : ℕ => (d : ℝ)))
  · obtain ⟨t, ht, hl'⟩ := flankListSet_lonely hl
    exact ⟨t, ht, fun d hd => hl' (d : ℝ) (Finset.mem_image.2 ⟨d, hd, rfl⟩)⟩
  · exact h R hpos hR hs ho hc hf hw hcv hl

theorem isolation_of_rest6 (h : ResidualRest6) {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) (k : Fin 8) : Isolation v k :=
  isolation_of_rest5 (residualRest5_of_rest6 h) hv k

#print axioms flankListSet_lonely
#print axioms isolation_of_rest6

end Fresh.FlankBand
