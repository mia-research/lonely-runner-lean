import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Cascade
import Fresh.SelfMoverCommon
import Fresh.SelfMoverAllCommon
import Fresh.RatioLanding
import Fresh.APLawR3_End8
import Fresh.APLawR3_Interior

/-!
# The AP-neighbourhood landing law, all eight subjects, speeds within `1/16`

Written 2026-10-23.  New file.  Speeds `v i` with `|v i - (c + i)| <= 1/16`.  End subjects (0, 7): `apLawR3_end0_speeds_8`, `apLawR3_end7_speeds_8` (relative radius `1/8`).  Interior subjects (1 to 6): `ap_interior_firstIso_max` (valid to speeds within `1/16`).
`ap_nbhd_firstIso_8`: every subject has a first isolation instant.  `ap_nbhd_lands_8`: for every subject there is a runner `j <> k` whose reading `|v j - v k|` satisfies `Lands v k`.  Grades: [L].
-/

open Classical

namespace Fresh.OneMover

open Fresh

theorem ap_nbhd_firstIso_8 (c : ℝ) (v : Fin 8 → ℝ) (hv : ∀ i : Fin 8, |v i - (c + ((i : ℕ) : ℝ))| ≤ 1 / 16) (k : Fin 8) :
    ∃ T : ℝ, 0 < T ∧ FirstIso v k T := by
  by_cases h0 : k = 0
  · subst h0
    obtain ⟨T, hT, hF, _⟩ := apLawR3_end0_speeds_8 c v hv
    exact ⟨T, hT, hF⟩
  by_cases h7 : k = 7
  · subst h7
    obtain ⟨T, hT, hF, _⟩ := apLawR3_end7_speeds_8 c v hv
    exact ⟨T, hT, hF⟩
  obtain ⟨m, hm, _, _, hF⟩ := ap_interior_firstIso_max c v (hv) k h0 h7
  exact ⟨1 / (8 * m), by positivity, hF⟩

theorem ap_nbhd_lands_8 (c : ℝ) (v : Fin 8 → ℝ) (hv : ∀ i : Fin 8, |v i - (c + ((i : ℕ) : ℝ))| ≤ 1 / 16) (k : Fin 8) :
    ∃ j : Fin 8, j ≠ k ∧ Lands v k |v j - v k| := by
  by_cases h0 : k = 0
  · subst h0
    obtain ⟨T, hT, hF, _⟩ := apLawR3_end0_speeds_8 c v hv
    refine ⟨1, by decide, lands_of_first v 0 _ T ?_ hT hF⟩
    exact Finset.mem_image.mpr ⟨1, Finset.mem_erase.mpr ⟨by decide, Finset.mem_univ _⟩, rfl⟩
  by_cases h7 : k = 7
  · subst h7
    obtain ⟨T, hT, hF, _⟩ := apLawR3_end7_speeds_8 c v hv
    refine ⟨6, by decide, lands_of_first v 7 _ T ?_ hT hF⟩
    exact Finset.mem_image.mpr ⟨6, Finset.mem_erase.mpr ⟨by decide, Finset.mem_univ _⟩, rfl⟩
  obtain ⟨m, hm, ⟨j, hjk, hjm⟩, hL⟩ := ap_interior_lands_max c v (hv) k h0 h7
  exact ⟨j, hjk, by rw [hjm]; exact hL⟩

#print axioms ap_nbhd_firstIso_8
#print axioms ap_nbhd_lands_8

end Fresh.OneMover
