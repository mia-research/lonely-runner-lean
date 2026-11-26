import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Cascade
import Fresh.SelfMoverCommon
import Fresh.SelfMoverAllCommon
import Fresh.RatioLanding
import Fresh.APLawR4_I1_4_Arr
import Fresh.APLawR4_Interior

/-!
# All six interior subjects, speeds within `1/8` of the AP

Written 2026-10-23.  New file.  Speeds `v i` with `|v i - (c + i)| <= 1/8` (relative readings within `1/4`).  Subjects 1 and 6: `apLawR4_I1_4_end_1`, `apLawR4_I1_4_end_6` (18-leaf chamber tree).
Subjects 2 to 5: the ratio condition (`ap_interior_firstIso_d` at `δ = 1/8`, its largest radius).  The end subjects 0 and 7 are not covered here.  Grades: [L].
-/

open Classical

namespace Fresh.OneMover

open Fresh

theorem ap_interior_firstIso_8 (c : ℝ) (v : Fin 8 → ℝ) (hv : ∀ i : Fin 8, |v i - (c + ((i : ℕ) : ℝ))| ≤ 1 / 8) (k : Fin 8)
    (hk0 : k ≠ 0) (hk7 : k ≠ 7) : ∃ T : ℝ, 0 < T ∧ FirstIso v k T := by
  by_cases h1 : k = 1
  · subst h1
    obtain ⟨T, hT, hF, _⟩ := apLawR4_I1_4_end_1 c v hv
    exact ⟨T, hT, hF⟩
  by_cases h6 : k = 6
  · subst h6
    obtain ⟨T, hT, hF, _⟩ := apLawR4_I1_4_end_6 c v hv
    exact ⟨T, hT, hF⟩
  obtain ⟨m, hm, _, _, hF⟩ := ap_interior_firstIso_d c (1 / 8) le_rfl v hv k hk0 h1 h6 hk7
  exact ⟨1 / (8 * m), by positivity, hF⟩

theorem ap_interior_lands_8 (c : ℝ) (v : Fin 8 → ℝ) (hv : ∀ i : Fin 8, |v i - (c + ((i : ℕ) : ℝ))| ≤ 1 / 8) (k : Fin 8)
    (hk0 : k ≠ 0) (hk7 : k ≠ 7) : ∃ j : Fin 8, j ≠ k ∧ Lands v k |v j - v k| := by
  by_cases h1 : k = 1
  · subst h1
    obtain ⟨T, hT, hF, _⟩ := apLawR4_I1_4_end_1 c v hv
    refine ⟨0, by decide, lands_of_first v 1 _ T ?_ hT hF⟩
    exact Finset.mem_image.mpr ⟨0, Finset.mem_erase.mpr ⟨by decide, Finset.mem_univ _⟩, rfl⟩
  by_cases h6 : k = 6
  · subst h6
    obtain ⟨T, hT, hF, _⟩ := apLawR4_I1_4_end_6 c v hv
    refine ⟨7, by decide, lands_of_first v 6 _ T ?_ hT hF⟩
    exact Finset.mem_image.mpr ⟨7, Finset.mem_erase.mpr ⟨by decide, Finset.mem_univ _⟩, rfl⟩
  obtain ⟨m, hm, ⟨j, hjk, hjm⟩, hL⟩ := ap_interior_lands_d c (1 / 8) le_rfl v hv k hk0 h1 h6 hk7
  exact ⟨j, hjk, by rw [hjm]; exact hL⟩

#print axioms ap_interior_firstIso_8
#print axioms ap_interior_lands_8

end Fresh.OneMover
