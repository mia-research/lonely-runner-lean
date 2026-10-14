import LonelyRunner.LRC.Spec.CoreWindowRunN

#print axioms LRC.CoreWindowRun.used_zone_covers
#print axioms LRC.CoreWindowRun.zone_label_unique
#print axioms LRC.CoreWindowRun.inserted_zone_used
#print axioms LRC.CoreWindowRun.window_forces_used_zone
#print axioms LRC.CoreWindowRun.window_forces_iterate_zone
#print axioms LRC.CoreWindowRun.core_gap_contains_zone
#print axioms LRC.CoreWindowRun.different_components_different_labels
#print axioms LRC.CoreWindowRun.labels_ordered

namespace LRC.CoreWindowRun.Regression
open MomentIterationN ConstructionN

/-- A singleton at the first core opening is still a forced used zone. -/
theorem singleton_window :
    ∃ K : ℤ, ((8 : ℝ), K) ∈ [((8 : ℝ), (1 : ℤ))] ∧
      zoneLo 8 8 K < 1 / 8 ∧ (1 : ℝ) / 8 < zoneHi 8 8 K ∧
      ∀ J : ℤ, zoneLo 8 8 J < 1 / 8 → (1 : ℝ) / 8 < zoneHi 8 8 J → J = K := by
  apply window_forces_used_zone (S := {1}) (V := 8) (b := 1 / 8)
    (T := 9 / 64) (L := 1 / 8) (U := 1 / 8)
    (by norm_num) (by
      intro d hd
      have h : d = 1 := by simpa using hd
      rw [h]
      norm_num)
    (path := [(8, 1)])
  · norm_num [Run, zoneLo, zoneHi]
  · norm_num
  · norm_num
  · norm_num
  · intro t hl hu d hd
    have ht : t = 1 / 8 := le_antisymm hu hl
    have hd1 : d = 1 := by simpa using hd
    subst t d
    norm_num [circDist, Int.fract]

#print axioms singleton_window
end LRC.CoreWindowRun.Regression
