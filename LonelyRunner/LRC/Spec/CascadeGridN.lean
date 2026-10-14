import LonelyRunner.LRC.Spec.RegimeSkeletonN
import LonelyRunner.LRC.Cascade.Iteration

/-!
# Grid certificates bound the actual cascade

This connects the proposed grid certificate to the existing iteration, without assuming
that each exit has only one new blocker. Coverage of arbitrary seven-reading arrangements
is still an unproved hypothesis; these theorems do not establish that coverage.
-/

namespace LRC.CascadeGrid

open MomentIterationN LRC.RegimeSkeleton

/-- A half-nearest-step grid certificate bounds every cascade iterate, including all failed
handoffs, by `15/(8*m)`. No restriction on the number of simultaneous blockers is needed. -/
theorem iterates_bounded_of_gridStep8_two {S : Finset ℕ} {m : ℕ}
    (hpos : ∀ d ∈ S, 0 < d) (hmS : m ∈ S) (hg : GridStep8 S m 2) :
    ∀ N : ℕ, (move 8 (S.image (fun d : ℕ => (d : ℝ))))^[N] (1 / (8 * m)) ≤
      15 / (8 * m) := by
  classical
  obtain ⟨t, ht, hlo, hhi, hl⟩ := gridStep8_two_bounded hpos hmS hg
  have hm : (0 : ℝ) < m := by exact_mod_cast hpos m hmS
  have hp : ∀ d ∈ S.image (fun d : ℕ => (d : ℝ)), 0 < d := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
    exact_mod_cast hpos a ha
  have hLonely : Lonely 8 (S.image (fun d : ℕ => (d : ℝ))) t := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
    exact hl a ha
  have hb : 1 / (8 * (m : ℝ)) ≤ t := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  have hu : t ≤ 15 / (8 * (m : ℝ)) := (le_div_iff₀ (by positivity)).mpr (by nlinarith)
  intro N
  exact le_trans (iterate_le_of_lonely hp hLonely hb N) hu

/-- The same certificate makes the existing cascade stop at a lonely fixed point within
that bound. The certificate remains an explicit premise, not a proved covering theorem. -/
theorem fixed_of_gridStep8_two {S : Finset ℕ} {m : ℕ}
    (hpos : ∀ d ∈ S, 0 < d) (hmS : m ∈ S) (hg : GridStep8 S m 2) :
    ∃ N : ℕ,
      let t := (move 8 (S.image (fun d : ℕ => (d : ℝ))))^[N] (1 / (8 * m))
      move 8 (S.image (fun d : ℕ => (d : ℝ))) t = t ∧
      t ≤ 15 / (8 * m) ∧ Lonely 8 (S.image (fun d : ℕ => (d : ℝ))) t := by
  classical
  obtain ⟨t, ht, _, _, hl⟩ := gridStep8_two_bounded hpos hmS hg
  have hp : ∀ d ∈ S.image (fun d : ℕ => (d : ℝ)), 0 < d := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
    exact_mod_cast hpos a ha
  have hLonely : Lonely 8 (S.image (fun d : ℕ => (d : ℝ))) t := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
    exact hl a ha
  obtain ⟨N, hN⟩ := exists_fixed_of_lonely hp
    (Finset.mem_image.mpr ⟨m, hmS, rfl⟩) ht hLonely
  exact ⟨N, hN, iterates_bounded_of_gridStep8_two hpos hmS hg N, lonely_of_fixed hp hN⟩

end LRC.CascadeGrid
