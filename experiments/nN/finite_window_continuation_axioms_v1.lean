import LonelyRunner.LRC.Spec.FiniteWindowContinuationN

#print axioms LRC.FiniteWindowContinuation.lap_bound
#print axioms LRC.FiniteWindowContinuation.deformation_bound
#print axioms LRC.FiniteWindowContinuation.affine_region_closed
#print axioms LRC.FiniteWindowContinuation.finite_regions_closed
#print axioms LRC.FiniteWindowContinuation.endpoint_of_finite_coverage
#print axioms LRC.FiniteWindowContinuation.endpoint_lap_window
#print axioms LRC.FiniteWindowContinuation.endpoint_of_bounded_witnesses

namespace LRC.FiniteWindowContinuation.Regression

/-- A closed singleton endpoint is retained; no positive margin is assumed. -/
theorem zero_margin_endpoint :
    ∃ q ∈ ({0} : Finset ℕ), ∀ _i : Fin 1, (0 : ℝ) ≤ 1 + 1 * (-1) := by
  apply endpoint_of_finite_coverage ({0} : Finset ℕ)
    (fun _ (_ : Fin 1) => (1 : ℝ)) (fun _ (_ : Fin 1) => (-1 : ℝ))
    (l := 0) (r := 1) (by norm_num)
  intro s hs
  refine ⟨0, by simp, fun _ => ?_⟩
  linarith [hs.2]

/-- Coverage at the limit does not imply any coverage beyond it. -/
theorem no_right_extension {s : ℝ} (hs : 1 < s) :
    ¬ (0 : ℝ) ≤ 1 + s * (-1) := by linarith

/-- Interior readings at endpoints 1 and 7 retain their closed clear edges. -/
theorem closed_band_edges :
    (1 : ℝ) / 8 ≤ 1 * (1 / 8) ∧ (7 : ℝ) * (1 / 8) ≤ 7 / 8 := by norm_num

#print axioms zero_margin_endpoint
#print axioms no_right_extension
#print axioms closed_band_edges

end LRC.FiniteWindowContinuation.Regression
