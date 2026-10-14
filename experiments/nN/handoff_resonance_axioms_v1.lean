import LonelyRunner.LRC.Spec.HandoffResonanceN

#print axioms LRC.HandoffResonance.off_lattice_role_breaks
#print axioms LRC.HandoffResonance.persistent_role_integral
#print axioms LRC.HandoffResonance.persistent_schedule_common_lattice
#print axioms LRC.HandoffResonance.integral_phase_lap_transport
#print axioms LRC.HandoffResonance.isolation_in_resonant_pair_gap

-- Exact regression against a surviving zero-drift return in the experiment.
example : ∀ x ∈ ({(1 : ℝ), 23509 / 10000, 8103 / 2500, 52223 / 12500,
    52223 / 10000, 57871 / 10000, 17184527 / 2310000} : Finset ℝ),
    (8 : ℝ)⁻¹ ≤ circDist (x * (81250 / 57871)) := by
  have h := LRC.HandoffResonance.isolation_in_resonant_pair_gap
    (m := 1) (p := 23509 / 10000) (q := 8103 / 2500) (D := 52223 / 50000)
    (c := 57871 / 10000) (f := 17184527 / 2310000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hl := h.2
  norm_num at hl ⊢
  exact hl
