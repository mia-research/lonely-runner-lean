import LonelyRunner.LRC.Spec.PinchReflectionN

/-!+# An incoming rational lap window supplies its own reflected replacement

The old window is assumed feasible earlier and at the current arrangement.
Its rational endpoint time and the earlier-feasibility hypothesis required by
reflection are derived, not separate certificates. No future window is assumed.
This is local continuation, not whole-deformation coverage.
-/

namespace LRC.IncomingWindow
variable {ι : Type*}

/-- Rational readings give a rational positive witness for every feasible
natural-lap window: take its largest lower endpoint. -/
theorem rational_window_time (S : Finset ι) (hS : S.Nonempty)
    (d : ι → ℚ) (q : ι → ℕ) (hd : ∀ i ∈ S, 0 < (d i : ℝ))
    (hw : ∃ t : ℝ, ∀ i ∈ S,
      (q i : ℝ) + 1/8 ≤ (d i : ℝ)*t ∧ (d i : ℝ)*t ≤ q i+7/8) :
    ∃ t : ℚ, 0 < (t : ℝ) ∧ ∀ i ∈ S,
      (q i : ℝ)+1/8 ≤ (d i : ℝ)*(t : ℝ) ∧
        (d i : ℝ)*(t : ℝ) ≤ q i+7/8 := by
  classical
  let lo := fun i => ((q i : ℝ)+1/8)/(d i : ℝ)
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' hS lo
  obtain ⟨t0, ht0⟩ := hw
  have hmax : ∀ j ∈ S, lo j ≤ lo i := by
    intro j hj
    have hh := Finset.le_sup' lo hj
    rwa [he] at hh
  have hupper : ∀ j ∈ S, lo i ≤ ((q j : ℝ)+7/8)/(d j : ℝ) := by
    intro j hj
    have hl : lo i ≤ t0 := (div_le_iff₀ (hd i hi)).mpr (by nlinarith [(ht0 i hi).1])
    have hu : t0 ≤ ((q j : ℝ)+7/8)/(d j : ℝ) :=
      (le_div_iff₀ (hd j hj)).mpr (by nlinarith [(ht0 j hj).2])
    exact hl.trans hu
  refine ⟨((q i : ℚ)+1/8)/d i, ?_, ?_⟩
  · push_cast
    exact div_pos (by positivity) (hd i hi)
  · intro j hj
    have hl := (div_le_iff₀ (hd j hj)).mp (hmax j hj)
    have hu := (le_div_iff₀ (hd j hj)).mp (hupper j hj)
    push_cast
    dsimp [lo] at hl hu
    constructor <;> nlinarith

/-- A rational incoming window always has a right-hand replacement,
including simultaneous pinches. Only OLD feasibility is supplied. -/
theorem replacement_of_incoming (S : Finset ι) (hS : S.Nonempty)
    (d : ι → ℚ) (v : ι → ℝ) (q : ι → ℕ) {delta : ℝ}
    (hd : ∀ i ∈ S, 0 < (d i : ℝ)) (hdelta : 0 < delta)
    (hpriorpos : ∀ i ∈ S, 0 < (d i : ℝ)-delta*v i)
    (hprior : ∃ t : ℝ, ∀ i ∈ S,
      (q i : ℝ)+1/8 ≤ ((d i : ℝ)-delta*v i)*t ∧
        ((d i : ℝ)-delta*v i)*t ≤ q i+7/8)
    (hnow : ∃ t : ℝ, ∀ i ∈ S,
      (q i : ℝ)+1/8 ≤ (d i : ℝ)*t ∧ (d i : ℝ)*t ≤ q i+7/8) :
    ∃ p : ι → ℤ, ∃ e : ℝ, 0 < e ∧ ∀ h : ℝ, 0 ≤ h → h ≤ e →
      ∃ t : ℝ, 0 < t ∧ ∀ i ∈ S,
        (p i : ℝ)+1/8 ≤ ((d i : ℝ)+h*v i)*t ∧
          ((d i : ℝ)+h*v i)*t ≤ p i+7/8 := by
  obtain ⟨t, ht, hband⟩ := rational_window_time S hS d q hd hnow
  have hleft := (WindowPinch.lap_windows_iff S hS
    (fun i => (d i : ℝ)-delta*v i) (fun i => (q i : ℤ)) hpriorpos).mp
    (by simpa using hprior)
  apply PinchReflection.rational_pinch_transport S hS d v (fun i => (q i : ℤ)) t
    hd ht hdelta (by simpa using hband)
  intro i hi j hj
  have hh := hleft i hi j hj
  simp only [Int.cast_natCast] at hh ⊢
  nlinarith

end LRC.IncomingWindow
