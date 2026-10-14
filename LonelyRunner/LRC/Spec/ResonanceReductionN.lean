import LonelyRunner.LRC.Spec.OneFreeN

/-!+# A bounded one-reading deformation reduces to finitely many resonances

Six fixed readings have a common period P. The existing OneFree theorem
settles every mover x off the lattice x*P ∈ ℤ. On [L,U] the remaining
values are exactly z/P for ceil(L*P) ≤ z ≤ floor(U*P). This is a finite
reduction for each fixed core and segment, not a universal finite catalogue.
No WindowBound, simple-pinch assumption or successful future transport is used.
The off-lattice implication uses the existing native order-seven theorem
through OneFreeN; this dependency is not a new proof of order seven.
-/

namespace LRC.ResonanceReduction

theorem resonance_index_iff {L U P : ℝ} (hP : 0 < P) (z : ℤ) :
    z ∈ Finset.Icc ⌈L*P⌉ ⌊U*P⌋ ↔ L ≤ (z : ℝ)/P ∧ (z : ℝ)/P ≤ U := by
  rw [Finset.mem_Icc, Int.ceil_le, Int.le_floor]
  rw [le_div_iff₀ hP, div_le_iff₀ hP]

/-- All continuous mover values in a bounded interval are settled iff its
explicit finite list of lattice values is settled. The exceptional values
themselves remain obligations, not assumed consequences of normalization. -/
theorem segment_iff_resonances (v : Fin 8 → ℝ) (k i : Fin 8)
    (hki : k ≠ i) {P L U : ℝ} (hP : 0 < P) (hL : 0 < L)
    (hcore : ∀ j : Fin 8, j ≠ k → j ≠ i → 0 < v j-v k)
    (hper : ∀ j : Fin 8, j ≠ i → ∃ z : ℤ, (v j-v k)*P = z) :
    (∀ x : ℝ, L ≤ x → x ≤ U →
      LRC.Spec.LonelyForSubject (Function.update v i (v k+x)) k) ↔
    ∀ z ∈ Finset.Icc ⌈L*P⌉ ⌊U*P⌋,
      LRC.Spec.LonelyForSubject (Function.update v i (v k+(z : ℝ)/P)) k := by
  classical
  constructor
  · intro h z hz
    obtain ⟨hl, hu⟩ := (resonance_index_iff hP z).mp hz
    exact h _ hl hu
  · intro h x hl hu
    by_cases hint : ∃ z : ℤ, x*P = z
    · obtain ⟨z, hz⟩ := hint
      have hx : x = (z : ℝ)/P := (eq_div_iff hP.ne').mpr hz
      have hzmem : z ∈ Finset.Icc ⌈L*P⌉ ⌊U*P⌋ :=
        (resonance_index_iff hP z).mpr (by simpa [← hx] using And.intro hl hu)
      simpa [← hx] using h z hzmem
    · apply LRC.OneFree.lonely_of_one_free_eight (i := i) hki (P := P) ?_ hP ?_ ?_
      · intro j hj
        by_cases hji : j = i
        · subst j
          simpa [Function.update_of_ne hki] using hL.trans_le hl
        · simpa [Function.update_of_ne hji, Function.update_of_ne hki] using hcore j hj hji
      · intro j hj
        simpa [Function.update_of_ne hj, Function.update_of_ne hki] using hper j hj
      · intro z hz
        apply hint
        refine ⟨z, ?_⟩
        simpa [Function.update_of_ne hki] using hz

end LRC.ResonanceReduction
