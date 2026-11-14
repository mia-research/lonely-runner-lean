import Fresh.FibreTest

namespace Fresh.FiniteRelations

open Set MeasureTheory
open scoped BigOperators

noncomputable section

/-- A finite cover of the ambient torus controls the average on every
parameter subgroup. The bound is independent of the integer parameters. -/
theorem uniform_phase_average (n : ℕ) {r a : ℝ} (hr : 0 < r) (ha : 0 < a) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ {d : ℕ} (U : Fin d → Fin n → ℤ)
      (g : PhaseTorus (Fin n) → ℝ), Continuous g → (∀ x, 0 ≤ g x) →
      (∃ z : PhaseTorus (Fin d), ∀ x, dist x (parameterMap U z) < 2*r → a ≤ g x) →
      μ ≤ phaseAverage U g 0 := by
  classical
  let X := PhaseTorus (Fin n)
  let B (x : X) := Metric.ball x r
  have hcover : (univ : Set X) ⊆ ⋃ x, B x := by
    intro x _
    exact mem_iUnion.mpr ⟨x,Metric.mem_ball_self hr⟩
  obtain ⟨S,hS⟩ := isCompact_univ.elim_finite_subcover B (fun _ => Metric.isOpen_ball) hcover
  have hspos : 0 < S.card := by
    obtain ⟨x,hx,_⟩ := mem_iUnion₂.mp (hS (mem_univ (0 : X)))
    exact Finset.card_pos.mpr ⟨x,hx⟩
  have hn : (0:ℝ) < S.card := by exact_mod_cast hspos
  refine ⟨a/S.card,div_pos ha hn,?_⟩
  intro d U g hg hgn hball
  obtain ⟨z,hz⟩ := hball
  let v (x : X) : PhaseTorus (Fin d) :=
    if h : ∃ y, parameterMap U y ∈ B x then h.choose else 0
  let f (x : X) (y : PhaseTorus (Fin d)) := g (parameterMap U ((z - v x) + y))
  have hlow (y : PhaseTorus (Fin d)) : a ≤ ∑ x ∈ S, f x y := by
    obtain ⟨x,hxs,hxy⟩ := mem_iUnion₂.mp (hS (mem_univ (parameterMap U y)))
    have h : ∃ y, parameterMap U y ∈ B x := ⟨y,hxy⟩
    have hv : parameterMap U (v x) ∈ B x := by
      simpa only [v,dif_pos h] using h.choose_spec
    have hd : dist (parameterMap U y) (parameterMap U (v x)) < 2*r := by
      have h1 := Metric.mem_ball.mp hxy
      have h2 := Metric.mem_ball.mp hv
      have hd := dist_triangle (parameterMap U y) x (parameterMap U (v x))
      rw [dist_comm x] at hd
      linarith
    have hneg (t : PhaseTorus (Fin d)) : parameterMap U (-t) = -parameterMap U t := by
      apply eq_neg_of_add_eq_zero_left
      rw [← parameterMap_add, neg_add_cancel]
      ext i
      simp [parameterMap]
    have hnear : dist (parameterMap U ((z - v x) + y)) (parameterMap U z) < 2*r := by
      rw [dist_pi_lt_iff (by positivity)] at hd ⊢
      intro i
      have hi := hd i
      simp only [sub_eq_add_neg,parameterMap_add,hneg,Pi.add_apply,Pi.neg_apply]
      have he : parameterMap U z i + -parameterMap U (v x) i +
          parameterMap U y i - parameterMap U z i =
            parameterMap U y i - parameterMap U (v x) i := by abel
      simpa only [dist_eq_norm,he] using hi
    exact (hz _ hnear).trans (Finset.single_le_sum (f := fun t => f t y) (fun t _ => hgn _) hxs)
  let M := parameterMeasure (Fin d)
  have hI (x : X) : Integrable (f x) M := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact hg.comp ((continuous_parameterMap U).comp (continuous_const.add continuous_id))
  have havg (x : X) : (∫ y, f x y ∂M) = phaseAverage U g 0 := by
    simpa only [f,phaseAverage,zero_add] using
      integral_add_left_eq_self (μ := M) (fun y => g (parameterMap U y)) (z - v x)
  have htotal := integral_mono (μ := M) (integrable_const a)
    (integrable_finset_sum S (fun x _ => hI x)) hlow
  rw [integral_finset_sum _ (fun x _ => hI x)] at htotal
  simp only [integral_const, probReal_univ, one_smul, havg, Finset.sum_const,
    nsmul_eq_mul] at htotal
  exact (div_le_iff₀ hn).2 (by simpa only [mul_comm] using htotal)

#print axioms uniform_phase_average

end
end Fresh.FiniteRelations
