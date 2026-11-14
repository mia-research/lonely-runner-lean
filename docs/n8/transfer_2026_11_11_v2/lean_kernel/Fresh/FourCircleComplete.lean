import Fresh.FourCircleGeometry
import Fresh.LowRankFibres
import Fresh.HarmonicFrontierVerified

namespace Fresh.FiniteRelations

private theorem four_positive (p : Fin 4 → ℕ) (hp : ∀ i, 0 < p i) (x : Fin 4 → ℝ) :
    ∃ q : ℕ, (q = 1 ∨ q = 2) ∧ ∃ s : ℝ,
      ∀ l, (1/8:ℝ) < distInt ((q:ℝ)*x l+(p l:ℝ)*s) := by
  by_cases h : ∀ i, p i = p 0
  · have he : Fresh.Harmonic.ClearsTwice #v[1,1,1,1] (13/100) :=
      Fresh.Harmonic.four_catalogue_phase (by decide)
        (by intro i; fin_cases i <;> decide)
        (by intro i j _; fin_cases i <;> fin_cases j <;> decide)
    obtain ⟨q,hq,t,ht⟩ := he x
    refine ⟨q,by simpa using hq,t/(p 0:ℝ),fun i => ?_⟩
    rw [h i]
    have hn : (p 0 : ℝ) ≠ 0 := by exact_mod_cast (hp 0).ne'
    rw [mul_div_cancel₀ _ hn]
    have hi := ht i
    have hget : (#v[1,1,1,1] : Vector ℕ 4).get i = 1 := by fin_cases i <;> decide
    rw [hget] at hi
    norm_num at hi
    rw [add_comm]
    exact (by norm_num : (1/8:ℝ) < 13/100).trans_le hi
  · push Not at h
    obtain ⟨i,hi⟩ := h
    exact four_positive_unequal p hp hi x

/-- Arbitrary signed nonzero four-slope circles clear strictly at one of
the two dilations. Only the all-equal positive profile uses a certificate. -/
theorem four_circle_clear : FourCircleClear (1/8) := by
  intro p hp x
  let y : Fin 4 → ℝ := fun i => if p i < 0 then -x i else x i
  obtain ⟨q,hq,t,ht⟩ := four_positive (fun i => (p i).natAbs)
    (fun i => Int.natAbs_pos.mpr (hp i)) y
  refine ⟨q,hq,t,fun i => ?_⟩
  have hi := ht i
  by_cases h : p i < 0
  · have hcast : ((p i).natAbs:ℝ) = -(p i:ℝ) := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, abs_of_neg h, Int.cast_neg]
    simp only [y,h,if_true,hcast] at hi
    rw [← Fresh.Cascade.distInt_neg ((q:ℝ)*x i+(p i:ℝ)*t)]
    convert hi using 2 <;> ring
  · have hcast : ((p i).natAbs:ℝ) = (p i:ℝ) := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, abs_of_nonneg (le_of_not_gt h)]
    simpa only [y,h,if_false,hcast] using hi

/-- Every rational subspace of codimension at most three that moves every
coordinate admits a strictly clear phase after one of two dilations. -/
theorem rank_three_fibre_clear {ι : Type*} [Fintype ι]
    (V : Submodule ℚ (ι → ℚ))
    (hdim : Fintype.card ι ≤ Module.finrank ℚ V+3)
    (hmoves : ∀ i, ∃ u : V, (u : ι → ℚ) i ≠ 0) (x : ι → ℝ) :
    ∃ q : ℕ, (q = 1 ∨ q = 2) ∧ ∃ w : V,
      ∀ i, (1/8:ℝ) < distInt ((q:ℝ)*x i+((w : ι → ℚ) i : ℝ)) :=
  low_rank_rational_fibre V le_rfl hdim hmoves (by norm_num) (fun _ => four_circle_clear) x

#print axioms four_circle_clear
#print axioms rank_three_fibre_clear

end Fresh.FiniteRelations
