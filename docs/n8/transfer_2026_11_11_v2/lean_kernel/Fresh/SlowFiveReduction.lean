import Fresh.ThreeFast

namespace Fresh.FiniteRelations

open Set

private theorem four_fast_first_window :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Fin 4 → ℝ, (∀ i, C < v i) →
      ∃ t ∈ Ioo (1/8:ℝ) (7/8), ∀ i, (1/8:ℝ) < distInt (v i*t) := by
  obtain ⟨N,E,C,_,hC,hv⟩ := buffered_clear_or_finite_kernels 4 (show (0:ℝ) < 1/10 by norm_num)
  refine ⟨C,hC,fun v hf => ?_⟩
  rcases hv v (1/5) (3/10) (by norm_num) hf with ⟨t,ht,h1 | h2⟩ | ⟨A,w,hw,_,hp,hdim⟩
  · exact ⟨t,⟨by linarith [ht.1],by linarith [ht.2]⟩,h1⟩
  · refine ⟨2*t,⟨by linarith [ht.1],by linarith [ht.2]⟩,fun i => ?_⟩
    rw [← mul_assoc,mul_comm (v i) 2,mul_assoc]
    exact h2 i
  · have hz : Module.finrank ℝ (LinearMap.ker (evaluate (tableRows A))) = 0 := hdim
    rw [Submodule.finrank_eq_zero.mp hz,Submodule.mem_bot] at hw
    subst w
    exact (lt_irrefl (0:ℝ) (hp 0)).elim

/-- The five-slow strict-window problem is a bounded problem. The same
first-window and buffered append lemmas close every escaping sector. -/
theorem five_slow_first_window_or_bounded :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ r : Fin 4 → ℝ, (∀ i, 1 ≤ r i) → Monotone r →
      (∃ t ∈ Ioo (1/8:ℝ) (7/8), ∀ i, (1/8:ℝ) < distInt (r i*t)) ∨ r 3 ≤ B := by
  obtain ⟨C₁,_,h₁⟩ := four_fast_first_window
  let B₁ := max 1 C₁
  obtain ⟨C₂,_,h₂⟩ := three_fast_window B₁
  let B₂ := max B₁ C₂
  obtain ⟨C₃,_,h₃⟩ := three_fast_window B₂
  let B₃ := max B₂ C₃
  obtain ⟨C₄,_,h₄⟩ := three_fast_window B₃
  have hb₁ : 1 ≤ B₁ := le_max_left _ _
  have hb₂ : B₁ ≤ B₂ := le_max_left _ _
  have hb₃ : B₂ ≤ B₃ := le_max_left _ _
  refine ⟨max B₃ C₄,hb₁.trans (hb₂.trans (hb₃.trans (le_max_left _ _))),fun r hr hm => ?_⟩
  by_cases h1 : C₁ < r 0
  · exact Or.inl (h₁ r (fun i => h1.trans_le (hm (Fin.zero_le i))))
  have hB₁ : r 0 ≤ B₁ := (le_of_not_gt h1).trans (le_max_right _ _)
  by_cases h2 : C₂ < r 1
  · let slow : Fin 3 → ℝ := ![r 0,1,1]
    let fast : Fin 3 → ℝ := ![r 1,r 2,r 3]
    obtain ⟨t,ht,hs,hf⟩ := h₂ slow fast (by intro i; fin_cases i <;> first | exact hr 0 | exact le_rfl)
      (by intro i; fin_cases i <;> first | exact hB₁ | exact hb₁)
      (by intro i; fin_cases i
          · exact h2
          · exact h2.trans_le (hm (by decide : (1:Fin 4) ≤ 2))
          · exact h2.trans_le (hm (by decide : (1:Fin 4) ≤ 3)))
    exact Or.inl ⟨t,ht,fun i => by fin_cases i
                                   · exact hs 0
                                   · exact hf 0
                                   · exact hf 1
                                   · exact hf 2⟩
  have hB₂ : r 1 ≤ B₂ := (le_of_not_gt h2).trans (le_max_right _ _)
  by_cases h3 : C₃ < r 2
  · let slow : Fin 3 → ℝ := ![r 0,r 1,1]
    let fast : Fin 3 → ℝ := ![r 2,r 3,r 3]
    obtain ⟨t,ht,hs,hf⟩ := h₃ slow fast
      (by intro i; fin_cases i <;> first | exact hr 0 | exact hr 1 | exact le_rfl)
      (by intro i; fin_cases i
          · exact hB₁.trans hb₂
          · exact hB₂
          · exact hb₁.trans hb₂)
      (by intro i; fin_cases i <;> first
          | exact h3
          | exact h3.trans_le (hm (by decide : (2:Fin 4) ≤ 3)))
    exact Or.inl ⟨t,ht,fun i => by fin_cases i
                                   · exact hs 0
                                   · exact hs 1
                                   · exact hf 0
                                   · exact hf 1⟩
  have hB₃ : r 2 ≤ B₃ := (le_of_not_gt h3).trans (le_max_right _ _)
  by_cases h4 : C₄ < r 3
  · let slow : Fin 3 → ℝ := ![r 0,r 1,r 2]
    let fast : Fin 3 → ℝ := fun _ => r 3
    obtain ⟨t,ht,hs,hf⟩ := h₄ slow fast
      (by intro i; fin_cases i <;> first | exact hr 0 | exact hr 1 | exact hr 2)
      (by intro i; fin_cases i
          · exact hB₁.trans (hb₂.trans hb₃)
          · exact hB₂.trans hb₃
          · exact hB₃)
      (fun _ => h4)
    exact Or.inl ⟨t,ht,fun i => by fin_cases i
                                   · exact hs 0
                                   · exact hs 1
                                   · exact hs 2
                                   · exact hf 0⟩
  exact Or.inr ((le_of_not_gt h4).trans (le_max_right _ _))

#print axioms five_slow_first_window_or_bounded

end Fresh.FiniteRelations
