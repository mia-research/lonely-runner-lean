import Fresh.FourPairStepPhysical

/-! Rules:1–4,8–18. Full native trace on original physical speed labels,
including the first-free branch that skips the reference T. Both branches
retain all seven readings and merge at the actual moved runner's opening. -/
namespace Fresh.FourPairStepNativePhysical
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourPairStepBounds Fresh.FourPairStepMerge Fresh.FourPairStepPhysical

theorem physical_original_episode (c g : ℝ) (m : ℤ) (hm : 1 ≤ m) (hg : 0 < g)
    (he1 : 1 < (8*(m : ℝ)+1)*g) (he2 : (8*(m : ℝ)-1)*g < 1)
    (κ σ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1/4) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    let E := disparitySet (speeds c g m κ σ) (1 : Fin 8)
    IsLeast (E : Set ℝ) g ∧
    (((2*(m : ℝ)+7/8 < moved m κ*(1/(8*g))) ∧ IsMove E (1/(8*g)) (U m κ)) ∨
     ((¬2*(m : ℝ)+7/8 < moved m κ*(1/(8*g))) ∧
        IsMove E (1/(8*g)) (T m) ∧ IsMove E (T m) (U m κ))) ∧
    IsMove E (U m κ) (V m) ∧ IsMove E (V m) (W m) ∧ LonelyAt E (W m) := by
  dsimp only
  rw [original_disparity_eq c g m hm hg κ σ hκ0 hκ1 hσ0 hσ1]
  exact native_original_episode g m hm hg he1 he2 κ σ hκ0 hκ1 hσ0 hσ1

#print axioms physical_original_episode
end Fresh.FourPairStepNativePhysical
