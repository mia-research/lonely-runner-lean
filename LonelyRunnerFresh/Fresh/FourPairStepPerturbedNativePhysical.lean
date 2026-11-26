import Fresh.FourPairStepPerturbedPhysical

/-! Rules:1–4,8–18. Full native trace on original physical speed labels,
including the first-free branch that skips the reference T. Both branches
retain all seven readings and merge at the actual moved runner's opening. -/
namespace Fresh.FourPairStepPerturbedNativePhysical
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourPairStepBounds Fresh.FourPairStepPerturbedMerge Fresh.FourPairStepPerturbedBounds Fresh.FourPairStepPerturbedPhysical

theorem physical_original_episode (c g : ℝ) (m : ℤ) (hm : 1 ≤ m) (hg : 0 < g)
    (he1 : 1 < (8*(m : ℝ)+1)*g) (he2 : (8*(m : ℝ)-1)*g < 1)
    (κ σ ρ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1/4) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hρ0 : 0 ≤ ρ) (hρκ : ρ ≤ κ) :
    let E := disparitySet (speeds c g m κ σ ρ) (1 : Fin 8)
    IsLeast (E : Set ℝ) g ∧
    (((2*(m : ℝ)+7/8 < moved m κ*(1/(8*g))) ∧ IsMove E (1/(8*g)) (U m κ)) ∨
     ((¬2*(m : ℝ)+7/8 < moved m κ*(1/(8*g))) ∧
        IsMove E (1/(8*g)) (T m) ∧ IsMove E (T m) (U m κ))) ∧
    IsMove E (U m κ) (VP m ρ) ∧ IsMove E (VP m ρ) (WP m ρ) ∧ LonelyAt E (WP m ρ) := by
  dsimp only
  rw [original_disparity_eq c g m hm hg κ σ ρ hκ0 hκ1 hσ0 hσ1 hρ0 hρκ]
  exact native_original_episode g m hm hg he1 he2 κ σ ρ hκ0 hκ1 hσ0 hσ1 hρ0 hρκ

#print axioms physical_original_episode
end Fresh.FourPairStepPerturbedNativePhysical
