import Fresh.FourPairStepWideNativePhysical
import Fresh.FourPairStepPerturbedJoins

/-! The previous quarter-strip family embeds in the wider original deformation.
The physical speeds are identical; only the permitted parameter domain grows. -/
namespace Fresh.FourPairStepWideJoins
open Fresh

theorem quarter_speeds (c g : ℝ) (m : ℤ) (κ σ ρ : ℝ) :
    FourPairStepWidePhysical.speeds c g m κ σ ρ =
    FourPairStepPerturbedPhysical.speeds c g m κ σ ρ := rfl

theorem quarter_class_inclusion {V : Fin 8 → ℝ} {k : Fin 8}
    (h : FourPairStepPerturbedPhysical.FourPairStepPerturbedClass V k) :
    FourPairStepWidePhysical.FourPairStepWideClass V k := by
  obtain ⟨hpos,hinj,c,g,B,z,κ,σ,ρ,m,τ,hg,hm,he1,he2,hκ0,hκ1,hσ0,hσ1,hρ0,hρκ,hz,hk,hV⟩ := h
  refine ⟨hpos,hinj,c,g,B,z,κ,σ,ρ,m,τ,hg,hm,he1,he2,hκ0,
    by linarith,hσ0,hσ1,hρ0,hρκ,hz,hk,?_⟩
  simpa only [quarter_speeds] using hV

#print axioms quarter_speeds
#print axioms quarter_class_inclusion
end Fresh.FourPairStepWideJoins
