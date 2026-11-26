import Fresh.FourPairStepIndependentNativePhysical
import Fresh.FourPairStepWideJoins

/-! The previous coupled-strip family embeds in the independent original deformation.
The physical speeds are identical; only the permitted parameter domain grows. -/
namespace Fresh.FourPairStepIndependentJoins
open Fresh

theorem triangle_speeds (c g : ℝ) (m : ℤ) (κ σ ρ : ℝ) :
    FourPairStepIndependentPhysical.speeds c g m κ σ ρ =
    FourPairStepWidePhysical.speeds c g m κ σ ρ := rfl

theorem triangle_class_inclusion {V : Fin 8 → ℝ} {k : Fin 8}
    (h : FourPairStepWidePhysical.FourPairStepWideClass V k) :
    FourPairStepIndependentPhysical.FourPairStepIndependentClass V k := by
  obtain ⟨hpos,hinj,c,g,B,z,κ,σ,ρ,m,τ,hg,hm,he1,he2,hκ0,hκ1,hσ0,hσ1,hρ0,hρκ,hz,hk,hV⟩ := h
  refine ⟨hpos,hinj,c,g,B,z,κ,σ,ρ,m,τ,hg,hm,he1,he2,hκ0,
    hκ1,hσ0,hσ1,hρ0,hρκ.trans hκ1,hz,hk,?_⟩
  simpa only [triangle_speeds] using hV

#print axioms triangle_speeds
#print axioms triangle_class_inclusion
end Fresh.FourPairStepIndependentJoins
