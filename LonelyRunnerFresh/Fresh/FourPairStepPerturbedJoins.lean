import Fresh.FourPairStepPerturbedNativePhysical

/-! Rules:1–4,8–18. The fixed far-pair class is the exactρ=0 slice.
This is an inclusion, not an additional disjoint arrangement class. -/
namespace Fresh.FourPairStepPerturbedJoins
open Fresh Fresh.FourPairStepBounds Fresh.FourPairStepPerturbedBounds

theorem baseline_speeds (c g : ℝ) (m : ℤ) (κ σ : ℝ) :
    FourPairStepPerturbedPhysical.speeds c g m κ σ 0 =
    FourPairStepPhysical.speeds c g m κ σ := by
  funext i
  simp [FourPairStepPerturbedPhysical.speeds,FourPairStepPhysical.speeds]

theorem baseline_class_inclusion {V : Fin 8 → ℝ} {k : Fin 8}
    (h : FourPairStepPhysical.FourPairStepClass V k) :
    FourPairStepPerturbedPhysical.FourPairStepPerturbedClass V k := by
  obtain ⟨hpos,hinj,c,g,B,z,κ,σ,m,τ,hg,hm,he1,he2,hκ0,hκ1,hσ0,hσ1,hz,hk,hV⟩ := h
  refine ⟨hpos,hinj,c,g,B,z,κ,σ,0,m,τ,hg,hm,he1,he2,hκ0,hκ1,hσ0,hσ1,le_rfl,hκ0.le,hz,hk,?_⟩
  simpa only [baseline_speeds] using hV

#print axioms baseline_speeds
#print axioms baseline_class_inclusion
end Fresh.FourPairStepPerturbedJoins
