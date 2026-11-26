import Fresh.NativeReturnCapture

/-! Existing relative-capture inputs imply a zero-return first-closing
quarter frame directly from ORIGINAL entry conditions. No target clearance
or isolation time is used to select the first-closing physical reading. -/
namespace Fresh.NativeReturnJoins
open Fresh Fresh.NativeReturnCapture Fresh.FastestCaptureRetention

-- STANDING: DEFINITION
noncomputable def QuarterZeroReturnClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (u c : Fin 8) (Q : ℝ) (N : ℤ) (L : Fin 8 → ℤ),
    ReturnFrame v k u c Q N L (fun _=>0) ∧ QuarterFace v k u c Q L (fun _=>0)

theorem relative_into_quarterZero {v : Fin 8 → ℝ} {k : Fin 8}
    (h : Fresh.NativeRelativeCapture.RelativeCaptureClass v k) : QuarterZeroReturnClass v k := by
  obtain ⟨hv,u,Q,N,L,hu,hQ,hlo,hhi,hm,hb⟩ := h
  have hd : 0 < |v u-v k| := abs_pos.mpr (sub_ne_zero.mpr (fun he => hu (hv.2 he)))
  let M : Fin 8 → ℤ := fun i=>if i=u then N else L i
  obtain ⟨c,hc,hfirst⟩ := Fresh.NativeFirstClosing.exists_first_closing hv k M
  have hfaces (i : Fin 8) (hi : i≠k) :
      |v i-v k|/4 ≤ |v u-v k| * ((M i : ℝ)+7/8-|v i-v k| * Q) := by
    by_cases hiu : i=u
    · subst i
      have hp := mul_nonneg hd.le (sub_nonneg.mpr hhi.le)
      have hown : |v u-v k|/4 ≤ |v u-v k| * ((N : ℝ)+7/8-|v u-v k| * Q) := by nlinarith only [hp,hd]
      simpa [M] using hown
    · rcases hb i hi hiu with hret|hcap
      · simpa [M,hiu] using hret.2
      · have hp := mul_nonneg hd.le (sub_nonneg.mpr hcap.2.1.le)
        dsimp [M]
        rw [if_neg hiu]
        nlinarith only [hp,hcap.2.2]
  refine ⟨hv,u,c,Q,N,M,?_,?_⟩
  · refine ⟨hu,hc,by simp [M],rfl,hQ,hlo,hhi,hm,?_,?_⟩
    · intro i hi hiu
      refine ⟨?_,Or.inl rfl⟩
      rcases hb i hi hiu with hret|hcap
      · apply Or.inl
        have hs : 0 ≤ |v i-v k| := abs_nonneg _
        have hup : |v i-v k| * Q ≤ (L i : ℝ)+7/8 := by nlinarith only [hret.2,hd,hs]
        simpa [M,hiu] using (show (L i : ℝ)+1/8 ≤ |v i-v k| * Q ∧ |v i-v k| * Q ≤ (L i : ℝ)+7/8 from ⟨hret.1,hup⟩)
      · apply Or.inr
        simpa [M,hiu] using (show (L i : ℝ)-1/8 < |v i-v k| * Q ∧ |v i-v k| * Q < (L i : ℝ)+1/8 from ⟨hcap.1,hcap.2.1⟩)
    · intro i hi
      simpa [lifted] using hfirst i hi
  · simpa [QuarterFace,lifted] using hfaces c hc

theorem quarterZero_into_quarter {v : Fin 8 → ℝ} {k : Fin 8} (h : QuarterZeroReturnClass v k) :
    QuarterReturnClass v k := by
  obtain ⟨hv,u,c,Q,N,L,hf,hface⟩ := h
  exact ⟨hv,u,c,Q,N,L,(fun _=>0),hf,hface⟩

theorem quarterZero_into_zero {v : Fin 8 → ℝ} {k : Fin 8} (h : QuarterZeroReturnClass v k) :
    ZeroReturnClass v k := by
  obtain ⟨hv,u,c,Q,N,L,hf,hface⟩ := h
  refine ⟨hv,u,c,Q,N,L,hf,?_⟩
  exact Fresh.NativeFirstClosing.quarter_implies_deficit _ _ Q N (lifted L (fun _=>0) c)
    (abs_nonneg _) hf.2.2.2.2.2.1 hface

theorem relative_into_zero {v : Fin 8 → ℝ} {k : Fin 8}
    (h : Fresh.NativeRelativeCapture.RelativeCaptureClass v k) : ZeroReturnClass v k :=
  quarterZero_into_zero (relative_into_quarterZero h)

theorem relative_into_sharp {v : Fin 8 → ℝ} {k : Fin 8}
    (h : Fresh.NativeRelativeCapture.RelativeCaptureClass v k) : SharpReturnClass v k :=
  zero_into_sharp (relative_into_zero h)

#print axioms relative_into_quarterZero
#print axioms quarterZero_into_quarter
#print axioms quarterZero_into_zero
#print axioms relative_into_zero
#print axioms relative_into_sharp
end Fresh.NativeReturnJoins
