import Fresh.GeneralTwoAPArrangement
import Fresh.SignedAPArrangement
import Fresh.APCoreOpening
import Fresh.TrainFlankInterplay

/-! Exact containments between arrangement families. The special cases below
are not counted as additional types. No existence premise is introduced.
[PROVISIONAL: counting tool] inherited reference-opening selections only.
-/
namespace Fresh.ArrangementFamilyJoinsOct26
open Fresh Fresh.SplitAPArrangement Fresh.OpeningClump Fresh.APCoreOpening
open Fresh.TrainFlankPair Fresh.TrainFlankInterplay

theorem base_injective_of_affine_relabel {f v : Fin 8 → ℝ} {B s : ℝ}
    {σ : Equiv.Perm (Fin 8)} (hinj : Function.Injective v)
    (hv : v=(fun i => B+s*f (σ i))) : Function.Injective f := by
  intro i j hij
  have he : v (σ.symm i)=v (σ.symm j) := by rw [hv]; simpa using congrArg (fun z => B+s*z) hij
  have hh := congrArg σ (hinj he)
  simpa using hh

theorem separated_imp_general {v : Fin 8 → ℝ} (h : TwoAPBlockClass v) :
    GeneralTwoAPBlockClass v := by
  obtain ⟨hpos,hinj,c,A,B,s,p,σ,hp2,hp6,hgap,hs,hv⟩ := h
  exact ⟨hpos,hinj,c,A,B,s,p,σ,by omega,by omega,hs,base_injective_of_affine_relabel hinj hv,hv⟩

theorem noninteger_imp_general {v : Fin 8 → ℝ} (h : NonintegerTwoAPBlockClass v) :
    GeneralTwoAPBlockClass v := by
  obtain ⟨hpos,hinj,c,A,B,s,p,σ,hp2,hp6,hnot,hs,hv⟩ := h
  exact ⟨hpos,hinj,c,A,B,s,p,σ,by omega,by omega,hs,base_injective_of_affine_relabel hinj hv,hv⟩

theorem openingClump_imp_APCore {v : Fin 8 → ℝ} {k : Fin 8}
    (h : OpeningClumpClass v k) : APCoreOpeningClass v k := by
  obtain ⟨s,x,w,C,hs,hx,hw,hC,hsep,hwidth,hmem⟩ := h
  refine ⟨1,s,x,w,C,by omega,by omega,hs,hx,hw,hC,?_,hwidth,?_⟩
  · norm_num
    nlinarith
  · intro d hd
    rcases (hmem d).1 hd with rfl | hdC
    · exact Or.inl ⟨1,by omega,by omega,by norm_num⟩
    · exact Or.inr hdC

theorem polynomialPair_imp_pairOpening {v : Fin 8 → ℝ} {k : Fin 8}
    (h : PolynomialPairTrainClass v k) : PairTrainOpeningClass v k := by
  obtain ⟨s,a,x,w,C,hs,ha,hsa,hx,hw,hC,hsep,hwidth,hmem⟩ := h
  have hleft : pairLeft s a 0 0=1/(8*s) := by
    unfold pairLeft
    norm_num
    rw [max_eq_left]
    · ring
    · exact div_le_div_of_nonneg_left (by norm_num) hs hsa
  have hright : pairRight s a 0 0=7/(8*a) := by
    unfold pairRight
    norm_num
    rw [min_eq_right]
    · ring
    · exact div_le_div_of_nonneg_left (by norm_num) hs hsa
  refine ⟨s,a,x,w,C,0,0,hs,ha,hx,hw,hC,?_,?_,hmem⟩
  · rw [hleft,hright]
    apply (le_div_iff₀ (by positivity : 0<8*a)).2
    have he : (1/(8*s)+1/x)*(8*a)=(a*x+8*a*s)/(s*x) := by field_simp
    rw [he,div_le_iff₀ (by positivity : 0<s*x)]
    nlinarith
  · rw [hleft]
    have he : w*(1/(8*s)+1/x)=(w*x+8*w*s)/(8*s*x) := by field_simp
    rw [he,div_le_iff₀ (by positivity : 0<8*s*x)]
    nlinarith

#print axioms base_injective_of_affine_relabel
#print axioms separated_imp_general
#print axioms noninteger_imp_general
#print axioms openingClump_imp_APCore
#print axioms polynomialPair_imp_pairOpening
end Fresh.ArrangementFamilyJoinsOct26
