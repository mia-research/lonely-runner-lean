import Fresh.MixedStepFourArrangement

/-! Rules1–4,8–18. Physical4+4 AP blocks with real step ratio b≥2.
The polynomial original-gap condition derives both the mixed-lap low-subject
family and the upper subjects' AP-core openings. Independent step scale,
physical mirror, drift and labels are retained by the physical class.
[PROVISIONAL: counting tool] inherited boundary-opening selection. -/
open Classical
namespace Fresh.MixedStepFourParamArrangement
open Fresh Fresh.OneMover Fresh.APCoreOpening Fresh.UnequalAPArrangement

theorem high_subject_param (c A b : ℝ) (hb : 2 ≤ b) (hgap : 6*b ≤ A-3)
    (k : Fin 8) (hk : 4 ≤ (k : ℕ)) : Isolation (speeds c A 1 b 4) k := by
  let x := A-3+b*(((k : ℕ)-4 : ℕ) : ℝ)
  let C := (Finset.range 4).image (fun j : ℕ => x+(j : ℝ))
  have hj0 := Nat.cast_nonneg (α := ℝ) ((k : ℕ)-4)
  have hxlo : 6*b ≤ x := by dsimp [x]; nlinarith
  have hbpos : 0<b := by linarith
  have hx : 0<x := by nlinarith
  have hC : ∀ d∈C, x≤d ∧ d≤x+3 := by
    intro d hd
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
    have hj3 : (j : ℝ) ≤ 3 := by exact_mod_cast (show j ≤ 3 by have := Finset.mem_range.mp hj; omega)
    have hj0 := Nat.cast_nonneg (α := ℝ) j
    constructor <;> linarith
  have hsep : 8*((3 : ℕ) : ℝ)*b ≤ x*(7-((3 : ℕ) : ℝ)) := by norm_num; linarith
  have hwidth : (3 : ℝ)*(1/(8*b)+1/x) ≤ 3/4 := by
    have h16 : (16 : ℝ) ≤ 8*b := by linarith
    have h12 : (12 : ℝ) ≤ x := by nlinarith
    have hi1 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ)<16) h16
    have hi2 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ)<12) h12
    norm_num at hi1 hi2 ⊢
    linarith
  obtain ⟨ht,hcore,hpacket⟩ := ap_core_clump_opening 3 (by norm_num) (by norm_num)
    hbpos hx (by norm_num : (0 : ℝ)≤3) hC hsep hwidth
  refine ⟨_,ht,fun i hik => ?_⟩
  have hkp : ¬(k : ℕ)<4 := by omega
  by_cases hip : (i : ℕ)<4
  · have hj : 3-(i : ℕ)<4 := by omega
    have hjcast : ((3-(i : ℕ) : ℕ) : ℝ)=3-((i : ℕ) : ℝ) := by rw [Nat.cast_sub (by omega : (i : ℕ) ≤ 3)]; norm_num
    have hm : x+((3-(i : ℕ) : ℕ) : ℝ) ∈ C :=
      Finset.mem_image.mpr ⟨3-(i : ℕ),Finset.mem_range.mpr hj,rfl⟩
    have hd : speeds c A 1 b 4 i-speeds c A 1 b 4 k = -(x+((3-(i : ℕ) : ℕ) : ℝ)) := by
      rw [hjcast]
      simp [speeds,hip,hkp,x]
      ring
    rw [hd,neg_mul,Fresh.Localisation.distInt_neg]
    exact hpacket _ hm
  · have hip' : 4 ≤ (i : ℕ) := by omega
    have hicas : (((i : ℕ)-4 : ℕ) : ℝ)=((i : ℕ) : ℝ)-4 := by norm_cast
    have hkcas : (((k : ℕ)-4 : ℕ) : ℝ)=((k : ℕ) : ℝ)-4 := by norm_cast
    let n := (((i : ℕ) : ℤ)-((k : ℕ) : ℤ)).natAbs
    have hn1 : 1 ≤ n := by dsimp [n]; have := Fin.val_ne_of_ne hik; omega
    have hnle : n ≤ 3 := by dsimp [n]; have := i.isLt; have := k.isLt; omega
    have hd : speeds c A 1 b 4 i-speeds c A 1 b 4 k = (((i : ℕ) : ℝ)-((k : ℕ) : ℝ))*b := by
      simp only [speeds,if_neg hip,if_neg hkp]
      rw [hicas,hkcas]
      ring
    have he : |speeds c A 1 b 4 i-speeds c A 1 b 4 k|=(n : ℝ)*b := by
      rw [hd,abs_mul,abs_of_pos hbpos,← natAbs_cast_abs i k]
    rw [← Fresh.Localisation.distInt_abs_mul,he]
    exact hcore n hn1 hnle

theorem gap_properties (b g : ℝ) (hb : 2 ≤ b) (hg : 0<g)
    (hpoly : 9*b^2 ≤ g*(8-3*b)) : 0<8-3*b ∧ 6*b ≤ g := by
  have hbpos : 0<b := by linarith
  have hF : 0<8-3*b := by
    by_contra hn
    have hm : g*(8-3*b) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hg.le (le_of_not_gt hn)
    nlinarith [sq_nonneg b]
  refine ⟨hF,?_⟩
  by_contra hn
  have hh := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hF
  have hbprod : 0 ≤ b*(b-2) := mul_nonneg hbpos.le (by linarith)
  nlinarith

theorem low_subject_param (c A b : ℝ) (hb : 2 ≤ b) (hg : 0<A-3)
    (hpoly : 9*b^2 ≤ (A-3)*(8-3*b))
    (k : Fin 8) (hk : (k : ℕ)<4) : Isolation (speeds c A 1 b 4) k := by
  let x := A-((k : ℕ) : ℝ)
  have hkR : ((k : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (show (k : ℕ) ≤ 3 by omega)
  have hxg : A-3 ≤ x := by dsimp [x]; linarith
  have hx : 0<x := hg.trans_le hxg
  have hF := (gap_properties b (A-3) hb hg hpoly).1
  have hxpoly : 9*b^2 ≤ x*(8-3*b) := by nlinarith
  obtain ⟨t,ht,hcore,hfast⟩ := Fresh.MixedStepFour.mixed_four_upper_family_readings hx hb hxpoly
  refine ⟨t,ht,fun i hik => ?_⟩
  by_cases hip : (i : ℕ)<4
  · let n := (((i : ℕ) : ℤ)-((k : ℕ) : ℤ)).natAbs
    have hn1 : 1 ≤ n := by dsimp [n]; have := Fin.val_ne_of_ne hik; omega
    have hnle : n ≤ 3 := by dsimp [n]; omega
    have hd : speeds c A 1 b 4 i-speeds c A 1 b 4 k = ((i : ℕ) : ℝ)-((k : ℕ) : ℝ) := by simp [speeds,hip,hk]
    rw [← Fresh.Localisation.distInt_abs_mul,hd,← natAbs_cast_abs i k]
    exact hcore n hn1 hnle
  · have hj : (i : ℕ)-4 ≤ 3 := by have := i.isLt; omega
    have hd : speeds c A 1 b 4 i-speeds c A 1 b 4 k = x+(((i : ℕ)-4 : ℕ) : ℝ)*b := by simp [speeds,hip,hk,x]; ring
    rw [hd]
    exact hfast ((i : ℕ)-4) hj

theorem mixed_four_param_all (c A b : ℝ) (hb : 2 ≤ b) (hg : 0<A-3)
    (hpoly : 9*b^2 ≤ (A-3)*(8-3*b)) :
    ∀ k : Fin 8, Isolation (speeds c A 1 b 4) k := by
  intro k
  by_cases hk : (k : ℕ)<4
  · exact low_subject_param c A b hb hg hpoly k hk
  · exact high_subject_param c A b hb (gap_properties b (A-3) hb hg hpoly).2 k (by omega)

-- STANDING: DEFINITION
def MixedFourParamArrangementClass (V : Fin 8 → ℝ) : Prop :=
  (∀ i, 0 < V i) ∧ Function.Injective V ∧
  ∃ (c A b B s : ℝ) (σ : Equiv.Perm (Fin 8)),
    2 ≤ b ∧ 0<A-3 ∧ 9*b^2 ≤ (A-3)*(8-3*b) ∧ s ≠ 0 ∧
    V = (fun i => B+s*speeds c A 1 b 4 (σ i))

theorem mixedFourParamArrangement_isolation {V : Fin 8 → ℝ}
    (h : MixedFourParamArrangementClass V) (k : Fin 8) : Isolation V k := by
  obtain ⟨hpos,hinj,c,A,b,B,s,σ,hb,hg,hpoly,hs,hV⟩ := h
  rw [hV]
  have hi := mixed_four_param_all c A b hb hg hpoly (σ k)
  have ha := subject_isolation_affine B s hs hi
  exact (Fresh.isolation_comp_perm _ σ k).2 ha

#print axioms high_subject_param
#print axioms gap_properties
#print axioms low_subject_param
#print axioms mixed_four_param_all
#print axioms mixedFourParamArrangement_isolation
end Fresh.MixedStepFourParamArrangement
