import Fresh.MixedStepFourLower
import Fresh.MixedStepFourParamArrangement

/-! Rules1–4,8–18. All-subject physical4+4 family for8/7≤b≤2,
originalgapg≥9b. The reference shift joins the upper mixed-wrap mechanism;
upperblock subjects retain their full APcore and the other four readings.
[PROVISIONAL: counting tool] inherited exact boundary-opening selection. -/
open Classical
namespace Fresh.MixedStepFourLowerArrangement
open Fresh Fresh.OneMover Fresh.APCoreOpening Fresh.UnequalAPArrangement

theorem high_subject_lower (c A b : ℝ) (hb : 1 ≤ b) (hgap : 9*b ≤ A-3)
    (k : Fin 8) (hk : 4 ≤ (k : ℕ)) : Isolation (speeds c A 1 b 4) k := by
  let x := A-3+b*(((k : ℕ)-4 : ℕ) : ℝ)
  let C := (Finset.range 4).image (fun j : ℕ => x+(j : ℝ))
  have hj0 := Nat.cast_nonneg (α := ℝ) ((k : ℕ)-4)
  have hxlo : 9*b ≤ x := by dsimp [x]; nlinarith
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
    have h16 : (8 : ℝ) ≤ 8*b := by linarith
    have h12 : (9 : ℝ) ≤ x := by nlinarith
    have hi1 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ)<8) h16
    have hi2 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ)<9) h12
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
theorem low_subject_lower (c A b : ℝ) (hblo : (8/7 : ℝ) ≤ b) (hbhi : b ≤ 2)
    (hgap : 9*b ≤ A-3)
    (k : Fin 8) (hk : (k : ℕ)<4) : Isolation (speeds c A 1 b 4) k := by
  let x := A-((k : ℕ) : ℝ)
  have hkR : ((k : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (show (k : ℕ) ≤ 3 by omega)
  have hxg : A-3 ≤ x := by dsimp [x]; linarith
  have hx : 9*b ≤ x := hgap.trans hxg
  obtain ⟨t,ht,hcore,hfast⟩ := Fresh.MixedStepFourLower.mixed_four_lower_family_readings hblo hbhi hx
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

theorem mixed_four_lower_all (c A b : ℝ) (hblo : (8/7 : ℝ) ≤ b) (hbhi : b ≤ 2)
    (hgap : 9*b ≤ A-3) : ∀ k : Fin 8, Isolation (speeds c A 1 b 4) k := by
  intro k
  by_cases hk : (k : ℕ)<4
  · exact low_subject_lower c A b hblo hbhi hgap k hk
  · exact high_subject_lower c A b (by linarith) hgap k (by omega)

-- STANDING: DEFINITION
def MixedFourLowerArrangementClass (V : Fin 8 → ℝ) : Prop :=
  (∀ i, 0 < V i) ∧ Function.Injective V ∧
  ∃ (c A b B s : ℝ) (σ : Equiv.Perm (Fin 8)),
    (8/7 : ℝ) ≤ b ∧ b ≤ 2 ∧ 9*b ≤ A-3 ∧ s ≠ 0 ∧
    V = (fun i => B+s*speeds c A 1 b 4 (σ i))

theorem mixedFourLowerArrangement_isolation {V : Fin 8 → ℝ}
    (h : MixedFourLowerArrangementClass V) (k : Fin 8) : Isolation V k := by
  obtain ⟨hpos,hinj,c,A,b,B,s,σ,hblo,hbhi,hgap,hs,hV⟩ := h
  rw [hV]
  have hi := mixed_four_lower_all c A b hblo hbhi hgap (σ k)
  have ha := subject_isolation_affine B s hs hi
  exact (Fresh.isolation_comp_perm _ σ k).2 ha

#print axioms high_subject_lower
#print axioms low_subject_lower
#print axioms mixed_four_lower_all
#print axioms mixedFourLowerArrangement_isolation
end Fresh.MixedStepFourLowerArrangement
