import Fresh.MiddleStepFive
import Fresh.UnequalAPArrangement

/-!
Rules:1–4,8–18. All-subject physical3+5 AP blocks with independent step
ratio b. The middle fast opening clears the low subjects; the upper five
subjects retain their step-b AP core and carry the entire low width-two
packet. Every original subject role and closed parameter face is retained.
[PROVISIONAL: counting tool] inherited exact opening selection.
-/
open Classical
namespace Fresh.MiddleStepFiveArrangement
open Fresh Fresh.OneMover Fresh.APCoreOpening Fresh.UnequalAPArrangement

theorem high_subject (c A b : ℝ) (hb : (3/4 : ℝ) ≤ b)
    (hgap : 32*b ≤ 3*(A-2)) (k : Fin 8) (hk : 3 ≤ (k : ℕ)) :
    Isolation (speeds c A 1 b 3) k := by
  let x := A-2+b*(((k : ℕ)-3 : ℕ) : ℝ)
  let C := (Finset.range 3).image (fun j : ℕ => x+(j : ℝ))
  have hbpos : 0<b := by linarith
  have hj0 := Nat.cast_nonneg (α := ℝ) ((k : ℕ)-3)
  have hxlo : 32*b ≤ 3*x := by dsimp [x]; nlinarith
  have hx8 : (8 : ℝ) ≤ x := by nlinarith
  have hx : 0<x := by linarith
  have hC : ∀ d∈C, x≤d ∧ d≤x+2 := by
    intro d hd
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
    have hj2 : (j : ℝ) ≤ 2 := by exact_mod_cast (show j ≤ 2 by have := Finset.mem_range.mp hj; omega)
    have hj0 := Nat.cast_nonneg (α := ℝ) j
    constructor <;> linarith
  have hsep : 8*((4 : ℕ) : ℝ)*b ≤ x*(7-((4 : ℕ) : ℝ)) := by norm_num; linarith
  have hwidth : (2 : ℝ)*(1/(8*b)+1/x) ≤ 3/4 := by
    have h6 : (6 : ℝ) ≤ 8*b := by linarith
    have hi1 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ)<6) h6
    have hi2 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ)<8) hx8
    norm_num at hi1 hi2 ⊢
    linarith
  obtain ⟨ht,hcore,hpacket⟩ := ap_core_clump_opening 4 (by norm_num) (by norm_num)
    hbpos hx (by norm_num : (0 : ℝ)≤2) hC hsep hwidth
  refine ⟨_,ht,fun i hik => ?_⟩
  have hkp : ¬(k : ℕ)<3 := by omega
  by_cases hip : (i : ℕ)<3
  · have hj : 2-(i : ℕ)<3 := by omega
    have hjcast : ((2-(i : ℕ) : ℕ) : ℝ)=2-((i : ℕ) : ℝ) := by rw [Nat.cast_sub (by omega : (i : ℕ) ≤ 2)]; norm_num
    have hm : x+((2-(i : ℕ) : ℕ) : ℝ) ∈ C :=
      Finset.mem_image.mpr ⟨2-(i : ℕ),Finset.mem_range.mpr hj,rfl⟩
    have hd : speeds c A 1 b 3 i-speeds c A 1 b 3 k = -(x+((2-(i : ℕ) : ℕ) : ℝ)) := by
      rw [hjcast]
      simp [speeds,hip,hkp,x]
      ring
    rw [hd,neg_mul,Fresh.Localisation.distInt_neg]
    exact hpacket _ hm
  · have hip' : 3 ≤ (i : ℕ) := by omega
    have hicas : (((i : ℕ)-3 : ℕ) : ℝ)=((i : ℕ) : ℝ)-3 := by norm_cast
    have hkcas : (((k : ℕ)-3 : ℕ) : ℝ)=((k : ℕ) : ℝ)-3 := by norm_cast
    let n := (((i : ℕ) : ℤ)-((k : ℕ) : ℤ)).natAbs
    have hn1 : 1 ≤ n := by dsimp [n]; have := Fin.val_ne_of_ne hik; omega
    have hnle : n ≤ 4 := by dsimp [n]; have := i.isLt; have := k.isLt; omega
    have hd : speeds c A 1 b 3 i-speeds c A 1 b 3 k = (((i : ℕ) : ℝ)-((k : ℕ) : ℝ))*b := by
      simp only [speeds,if_neg hip,if_neg hkp]
      rw [hicas,hkcas]
      ring
    have he : |speeds c A 1 b 3 i-speeds c A 1 b 3 k|=(n : ℝ)*b := by
      rw [hd,abs_mul,abs_of_pos hbpos,← natAbs_cast_abs i k]
    rw [← Fresh.Localisation.distInt_abs_mul,he]
    exact hcore n hn1 hnle

theorem low_subject (c A b : ℝ) (hb : (6/7 : ℝ) ≤ b)
    (hgap : 32*b ≤ 3*(A-2))
    (hbranch : b ≤ 2 ∨ 2*b*(b+1) ≤ (A-2)*(3-b))
    (k : Fin 8) (hk : (k : ℕ)<3) : Isolation (speeds c A 1 b 3) k := by
  let x := A-((k : ℕ) : ℝ)
  have hkR : ((k : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (show (k : ℕ) ≤ 2 by omega)
  have hxg : A-2 ≤ x := by dsimp [x]; linarith
  have hbpos : 0<b := by linarith
  have hg : 0<A-2 := by nlinarith
  have hx : 0<x := hg.trans_le hxg
  have hfamily : ∃ T : ℝ, 0<T ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ 2 → (1/8 : ℝ) ≤ distInt ((j : ℝ)*T)) ∧
      ∀ j : ℕ, j ≤ 4 → (1/8 : ℝ) ≤ distInt ((x+(j : ℝ)*b)*T) := by
    by_cases hblo : b ≤ 2
    · exact Fresh.MiddleStepFive.middle_five_lower_readings hb hblo (by nlinarith)
    · have hb2 : 2 ≤ b := le_of_lt (lt_of_not_ge hblo)
      have hp := hbranch.resolve_left hblo
      have hF : 0<3-b := by
        by_contra hn
        have hm : (A-2)*(3-b) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hg.le (le_of_not_gt hn)
        nlinarith [sq_nonneg b]
      have hxpoly : 2*b*(b+1) ≤ x*(3-b) := by nlinarith
      exact Fresh.MiddleStepFive.middle_five_upper_readings hx hb2 hxpoly
  obtain ⟨t,ht,hcore,hfast⟩ := hfamily
  refine ⟨t,ht,fun i hik => ?_⟩
  by_cases hip : (i : ℕ)<3
  · let n := (((i : ℕ) : ℤ)-((k : ℕ) : ℤ)).natAbs
    have hn1 : 1 ≤ n := by dsimp [n]; have := Fin.val_ne_of_ne hik; omega
    have hnle : n ≤ 2 := by dsimp [n]; omega
    have hd : speeds c A 1 b 3 i-speeds c A 1 b 3 k = ((i : ℕ) : ℝ)-((k : ℕ) : ℝ) := by simp [speeds,hip,hk]
    rw [← Fresh.Localisation.distInt_abs_mul,hd,← natAbs_cast_abs i k]
    exact hcore n hn1 hnle
  · have hj : (i : ℕ)-3 ≤ 4 := by have := i.isLt; omega
    have hd : speeds c A 1 b 3 i-speeds c A 1 b 3 k = x+(((i : ℕ)-3 : ℕ) : ℝ)*b := by simp [speeds,hip,hk,x]; ring
    rw [hd]
    exact hfast ((i : ℕ)-3) hj

theorem middle_five_all (c A b : ℝ) (hb : (6/7 : ℝ) ≤ b)
    (hgap : 32*b ≤ 3*(A-2))
    (hbranch : b ≤ 2 ∨ 2*b*(b+1) ≤ (A-2)*(3-b)) :
    ∀ k : Fin 8, Isolation (speeds c A 1 b 3) k := by
  intro k
  by_cases hk : (k : ℕ)<3
  · exact low_subject c A b hb hgap hbranch k hk
  · exact high_subject c A b (by linarith) hgap k (by omega)

-- STANDING: DEFINITION
def MiddleFiveArrangementClass (V : Fin 8 → ℝ) : Prop :=
  (∀ i, 0 < V i) ∧ Function.Injective V ∧
  ∃ (c A b B s : ℝ) (σ : Equiv.Perm (Fin 8)),
    (6/7 : ℝ) ≤ b ∧ 32*b ≤ 3*(A-2) ∧
    (b ≤ 2 ∨ 2*b*(b+1) ≤ (A-2)*(3-b)) ∧ s ≠ 0 ∧
    V = (fun i => B+s*speeds c A 1 b 3 (σ i))

theorem middleFiveArrangement_isolation {V : Fin 8 → ℝ}
    (h : MiddleFiveArrangementClass V) (k : Fin 8) : Isolation V k := by
  obtain ⟨hpos,hinj,c,A,b,B,s,σ,hb,hgap,hbranch,hs,hV⟩ := h
  rw [hV]
  have hi := middle_five_all c A b hb hgap hbranch (σ k)
  have ha := subject_isolation_affine B s hs hi
  exact (Fresh.isolation_comp_perm _ σ k).2 ha

#print axioms high_subject
#print axioms low_subject
#print axioms middle_five_all
#print axioms middleFiveArrangement_isolation
end Fresh.MiddleStepFiveArrangement
