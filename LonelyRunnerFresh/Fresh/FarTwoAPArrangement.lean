import Fresh.UnequalAPArrangement

/-!
Rules:1–4,8–18. Physical all-subject unequal-step two-AP assembly,
conditional on the explicit far mixed-packet law. Original gap≥96max(steps).
Every label, retained core reading, opposite packet member, and reflection
scale is derived. The signed fractional family H remains a stated premise
until its independent source is imported by a consuming file.
-/
open Classical
namespace Fresh.FarTwoAPArrangement
open Fresh Fresh.OneMover Fresh.UnequalAPArrangement Fresh.APCoreOpening

theorem low_subject_of
    (H : ∀ r : ℕ, 1 ≤ r → r ≤ 5 → ∀ x b : ℝ, 1 ≤ b → 96*b ≤ x →
      ∃ t : ℝ, 0<t ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ r → (1/8 : ℝ) ≤ distInt ((j : ℝ)*t)) ∧
        ∀ j : ℕ, j ≤ 6-r → (1/8 : ℝ) ≤ distInt ((x+(j : ℝ)*b)*t))
    (c A b : ℝ) (p : ℕ) (hp2 : 2 ≤ p) (hp6 : p ≤ 6)
    (hb : 1 ≤ b) (hgap : 96*b ≤ A-((p : ℝ)-1))
    (k : Fin 8) (hk : (k : ℕ)<p) : Isolation (speeds c A 1 b p) k := by
  let x := A-((k : ℕ) : ℝ)
  have hkR : ((k : ℕ) : ℝ) ≤ (p : ℝ)-1 := by
    have hh : ((k : ℕ) : ℝ)+1 ≤ p := by exact_mod_cast (show (k : ℕ)+1 ≤ p by omega)
    linarith
  have hx : 96*b ≤ x := by dsimp [x]; linarith
  obtain ⟨t,ht,hcore,hfast⟩ := H (p-1) (by omega) (by omega) x b hb hx
  refine ⟨t,ht,fun i hik => ?_⟩
  by_cases hip : (i : ℕ)<p
  · let n := (((i : ℕ) : ℤ)-((k : ℕ) : ℤ)).natAbs
    have hn1 : 1 ≤ n := by dsimp [n]; have := Fin.val_ne_of_ne hik; omega
    have hnle : n ≤ p-1 := by dsimp [n]; omega
    have hd : speeds c A 1 b p i-speeds c A 1 b p k = ((i : ℕ) : ℝ)-((k : ℕ) : ℝ) := by simp [speeds,hip,hk]
    rw [← Fresh.Localisation.distInt_abs_mul,hd,← natAbs_cast_abs i k]
    exact hcore n hn1 hnle
  · have hj : (i : ℕ)-p ≤ 6-(p-1) := by have := i.isLt; omega
    have hd : speeds c A 1 b p i-speeds c A 1 b p k = x+(((i : ℕ)-p : ℕ) : ℝ)*b := by simp [speeds,hip,hk,x]; ring
    rw [hd]
    exact hfast ((i : ℕ)-p) hj

theorem high_subject (c A b : ℝ) (p : ℕ) (hp2 : 2 ≤ p) (hp6 : p ≤ 6)
    (hb : 1 ≤ b) (hgap : 96*b ≤ A-((p : ℝ)-1))
    (k : Fin 8) (hk : p ≤ (k : ℕ)) : Isolation (speeds c A 1 b p) k := by
  let x := A-((p : ℝ)-1)+b*(((k : ℕ)-p : ℕ) : ℝ)
  let w := (p : ℝ)-1
  let C := (Finset.range p).image (fun j : ℕ => x+(j : ℝ))
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hpR6 : (p : ℝ) ≤ 6 := by exact_mod_cast hp6
  have hbpos : 0<b := by linarith
  have hj0 := Nat.cast_nonneg (α := ℝ) ((k : ℕ)-p)
  have hxlo : 96*b ≤ x := by dsimp [x]; nlinarith
  have hx96 : (96 : ℝ) ≤ x := by nlinarith
  have hx : 0<x := by linarith
  have hw0 : 0≤w := by dsimp [w]; linarith
  have hw5 : w≤5 := by dsimp [w]; linarith
  have hcastR : ((7-p : ℕ) : ℝ)=7-(p : ℝ) := by rw [Nat.cast_sub (by omega : p ≤ 7)]; norm_num
  have hcastL : ((p-1 : ℕ) : ℝ)=(p : ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ p)]; norm_num
  have hC : ∀ d∈C, x≤d ∧ d≤x+w := by
    intro d hd
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
    have hjR : (j : ℝ) ≤ (p : ℝ)-1 := by
      have hh : (j : ℝ)+1 ≤ p := by exact_mod_cast (show j+1 ≤ p by have := Finset.mem_range.mp hj; omega)
      linarith
    have hj0 := Nat.cast_nonneg (α := ℝ) j
    dsimp [w]
    constructor <;> linarith
  have hsep : 8*((7-p : ℕ) : ℝ)*b ≤ x*(7-((7-p : ℕ) : ℝ)) := by
    rw [hcastR]
    have hh1 := mul_le_mul_of_nonneg_right hpR hbpos.le
    have hh2 := mul_le_mul_of_nonneg_left hpR hx.le
    nlinarith
  have hwidth : w*(1/(8*b)+1/x) ≤ 3/4 := by
    have h8 : (8 : ℝ) ≤ 8*b := by linarith
    have hi1 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ)<8) h8
    have hi2 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ)<96) hx96
    have hs : 0≤1/(8*b)+1/x := by positivity
    have hm := mul_le_mul_of_nonneg_right hw5 hs
    norm_num at hi1 hi2 ⊢
    nlinarith
  obtain ⟨ht,hcore,hpacket⟩ := ap_core_clump_opening (7-p) (by omega) (by omega)
    hbpos hx hw0 hC hsep hwidth
  refine ⟨_,ht,fun i hik => ?_⟩
  have hkp : ¬(k : ℕ)<p := by omega
  by_cases hip : (i : ℕ)<p
  · have hj : p-1-(i : ℕ)<p := by omega
    have hjcast : ((p-1-(i : ℕ) : ℕ) : ℝ)=(p : ℝ)-1-((i : ℕ) : ℝ) := by rw [Nat.cast_sub (by omega : (i : ℕ) ≤ p-1),hcastL]
    have hm : x+((p-1-(i : ℕ) : ℕ) : ℝ) ∈ C :=
      Finset.mem_image.mpr ⟨p-1-(i : ℕ),Finset.mem_range.mpr hj,rfl⟩
    have hd : speeds c A 1 b p i-speeds c A 1 b p k = -(x+((p-1-(i : ℕ) : ℕ) : ℝ)) := by
      rw [hjcast]
      simp [speeds,hip,hkp,x]
      ring
    rw [hd,neg_mul,Fresh.Localisation.distInt_neg]
    exact hpacket _ hm
  · have hip' : p ≤ (i : ℕ) := by omega
    have hicas : (((i : ℕ)-p : ℕ) : ℝ)=((i : ℕ) : ℝ)-(p : ℝ) := by norm_cast
    have hkcas : (((k : ℕ)-p : ℕ) : ℝ)=((k : ℕ) : ℝ)-(p : ℝ) := by norm_cast
    let n := (((i : ℕ) : ℤ)-((k : ℕ) : ℤ)).natAbs
    have hn1 : 1 ≤ n := by dsimp [n]; have := Fin.val_ne_of_ne hik; omega
    have hnle : n ≤ 7-p := by dsimp [n]; have := i.isLt; have := k.isLt; omega
    have hd : speeds c A 1 b p i-speeds c A 1 b p k = (((i : ℕ) : ℝ)-((k : ℕ) : ℝ))*b := by
      simp only [speeds,if_neg hip,if_neg hkp]
      rw [hicas,hkcas]
      ring
    have he : |speeds c A 1 b p i-speeds c A 1 b p k|=(n : ℝ)*b := by
      rw [hd,abs_mul,abs_of_pos hbpos,← natAbs_cast_abs i k]
    rw [← Fresh.Localisation.distInt_abs_mul,he]
    exact hcore n hn1 hnle

theorem far_ge_one_all_of
    (H : ∀ r : ℕ, 1 ≤ r → r ≤ 5 → ∀ x b : ℝ, 1 ≤ b → 96*b ≤ x →
      ∃ t : ℝ, 0<t ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ r → (1/8 : ℝ) ≤ distInt ((j : ℝ)*t)) ∧
        ∀ j : ℕ, j ≤ 6-r → (1/8 : ℝ) ≤ distInt ((x+(j : ℝ)*b)*t))
    (c A b : ℝ) (p : ℕ) (hp2 : 2 ≤ p) (hp6 : p ≤ 6)
    (hb : 1 ≤ b) (hgap : 96*b ≤ A-((p : ℝ)-1)) :
    ∀ k : Fin 8, Isolation (speeds c A 1 b p) k := by
  intro k
  by_cases hk : (k : ℕ)<p
  · exact low_subject_of H c A b p hp2 hp6 hb hgap k hk
  · exact high_subject c A b p hp2 hp6 hb hgap k (by omega)

theorem reverse_reflect (c A b : ℝ) (hb : b ≠ 0) (p : ℕ) (hp2 : 2 ≤ p) (hp6 : p ≤ 6) :
    speeds c A 1 b p =
      (fun i => -b*speeds ((-c-A-((7-p : ℕ) : ℝ)*b)/b)
        ((A+((7-p : ℕ) : ℝ)*b-((p-1 : ℕ) : ℝ))/b) 1 (1/b) (8-p) (Fin.revPerm i)) := by
  funext i
  interval_cases p <;> fin_cases i <;> norm_num [speeds,Fin.revPerm,Fin.rev] <;> field_simp <;> ring

theorem far_positive_all_of
    (H : ∀ r : ℕ, 1 ≤ r → r ≤ 5 → ∀ x b : ℝ, 1 ≤ b → 96*b ≤ x →
      ∃ t : ℝ, 0<t ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ r → (1/8 : ℝ) ≤ distInt ((j : ℝ)*t)) ∧
        ∀ j : ℕ, j ≤ 6-r → (1/8 : ℝ) ≤ distInt ((x+(j : ℝ)*b)*t))
    (c A b : ℝ) (p : ℕ) (hp2 : 2 ≤ p) (hp6 : p ≤ 6)
    (hb : 0<b) (hgap : 96*max (1 : ℝ) b ≤ A-((p : ℝ)-1)) :
    ∀ k : Fin 8, Isolation (speeds c A 1 b p) k := by
  by_cases hb1 : 1 ≤ b
  · have hh : 96*b ≤ A-((p : ℝ)-1) := by rw [max_eq_right hb1] at hgap; exact hgap
    exact far_ge_one_all_of H c A b p hp2 hp6 hb1 hh
  · have hbsmall : b<1 := lt_of_not_ge hb1
    have h96 : (96 : ℝ) ≤ A-((p : ℝ)-1) := by rw [max_eq_left hbsmall.le] at hgap; simpa using hgap
    have hratio : (1 : ℝ) ≤ 1/b := by apply (le_div_iff₀ hb).2; linarith
    have hcastR : ((7-p : ℕ) : ℝ)=7-(p : ℝ) := by rw [Nat.cast_sub (by omega : p ≤ 7)]; norm_num
    have hcastL : ((p-1 : ℕ) : ℝ)=(p : ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ p)]; norm_num
    have hcastQ : ((8-p : ℕ) : ℝ)=8-(p : ℝ) := by rw [Nat.cast_sub (by omega : p ≤ 8)]; norm_num
    have he : (A+((7-p : ℕ) : ℝ)*b-((p-1 : ℕ) : ℝ))/b-(((8-p : ℕ) : ℝ)-1)=(A-((p : ℝ)-1))/b := by
      rw [hcastR,hcastL,hcastQ]
      field_simp
      <;> ring
    have hh : 96*(1/b) ≤ (A+((7-p : ℕ) : ℝ)*b-((p-1 : ℕ) : ℝ))/b-(((8-p : ℕ) : ℝ)-1) := by
      rw [he,show 96*(1/b)=96/b by ring]
      apply (div_le_div_iff₀ hb hb).2
      nlinarith
    have hnew := far_ge_one_all_of H ((-c-A-((7-p : ℕ) : ℝ)*b)/b)
      ((A+((7-p : ℕ) : ℝ)*b-((p-1 : ℕ) : ℝ))/b) (1/b) (8-p) (by omega) (by omega) hratio hh
    intro k
    have hi := hnew (Fin.revPerm k)
    have ha := subject_isolation_affine 0 (-b) (by linarith : -b ≠ 0) hi
    have ho := (Fresh.isolation_comp_perm _ Fin.revPerm k).2 ha
    rw [reverse_reflect c A b hb.ne' p hp2 hp6]
    simpa only [zero_add] using ho

-- STANDING: DEFINITION
def FarTwoAPBlockClass (V : Fin 8 → ℝ) : Prop :=
  (∀ i, 0 < V i) ∧ Function.Injective V ∧
  ∃ (c A b B s : ℝ) (p : ℕ) (σ : Equiv.Perm (Fin 8)),
    2 ≤ p ∧ p ≤ 6 ∧ 0<b ∧ 96*max (1 : ℝ) b ≤ A-((p : ℝ)-1) ∧ s ≠ 0 ∧
    V = (fun i => B+s*speeds c A 1 b p (σ i))

theorem farTwoAPBlock_isolation_of
    (H : ∀ r : ℕ, 1 ≤ r → r ≤ 5 → ∀ x b : ℝ, 1 ≤ b → 96*b ≤ x →
      ∃ t : ℝ, 0<t ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ r → (1/8 : ℝ) ≤ distInt ((j : ℝ)*t)) ∧
        ∀ j : ℕ, j ≤ 6-r → (1/8 : ℝ) ≤ distInt ((x+(j : ℝ)*b)*t))
    {V : Fin 8 → ℝ} (h : FarTwoAPBlockClass V) (k : Fin 8) : Isolation V k := by
  obtain ⟨hpos,hinj,c,A,b,B,s,p,σ,hp2,hp6,hb,hgap,hs,hV⟩ := h
  rw [hV]
  have hi := far_positive_all_of H c A b p hp2 hp6 hb hgap (σ k)
  have ha := subject_isolation_affine B s hs hi
  exact (Fresh.isolation_comp_perm _ σ k).2 ha

#print axioms low_subject_of
#print axioms high_subject
#print axioms far_ge_one_all_of
#print axioms reverse_reflect
#print axioms far_positive_all_of
#print axioms farTwoAPBlock_isolation_of
end Fresh.FarTwoAPArrangement
