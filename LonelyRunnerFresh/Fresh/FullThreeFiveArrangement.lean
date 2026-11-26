import Fresh.ThreePacketPhase
import Fresh.MiddleStepFiveArrangementAll

/-!
Rules:1–4,8–18. Every positive step ratio for physical3+5 AP blocks,
original gap at least32/3 times the larger internal step. Larger ratios use
the five-packet middle anchor. Smaller ratios retain the low core directly;
upper subjects normalize their positive unit and use the proved three-packet
phase law, retaining all physical readings and labels.
[PROVISIONAL: counting tool; covering] inherited selectors/parameter joins.
-/
open Classical
namespace Fresh.FullThreeFiveArrangement
open Fresh Fresh.OneMover Fresh.APCoreOpening Fresh.UnequalAPArrangement

theorem low_small (c A b : ℝ) (hb : 0<b) (hbhi : b ≤ 6/7)
    (hgap : (32/3 : ℝ) ≤ A-2) (k : Fin 8) (hk : (k : ℕ)<3) :
    Isolation (speeds c A 1 b 3) k := by
  let x := A-((k : ℕ) : ℝ)
  let C := (Finset.range 5).image (fun j : ℕ => x+(j : ℝ)*b)
  have hkR : ((k : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (show (k : ℕ) ≤ 2 by omega)
  have hxlo : (32/3 : ℝ) ≤ x := by dsimp [x]; linarith
  have hx : 0<x := by linarith
  have hC : ∀ d∈C, x≤d ∧ d≤x+4*b := by
    intro d hd
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
    have hj4 : (j : ℝ) ≤ 4 := by exact_mod_cast (show j ≤ 4 by have := Finset.mem_range.mp hj; omega)
    have hj0 := Nat.cast_nonneg (α := ℝ) j
    constructor <;> nlinarith
  have hsep : 8*((2 : ℕ) : ℝ)*1 ≤ x*(7-((2 : ℕ) : ℝ)) := by norm_num; linarith
  have hwidth : (4*b)*(1/(8*1)+1/x) ≤ 3/4 := by
    have hi := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ)<32/3) hxlo
    norm_num at hi ⊢
    simp only [one_div] at hi ⊢
    have hh : (1/8 : ℝ)+1/x ≤ 7/32 := by simpa only [one_div] using (show (1/8 : ℝ)+x⁻¹ ≤ 7/32 by linarith)
    have hm := mul_le_mul_of_nonneg_left hh (by linarith : 0 ≤ 4*b)
    nlinarith
  obtain ⟨ht,hcore,hpacket⟩ := ap_core_clump_opening 2 (by norm_num) (by norm_num)
    (by norm_num : (0 : ℝ)<1) hx (by linarith : 0 ≤ 4*b) hC hsep hwidth
  refine ⟨_,ht,fun i hik => ?_⟩
  by_cases hip : (i : ℕ)<3
  · let n := (((i : ℕ) : ℤ)-((k : ℕ) : ℤ)).natAbs
    have hn1 : 1 ≤ n := by dsimp [n]; have := Fin.val_ne_of_ne hik; omega
    have hnle : n ≤ 2 := by dsimp [n]; omega
    have hd : speeds c A 1 b 3 i-speeds c A 1 b 3 k = ((i : ℕ) : ℝ)-((k : ℕ) : ℝ) := by simp [speeds,hip,hk]
    rw [← Fresh.Localisation.distInt_abs_mul,hd,← natAbs_cast_abs i k]
    simpa [n] using hcore n hn1 hnle
  · have hj : (i : ℕ)-3<5 := by have := i.isLt; omega
    have hm : x+(((i : ℕ)-3 : ℕ) : ℝ)*b ∈ C :=
      Finset.mem_image.mpr ⟨(i : ℕ)-3,Finset.mem_range.mpr hj,rfl⟩
    have hd : speeds c A 1 b 3 i-speeds c A 1 b 3 k = x+(((i : ℕ)-3 : ℕ) : ℝ)*b := by simp [speeds,hip,hk,x]; ring
    rw [hd]
    exact hpacket _ hm

theorem high_small (c A b : ℝ) (hb : 0<b) (hbhi : b ≤ 6/7)
    (hgap : (32/3 : ℝ) ≤ A-2) (k : Fin 8) (hk : 3 ≤ (k : ℕ)) :
    Isolation (speeds c A 1 b 3) k := by
  let x := (A-2+b*(((k : ℕ)-3 : ℕ) : ℝ))/b
  let d := 1/b
  have hd1 : (1 : ℝ) ≤ d := by dsimp [d]; apply (le_div_iff₀ hb).2; linarith
  have hj0 := Nat.cast_nonneg (α := ℝ) ((k : ℕ)-3)
  have hx : (32/3 : ℝ)*d ≤ x := by
    dsimp [x,d]
    rw [show (32/3 : ℝ)*(1/b)=(32/3)/b by ring]
    apply div_le_div_of_nonneg_right _ hb.le
    have hm := mul_nonneg hb.le hj0
    linarith
  obtain ⟨T,hT,hcore,hpacket⟩ := Fresh.ThreePacketPhase.three_packet_all hd1 hx
  refine ⟨T/b,by positivity,fun i hik => ?_⟩
  have hkp : ¬(k : ℕ)<3 := by omega
  by_cases hip : (i : ℕ)<3
  · have hj : 2-(i : ℕ) ≤ 2 := by omega
    have hjcast : ((2-(i : ℕ) : ℕ) : ℝ)=2-((i : ℕ) : ℝ) := by rw [Nat.cast_sub (by omega : (i : ℕ) ≤ 2)]; norm_num
    have he : (speeds c A 1 b 3 i-speeds c A 1 b 3 k)*(T/b) =
        -((x+((2-(i : ℕ) : ℕ) : ℝ)*d)*T) := by
      rw [hjcast]
      simp only [speeds,if_pos hip,if_neg hkp]
      dsimp [x,d]
      field_simp
      <;> ring
    rw [he,Fresh.Localisation.distInt_neg]
    exact hpacket (2-(i : ℕ)) hj
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
      rw [hd,abs_mul,abs_of_pos hb,← natAbs_cast_abs i k]
    rw [← Fresh.Localisation.distInt_abs_mul,he]
    have hmul : ((n : ℝ)*b)*(T/b)=(n : ℝ)*T := by field_simp
    rw [hmul]
    exact hcore n hn1 hnle

theorem three_five_all (c A b : ℝ) (hb : 0<b)
    (hgap : (32/3 : ℝ)*max (1 : ℝ) b ≤ A-2) :
    ∀ k : Fin 8, Isolation (speeds c A 1 b 3) k := by
  by_cases hblo : (6/7 : ℝ) ≤ b
  · have hmax := le_max_right (1 : ℝ) b
    have hh : 32*b ≤ 3*(A-2) := by nlinarith
    exact Fresh.MiddleStepFiveArrangementAll.middle_five_all_subjects c A b hblo hh
  · have hbhi : b ≤ 6/7 := le_of_lt (lt_of_not_ge hblo)
    have hmax : max (1 : ℝ) b=1 := max_eq_left (by linarith)
    have hh : (32/3 : ℝ) ≤ A-2 := by rw [hmax] at hgap; simpa using hgap
    intro k
    by_cases hk : (k : ℕ)<3
    · exact low_small c A b hb hbhi hh k hk
    · exact high_small c A b hb hbhi hh k (by omega)

-- STANDING: DEFINITION
def FullThreeFiveArrangementClass (V : Fin 8 → ℝ) : Prop :=
  (∀ i, 0 < V i) ∧ Function.Injective V ∧
  ∃ (c A b B s : ℝ) (σ : Equiv.Perm (Fin 8)),
    0<b ∧ (32/3 : ℝ)*max (1 : ℝ) b ≤ A-2 ∧ s ≠ 0 ∧
    V = (fun i => B+s*speeds c A 1 b 3 (σ i))

theorem fullThreeFiveArrangement_isolation {V : Fin 8 → ℝ}
    (h : FullThreeFiveArrangementClass V) (k : Fin 8) : Isolation V k := by
  obtain ⟨hpos,hinj,c,A,b,B,s,σ,hb,hgap,hs,hV⟩ := h
  rw [hV]
  have hi := three_five_all c A b hb hgap (σ k)
  have ha := subject_isolation_affine B s hs hi
  exact (Fresh.isolation_comp_perm _ σ k).2 ha

#print axioms low_small
#print axioms high_small
#print axioms three_five_all
#print axioms fullThreeFiveArrangement_isolation
end Fresh.FullThreeFiveArrangement
