import Fresh.UnequalAPArrangement
import Fresh.MixedStepFour

/-!
Rules:1–4,8–18. Physical4+4 AP blocks, internal step ratio1:2.
The second block's subjects retain AP core step2 and carry the first block
of width3 to its named opening. The first block's subjects require the
mixed-lap family; they are not supplied by the previous compact-width law.
-/
open Classical
namespace Fresh.MixedStepFourArrangement
open Fresh Fresh.OneMover Fresh.APCoreOpening
open Fresh.UnequalAPArrangement

theorem high_subject (c A : ℝ) (hgap : (51/4 : ℝ) ≤ A-3)
    (k : Fin 8) (hk : 4 ≤ (k : ℕ)) : Isolation (speeds c A 1 2 4) k := by
  let x := A-3+2*(((k : ℕ)-4 : ℕ) : ℝ)
  let C := (Finset.range 4).image (fun j : ℕ => x+(j : ℝ))
  have hj0 := Nat.cast_nonneg (α := ℝ) ((k : ℕ)-4)
  have hxlo : (51/4 : ℝ) ≤ x := by dsimp [x]; linarith
  have hx : 0<x := lt_of_lt_of_le (by norm_num) hxlo
  have hC : ∀ d∈C, x≤d ∧ d≤x+3 := by
    intro d hd
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
    have hj3 : (j : ℝ) ≤ 3 := by exact_mod_cast (show j ≤ 3 by have := Finset.mem_range.mp hj; omega)
    have hj0 := Nat.cast_nonneg (α := ℝ) j
    constructor <;> linarith
  have hsep : 8*((3 : ℕ) : ℝ)*2 ≤ x*(7-((3 : ℕ) : ℝ)) := by norm_num; linarith
  have hwidth : (3 : ℝ)*(1/(8*2)+1/x) ≤ 3/4 := by
    have hi := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ)<51/4) hxlo
    norm_num at hi ⊢
    linarith
  obtain ⟨ht,hcore,hpacket⟩ := ap_core_clump_opening 3 (by norm_num) (by norm_num)
    (by norm_num : (0 : ℝ)<2) hx (by norm_num : (0 : ℝ)≤3) hC hsep hwidth
  refine ⟨_,ht,fun i hik => ?_⟩
  have hkp : ¬(k : ℕ)<4 := by omega
  by_cases hip : (i : ℕ)<4
  · have hj : 3-(i : ℕ)<4 := by omega
    have hjcast : ((3-(i : ℕ) : ℕ) : ℝ)=3-((i : ℕ) : ℝ) := by rw [Nat.cast_sub (by omega : (i : ℕ) ≤ 3)]; norm_num
    have hm : x+((3-(i : ℕ) : ℕ) : ℝ) ∈ C :=
      Finset.mem_image.mpr ⟨3-(i : ℕ),Finset.mem_range.mpr hj,rfl⟩
    have hd : speeds c A 1 2 4 i-speeds c A 1 2 4 k = -(x+((3-(i : ℕ) : ℕ) : ℝ)) := by
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
    have hd : speeds c A 1 2 4 i-speeds c A 1 2 4 k = (((i : ℕ) : ℝ)-((k : ℕ) : ℝ))*2 := by
      simp only [speeds,if_neg hip,if_neg hkp]
      rw [hicas,hkcas]
      ring
    have he : |speeds c A 1 2 4 i-speeds c A 1 2 4 k|=(n : ℝ)*2 := by
      rw [hd,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2),← natAbs_cast_abs i k]
    rw [← Fresh.Localisation.distInt_abs_mul,he]
    exact hcore n hn1 hnle

theorem low_subject (c A : ℝ) (hgap : (51/4 : ℝ) ≤ A-3)
    (k : Fin 8) (hk : (k : ℕ)<4) : Isolation (speeds c A 1 2 4) k := by
  let x := A-((k : ℕ) : ℝ)
  have hkR : ((k : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (show (k : ℕ) ≤ 3 by omega)
  have hxlo : (51/4 : ℝ) ≤ x := by dsimp [x]; linarith
  obtain ⟨t,ht,hcore,hfast⟩ := Fresh.MixedStepFour.mixed_four_two_tail_readings x hxlo
  refine ⟨t,ht,fun i hik => ?_⟩
  by_cases hip : (i : ℕ)<4
  · let n := (((i : ℕ) : ℤ)-((k : ℕ) : ℤ)).natAbs
    have hn1 : 1 ≤ n := by dsimp [n]; have := Fin.val_ne_of_ne hik; omega
    have hnle : n ≤ 3 := by dsimp [n]; omega
    have hd : speeds c A 1 2 4 i-speeds c A 1 2 4 k = ((i : ℕ) : ℝ)-((k : ℕ) : ℝ) := by simp [speeds,hip,hk]
    rw [← Fresh.Localisation.distInt_abs_mul,hd,← natAbs_cast_abs i k]
    exact hcore n hn1 hnle
  · have hj : (i : ℕ)-4 ≤ 3 := by have := i.isLt; omega
    have hd : speeds c A 1 2 4 i-speeds c A 1 2 4 k = x+2*(((i : ℕ)-4 : ℕ) : ℝ) := by simp [speeds,hip,hk,x]; ring
    rw [hd]
    exact hfast ((i : ℕ)-4) hj

theorem mixed_four_two_all (c A : ℝ) (hgap : (51/4 : ℝ) ≤ A-3) :
    ∀ k : Fin 8, Isolation (speeds c A 1 2 4) k := by
  intro k
  by_cases hk : (k : ℕ)<4
  · exact low_subject c A hgap k hk
  · exact high_subject c A hgap k (by omega)

-- STANDING: DEFINITION
def MixedFourTwoArrangementClass (V : Fin 8 → ℝ) : Prop :=
  (∀ i, 0 < V i) ∧ Function.Injective V ∧
  ∃ (c A B s : ℝ) (σ : Equiv.Perm (Fin 8)),
    (51/4 : ℝ) ≤ A-3 ∧ s ≠ 0 ∧
    V = (fun i => B+s*speeds c A 1 2 4 (σ i))

theorem mixedFourTwoArrangement_isolation {V : Fin 8 → ℝ}
    (h : MixedFourTwoArrangementClass V) (k : Fin 8) : Isolation V k := by
  obtain ⟨hpos,hinj,c,A,B,s,σ,hgap,hs,hV⟩ := h
  rw [hV]
  have hi := mixed_four_two_all c A hgap (σ k)
  have ha := subject_isolation_affine B s hs hi
  exact (Fresh.isolation_comp_perm _ σ k).2 ha

#print axioms high_subject
#print axioms low_subject
#print axioms mixed_four_two_all
#print axioms mixedFourTwoArrangement_isolation
end Fresh.MixedStepFourArrangement
