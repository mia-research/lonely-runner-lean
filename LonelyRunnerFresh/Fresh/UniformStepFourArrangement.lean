import Fresh.MixedStepFourLowerArrangement

/-!
Rules:1–4,8–18. Physical4+4 assembly conditional on the uniform mixed-packet
law for b≥1,x≥21b. A checked reversal/reflection identity transports b<1
to1/b, giving all positive step ratios with gap≥21max(1,b).
The conditional hypothesis is explicit and must be discharged by its source.
-/
open Classical
namespace Fresh.UniformStepFourArrangement
open Fresh Fresh.OneMover Fresh.UnequalAPArrangement

theorem low_subject_uniform_of
    (H : ∀ x b : ℝ, 1 ≤ b → 21*b ≤ x →
      ∃ t : ℝ, 0<t ∧ ∀ d∈Fresh.MixedStepFour.mixedTrain x b, (1/8 : ℝ) ≤ distInt (d*t))
    (c A b : ℝ) (hb : 1 ≤ b) (hgap : 21*b ≤ A-3)
    (k : Fin 8) (hk : (k : ℕ)<4) : Isolation (speeds c A 1 b 4) k := by
  let x := A-((k : ℕ) : ℝ)
  have hkR : ((k : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (show (k : ℕ) ≤ 3 by omega)
  have hxg : A-3 ≤ x := by dsimp [x]; linarith
  have hx : 21*b ≤ x := hgap.trans hxg
  obtain ⟨t,ht,hclear⟩ := H x b hb hx
  have hcore : ∀ j : ℕ, 1 ≤ j → j ≤ 3 → (1/8 : ℝ) ≤ distInt ((j : ℝ)*t) := by
    intro j hj1 hj3
    interval_cases j <;> apply hclear <;> norm_num [Fresh.MixedStepFour.mixedTrain]
  have hfast : ∀ j : ℕ, j ≤ 3 → (1/8 : ℝ) ≤ distInt ((x+(j : ℝ)*b)*t) := by
    intro j hj3
    interval_cases j <;> apply hclear <;> norm_num [Fresh.MixedStepFour.mixedTrain]
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

theorem uniform_four_ge_one_all_of
    (H : ∀ x b : ℝ, 1 ≤ b → 21*b ≤ x →
      ∃ t : ℝ, 0<t ∧ ∀ d∈Fresh.MixedStepFour.mixedTrain x b, (1/8 : ℝ) ≤ distInt (d*t))
    (c A b : ℝ) (hb : 1 ≤ b) (hgap : 21*b ≤ A-3) :
    ∀ k : Fin 8, Isolation (speeds c A 1 b 4) k := by
  intro k
  by_cases hk : (k : ℕ)<4
  · exact low_subject_uniform_of H c A b hb hgap k hk
  · exact Fresh.MixedStepFourLowerArrangement.high_subject_lower c A b hb (by nlinarith) k (by omega)

theorem four_reverse_reflect (c A b : ℝ) (hb : b ≠ 0) :
    speeds c A 1 b 4 = (fun i => -b*speeds ((-c-A-3*b)/b) ((A+3*b-3)/b) 1 (1/b) 4 (Fin.revPerm i)) := by
  funext i
  fin_cases i
  · change speeds c A 1 b 4 (0 : Fin 8) = -b*speeds ((-c-A-3*b)/b) ((A+3*b-3)/b) 1 (1/b) 4 (7 : Fin 8)
    norm_num [speeds]
    field_simp
    <;> ring
  · change speeds c A 1 b 4 (1 : Fin 8) = -b*speeds ((-c-A-3*b)/b) ((A+3*b-3)/b) 1 (1/b) 4 (6 : Fin 8)
    norm_num [speeds]
    field_simp
    <;> ring
  · change speeds c A 1 b 4 (2 : Fin 8) = -b*speeds ((-c-A-3*b)/b) ((A+3*b-3)/b) 1 (1/b) 4 (5 : Fin 8)
    norm_num [speeds]
    field_simp
    <;> ring
  · change speeds c A 1 b 4 (3 : Fin 8) = -b*speeds ((-c-A-3*b)/b) ((A+3*b-3)/b) 1 (1/b) 4 (4 : Fin 8)
    norm_num [speeds]
    field_simp
    <;> ring
  · change speeds c A 1 b 4 (4 : Fin 8) = -b*speeds ((-c-A-3*b)/b) ((A+3*b-3)/b) 1 (1/b) 4 (3 : Fin 8)
    norm_num [speeds]
    field_simp
    <;> ring
  · change speeds c A 1 b 4 (5 : Fin 8) = -b*speeds ((-c-A-3*b)/b) ((A+3*b-3)/b) 1 (1/b) 4 (2 : Fin 8)
    norm_num [speeds]
    field_simp
    <;> ring
  · change speeds c A 1 b 4 (6 : Fin 8) = -b*speeds ((-c-A-3*b)/b) ((A+3*b-3)/b) 1 (1/b) 4 (1 : Fin 8)
    norm_num [speeds]
    field_simp
    <;> ring
  · change speeds c A 1 b 4 (7 : Fin 8) = -b*speeds ((-c-A-3*b)/b) ((A+3*b-3)/b) 1 (1/b) 4 (0 : Fin 8)
    norm_num [speeds]
    field_simp
    <;> ring

theorem uniform_four_positive_all_of
    (H : ∀ x b : ℝ, 1 ≤ b → 21*b ≤ x →
      ∃ t : ℝ, 0<t ∧ ∀ d∈Fresh.MixedStepFour.mixedTrain x b, (1/8 : ℝ) ≤ distInt (d*t))
    (c A b : ℝ) (hb : 0<b) (hgap : 21*max (1 : ℝ) b ≤ A-3) :
    ∀ k : Fin 8, Isolation (speeds c A 1 b 4) k := by
  by_cases hb1 : 1 ≤ b
  · have hh : 21*b ≤ A-3 := by rw [max_eq_right hb1] at hgap; exact hgap
    exact uniform_four_ge_one_all_of H c A b hb1 hh
  · have hbsmall : b<1 := lt_of_not_ge hb1
    have h21 : (21 : ℝ) ≤ A-3 := by rw [max_eq_left hbsmall.le] at hgap; simpa using hgap
    have hratio : (1 : ℝ) ≤ 1/b := by apply (le_div_iff₀ hb).2; linarith
    have he : (A+3*b-3)/b-3=(A-3)/b := by field_simp; ring
    have hh : 21*(1/b) ≤ (A+3*b-3)/b-3 := by
      rw [he,show 21*(1/b)=21/b by ring]
      apply (div_le_div_iff₀ hb hb).2
      nlinarith
    have hnew := uniform_four_ge_one_all_of H ((-c-A-3*b)/b) ((A+3*b-3)/b) (1/b) hratio hh
    intro k
    have hi := hnew (Fin.revPerm k)
    have ha := subject_isolation_affine 0 (-b) (by linarith : -b ≠ 0) hi
    have ho := (Fresh.isolation_comp_perm _ Fin.revPerm k).2 ha
    rw [four_reverse_reflect c A b hb.ne']
    simpa only [zero_add] using ho

-- STANDING: DEFINITION
def UniformFourArrangementClass (V : Fin 8 → ℝ) : Prop :=
  (∀ i, 0 < V i) ∧ Function.Injective V ∧
  ∃ (c A b B s : ℝ) (σ : Equiv.Perm (Fin 8)),
    0<b ∧ 21*max (1 : ℝ) b ≤ A-3 ∧ s ≠ 0 ∧
    V = (fun i => B+s*speeds c A 1 b 4 (σ i))

theorem uniformFourArrangement_isolation_of
    (H : ∀ x b : ℝ, 1 ≤ b → 21*b ≤ x →
      ∃ t : ℝ, 0<t ∧ ∀ d∈Fresh.MixedStepFour.mixedTrain x b, (1/8 : ℝ) ≤ distInt (d*t))
    {V : Fin 8 → ℝ} (h : UniformFourArrangementClass V) (k : Fin 8) : Isolation V k := by
  obtain ⟨hpos,hinj,c,A,b,B,s,σ,hb,hgap,hs,hV⟩ := h
  rw [hV]
  have hi := uniform_four_positive_all_of H c A b hb hgap (σ k)
  have ha := subject_isolation_affine B s hs hi
  exact (Fresh.isolation_comp_perm _ σ k).2 ha

#print axioms low_subject_uniform_of
#print axioms uniform_four_ge_one_all_of
#print axioms four_reverse_reflect
#print axioms uniform_four_positive_all_of
#print axioms uniformFourArrangement_isolation_of
end Fresh.UniformStepFourArrangement
