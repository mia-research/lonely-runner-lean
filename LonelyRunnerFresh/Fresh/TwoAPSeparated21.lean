import Fresh.TwoSixArrangement
import Fresh.FullThreeFiveArrangement
import Fresh.UniformStepFourArrangementAll
import Fresh.FarTwoAPArrangementAll

/-! Shared separation family for every two-block composition2+6,...,6+2.
The three native subject-role proofs join by block reversal and scale.
[PROVISIONAL: counting tool] inherited exact reference/cycle selections.
[PROVISIONAL: covering] inherited finite parameter joins and pair placement.
This is an arrangement separation hypothesis, not a global cascade bound.
-/
namespace Fresh.TwoAPSeparated21
open Fresh Fresh.OneMover Fresh.UnequalAPArrangement

 theorem separated_small (c A b : ℝ) (p : ℕ) (hp2 : 2 ≤ p) (hp4 : p ≤ 4)
    (hb : 0 < b) (hgap : 21*max (1 : ℝ) b ≤ A-((p : ℝ)-1)) :
    ∀ k : Fin 8, Isolation (speeds c A 1 b p) k := by
  have hM : 0 ≤ max (1 : ℝ) b := le_trans (by norm_num) (le_max_left _ _)
  interval_cases p
  · apply Fresh.TwoSixArrangement.two_six_all_subjects c A b hb
    norm_num at hgap ⊢
    nlinarith
  · apply Fresh.FullThreeFiveArrangement.three_five_all c A b hb
    norm_num at hgap ⊢
    nlinarith
  · exact Fresh.UniformStepFourArrangement.uniform_four_all c A b hb (by norm_num at hgap ⊢; exact hgap)

 theorem max_reciprocal {b : ℝ} (hb : 0 < b) :
    max (1 : ℝ) (1/b)=max (1 : ℝ) b/b := by
  by_cases h : 1 ≤ b
  · have hi : 1/b ≤ (1 : ℝ) := (div_le_one hb).2 h
    rw [max_eq_left hi,max_eq_right h]
    field_simp
  · have hle : b ≤ 1 := (lt_of_not_ge h).le
    have hi : (1 : ℝ) ≤ 1/b := (le_div_iff₀ hb).2 (by linarith)
    rw [max_eq_right hi,max_eq_left hle]

 theorem separated_all (c A b : ℝ) (p : ℕ) (hp2 : 2 ≤ p) (hp6 : p ≤ 6)
    (hb : 0 < b) (hgap : 21*max (1 : ℝ) b ≤ A-((p : ℝ)-1)) :
    ∀ k : Fin 8, Isolation (speeds c A 1 b p) k := by
  by_cases hp4 : p ≤ 4
  · exact separated_small c A b p hp2 hp4 hb hgap
  have hq2 : 2 ≤ 8-p := by omega
  have hq4 : 8-p ≤ 4 := by omega
  have hR : ((7-p : ℕ) : ℝ)=7-(p : ℝ) := by rw [Nat.cast_sub (by omega : p ≤ 7)]; norm_num
  have hL : ((p-1 : ℕ) : ℝ)=(p : ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ p)]; norm_num
  have hQ : ((8-p : ℕ) : ℝ)=8-(p : ℝ) := by rw [Nat.cast_sub (by omega : p ≤ 8)]; norm_num
  have he : (A+((7-p : ℕ) : ℝ)*b-((p-1 : ℕ) : ℝ))/b-(((8-p : ℕ) : ℝ)-1)=
      (A-((p : ℝ)-1))/b := by
    rw [hR,hL,hQ]
    field_simp <;> ring
  have hnewgap : 21*max (1 : ℝ) (1/b) ≤
      (A+((7-p : ℕ) : ℝ)*b-((p-1 : ℕ) : ℝ))/b-(((8-p : ℕ) : ℝ)-1) := by
    rw [he,max_reciprocal hb]
    rw [show 21*(max (1 : ℝ) b/b)=(21*max (1 : ℝ) b)/b by ring]
    exact div_le_div_of_nonneg_right hgap hb.le
  have hnew := separated_small ((-c-A-((7-p : ℕ) : ℝ)*b)/b)
    ((A+((7-p : ℕ) : ℝ)*b-((p-1 : ℕ) : ℝ))/b) (1/b) (8-p) hq2 hq4 (by positivity) hnewgap
  intro k
  have hi := hnew (Fin.revPerm k)
  have ha := subject_isolation_affine 0 (-b) (by linarith : -b ≠ 0) hi
  have ho := (Fresh.isolation_comp_perm _ Fin.revPerm k).2 ha
  rw [Fresh.FarTwoAPArrangement.reverse_reflect c A b hb.ne' p hp2 hp6]
  simpa only [zero_add] using ho

-- STANDING: DEFINITION
def SeparatedTwoAP21Class (V : Fin 8 → ℝ) : Prop :=
  (∀ i, 0 < V i) ∧ Function.Injective V ∧
  ∃ (c A b B s : ℝ) (p : ℕ) (σ : Equiv.Perm (Fin 8)),
    2 ≤ p ∧ p ≤ 6 ∧ 0 < b ∧ 21*max (1 : ℝ) b ≤ A-((p : ℝ)-1) ∧ s ≠ 0 ∧
    V=(fun i => B+s*speeds c A 1 b p (σ i))

theorem separatedTwoAP21_isolation {V : Fin 8 → ℝ}
    (h : SeparatedTwoAP21Class V) (k : Fin 8) : Isolation V k := by
  obtain ⟨hpos,hinj,c,A,b,B,s,p,σ,hp2,hp6,hb,hgap,hs,hV⟩ := h
  rw [hV]
  have hi := separated_all c A b p hp2 hp6 hb hgap (σ k)
  have ha := subject_isolation_affine B s hs hi
  exact (Fresh.isolation_comp_perm _ σ k).2 ha

theorem far96_imp_separated21 {V : Fin 8 → ℝ}
    (h : Fresh.FarTwoAPArrangement.FarTwoAPBlockClass V) : SeparatedTwoAP21Class V := by
  obtain ⟨hpos,hinj,c,A,b,B,s,p,σ,hp2,hp6,hb,hgap,hs,hV⟩ := h
  refine ⟨hpos,hinj,c,A,b,B,s,p,σ,hp2,hp6,hb,?_,hs,hV⟩
  have hM : 0 ≤ max (1 : ℝ) b := le_trans (by norm_num) (le_max_left _ _)
  nlinarith

#print axioms separated_small
#print axioms max_reciprocal
#print axioms separated_all
#print axioms separatedTwoAP21_isolation
#print axioms far96_imp_separated21
end Fresh.TwoAPSeparated21
