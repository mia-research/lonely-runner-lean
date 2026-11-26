import Fresh.MiddleStepFiveLarge
import Fresh.MiddleStepFiveArrangement

/-!
Rules:1–4,8–18. All-subject3+5 physical AP blocks at every step ratio
b≥18/5 with originalgapg≥32b/3. The same middle-anchor law retains independent
whole-lap cycle shifts, while upper subjects consume their full AP-core law.
[PROVISIONAL: counting tool] inherited exact ceiling/opening selection.
-/
open Classical
namespace Fresh.MiddleStepFiveLargeArrangement
open Fresh Fresh.OneMover Fresh.UnequalAPArrangement

theorem low_subject_large (c A b : ℝ) (hb : (18/5 : ℝ) ≤ b)
    (hgap : 32*b ≤ 3*(A-2))
    (k : Fin 8) (hk : (k : ℕ)<3) : Isolation (speeds c A 1 b 3) k := by
  let x := A-((k : ℕ) : ℝ)
  have hkR : ((k : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (show (k : ℕ) ≤ 2 by omega)
  have hxg : A-2 ≤ x := by dsimp [x]; linarith
  have hbpos : 0<b := by linarith
  have hg : 0<A-2 := by nlinarith
  have hx : 0<x := hg.trans_le hxg
  obtain ⟨t,ht,hcore,hfast⟩ := Fresh.MiddleStepFiveLarge.middle_five_large_readings hb (by nlinarith : 6*b ≤ x)
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

theorem middle_five_large_all (c A b : ℝ) (hb : (18/5 : ℝ) ≤ b)
    (hgap : 32*b ≤ 3*(A-2)) : ∀ k : Fin 8, Isolation (speeds c A 1 b 3) k := by
  intro k
  by_cases hk : (k : ℕ)<3
  · exact low_subject_large c A b hb hgap k hk
  · exact Fresh.MiddleStepFiveArrangement.high_subject c A b (by linarith) hgap k (by omega)

-- STANDING: DEFINITION
def MiddleFiveLargeArrangementClass (V : Fin 8 → ℝ) : Prop :=
  (∀ i, 0 < V i) ∧ Function.Injective V ∧
  ∃ (c A b B s : ℝ) (σ : Equiv.Perm (Fin 8)),
    (18/5 : ℝ) ≤ b ∧ 32*b ≤ 3*(A-2) ∧ s ≠ 0 ∧
    V = (fun i => B+s*speeds c A 1 b 3 (σ i))

theorem middleFiveLargeArrangement_isolation {V : Fin 8 → ℝ}
    (h : MiddleFiveLargeArrangementClass V) (k : Fin 8) : Isolation V k := by
  obtain ⟨hpos,hinj,c,A,b,B,s,σ,hb,hgap,hs,hV⟩ := h
  rw [hV]
  have hi := middle_five_large_all c A b hb hgap (σ k)
  have ha := subject_isolation_affine B s hs hi
  exact (Fresh.isolation_comp_perm _ σ k).2 ha

#print axioms low_subject_large
#print axioms middle_five_large_all
#print axioms middleFiveLargeArrangement_isolation
end Fresh.MiddleStepFiveLargeArrangement
