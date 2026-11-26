import Fresh.MiddleStepFiveAll
import Fresh.MiddleStepFiveArrangement

/-!
Rules:1–4,8–18. Physical3+5 AP arrangement, all8subjects, every real
step ratio b≥6/7, original gapg≥32b/3. Two middle phase bands and their
cycle repeat remove the prior extra polynomial condition. Physical
positive/distinct speeds, signedscale,mirror,drift,labels remain explicit.
[PROVISIONAL: counting tool; covering] inherited selectors/parameter split.
-/
open Classical
namespace Fresh.MiddleStepFiveArrangementAll
open Fresh Fresh.OneMover Fresh.UnequalAPArrangement

theorem low_subject_all (c A b : ℝ) (hb : (6/7 : ℝ) ≤ b)
    (hgap : 32*b ≤ 3*(A-2))
    (k : Fin 8) (hk : (k : ℕ)<3) : Isolation (speeds c A 1 b 3) k := by
  let x := A-((k : ℕ) : ℝ)
  have hkR : ((k : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (show (k : ℕ) ≤ 2 by omega)
  have hxg : A-2 ≤ x := by dsimp [x]; linarith
  have hbpos : 0<b := by linarith
  have hg : 0<A-2 := by nlinarith
  have hx : 0<x := hg.trans_le hxg
  obtain ⟨t,ht,hcore,hfast⟩ := Fresh.MiddleStepFiveAll.middle_five_all_readings hb (by nlinarith : 6*b ≤ x)
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

theorem middle_five_all_subjects (c A b : ℝ) (hb : (6/7 : ℝ) ≤ b)
    (hgap : 32*b ≤ 3*(A-2)) : ∀ k : Fin 8, Isolation (speeds c A 1 b 3) k := by
  intro k
  by_cases hk : (k : ℕ)<3
  · exact low_subject_all c A b hb hgap k hk
  · exact Fresh.MiddleStepFiveArrangement.high_subject c A b (by linarith) hgap k (by omega)

-- STANDING: DEFINITION
def MiddleFiveAllArrangementClass (V : Fin 8 → ℝ) : Prop :=
  (∀ i, 0 < V i) ∧ Function.Injective V ∧
  ∃ (c A b B s : ℝ) (σ : Equiv.Perm (Fin 8)),
    (6/7 : ℝ) ≤ b ∧ 32*b ≤ 3*(A-2) ∧ s ≠ 0 ∧
    V = (fun i => B+s*speeds c A 1 b 3 (σ i))

theorem middleFiveAllArrangement_isolation {V : Fin 8 → ℝ}
    (h : MiddleFiveAllArrangementClass V) (k : Fin 8) : Isolation V k := by
  obtain ⟨hpos,hinj,c,A,b,B,s,σ,hb,hgap,hs,hV⟩ := h
  rw [hV]
  have hi := middle_five_all_subjects c A b hb hgap (σ k)
  have ha := subject_isolation_affine B s hs hi
  exact (Fresh.isolation_comp_perm _ σ k).2 ha

#print axioms low_subject_all
#print axioms middle_five_all_subjects
#print axioms middleFiveAllArrangement_isolation
end Fresh.MiddleStepFiveArrangementAll
