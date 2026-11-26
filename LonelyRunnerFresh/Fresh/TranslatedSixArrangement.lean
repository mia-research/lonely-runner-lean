import Fresh.TranslatedSixPositive
import Fresh.TwoMoverSubjectTransport

/-!
Rules: 1–4, 8–18. Eight moving speeds (c,c+1,c+a,...,c+a+5), every real
a>1. The ordered pair is separated from the six-term AP by no required gap.
The two endpoint subjects consume train(a) and train(a-1); six AP subjects
consume S2Complete. [PROVISIONAL: covering; counting tool] inherited from
these source families. The domain 0<a<1 is not asserted here; a=1 has a
physical collision. Signed affine scale, physical mirror and relabeling are
retained in the physical class.
-/
open Classical
namespace Fresh.TranslatedSixArrangement
open Fresh Fresh.OneMover Fresh.TranslatedSix

/-- Base AP with both endpoint labels replaced. -/
noncomputable def base (c a : ℝ) : Fin 8 → ℝ :=
  twoMover (c+a-1) c (c+1) 0 7

/-- Label order [0,7,1,2,3,4,5,6] displays the close pair first. -/
noncomputable def displayPerm : Equiv.Perm (Fin 8) :=
  Equiv.ofBijective
    (fun i => Fin.ofNat 8 (if i = 0 then 0 else if i = 1 then 7 else (i : ℕ)-1))
    (by decide)

noncomputable def speeds (c a : ℝ) : Fin 8 → ℝ := base c a ∘ displayPerm

theorem speeds_zero (c a : ℝ) : speeds c a 0 = c := by
  change base c a (0 : Fin 8) = c
  simp [base,twoMover]
theorem speeds_one (c a : ℝ) : speeds c a 1 = c+1 := by
  change base c a (7 : Fin 8) = c+1
  norm_num [base,twoMover,Fin.ext_iff]
theorem speeds_train (c a : ℝ) (j : Fin 6) :
    speeds c a (⟨(j : ℕ)+2, by omega⟩ : Fin 8) = c+a+(j : ℕ) := by
  have hp : displayPerm (⟨(j : ℕ)+2, by omega⟩ : Fin 8) = (⟨(j : ℕ)+1, by omega⟩ : Fin 8) := by
    fin_cases j <;> decide
  have h0 : (⟨(j : ℕ)+1, by omega⟩ : Fin 8) ≠ 0 := by
    intro he
    have hh := congrArg Fin.val he
    simp at hh
  have h7 : (⟨(j : ℕ)+1, by omega⟩ : Fin 8) ≠ 7 := by
    intro he
    have hh := congrArg Fin.val he
    change (j : ℕ)+1=7 at hh
    have := j.isLt
    omega
  change base c a (displayPerm _) = _
  rw [hp]
  simp only [base,twoMover,if_neg h0,if_neg h7]
  push_cast
  ring

theorem base_subject_zero (c a : ℝ) (ha : 1 < a) : Isolation (base c a) 0 := by
  obtain ⟨t,ht,hclear⟩ := translated_six_positive a (by linarith)
  refine ⟨t,ht,?_⟩
  intro i hi
  fin_cases i
  · exact False.elim (hi rfl)
  · have hc := hclear (a) (by simp [train])
    have he : base c a (1 : Fin 8) - base c a 0 = a := by norm_num [base,twoMover,Fin.ext_iff] <;> ring
    change (1/8 : ℝ) ≤ distInt ((base c a (1 : Fin 8)-base c a (0 : Fin 8))*t)
    rw [he]
    exact hc
  · have hc := hclear (a+1) (by simp [train])
    have he : base c a (2 : Fin 8) - base c a 0 = a+1 := by norm_num [base,twoMover,Fin.ext_iff] <;> ring
    change (1/8 : ℝ) ≤ distInt ((base c a (2 : Fin 8)-base c a (0 : Fin 8))*t)
    rw [he]
    exact hc
  · have hc := hclear (a+2) (by simp [train])
    have he : base c a (3 : Fin 8) - base c a 0 = a+2 := by norm_num [base,twoMover,Fin.ext_iff] <;> ring
    change (1/8 : ℝ) ≤ distInt ((base c a (3 : Fin 8)-base c a (0 : Fin 8))*t)
    rw [he]
    exact hc
  · have hc := hclear (a+3) (by simp [train])
    have he : base c a (4 : Fin 8) - base c a 0 = a+3 := by norm_num [base,twoMover,Fin.ext_iff] <;> ring
    change (1/8 : ℝ) ≤ distInt ((base c a (4 : Fin 8)-base c a (0 : Fin 8))*t)
    rw [he]
    exact hc
  · have hc := hclear (a+4) (by simp [train])
    have he : base c a (5 : Fin 8) - base c a 0 = a+4 := by norm_num [base,twoMover,Fin.ext_iff] <;> ring
    change (1/8 : ℝ) ≤ distInt ((base c a (5 : Fin 8)-base c a (0 : Fin 8))*t)
    rw [he]
    exact hc
  · have hc := hclear (a+5) (by simp [train])
    have he : base c a (6 : Fin 8) - base c a 0 = a+5 := by norm_num [base,twoMover,Fin.ext_iff] <;> ring
    change (1/8 : ℝ) ≤ distInt ((base c a (6 : Fin 8)-base c a (0 : Fin 8))*t)
    rw [he]
    exact hc
  · have hc := hclear (1) (by simp [train])
    have he : base c a (7 : Fin 8) - base c a 0 = 1 := by norm_num [base,twoMover,Fin.ext_iff] <;> ring
    change (1/8 : ℝ) ≤ distInt ((base c a (7 : Fin 8)-base c a (0 : Fin 8))*t)
    rw [he]
    exact hc

theorem base_subject_seven (c a : ℝ) (ha : 1 < a) : Isolation (base c a) 7 := by
  obtain ⟨t,ht,hclear⟩ := translated_six_positive (a-1) (by linarith)
  refine ⟨t,ht,?_⟩
  intro i hi
  fin_cases i
  · have hc := hclear (1) (by simp [train])
    have he : base c a (0 : Fin 8) - base c a 7 = -(1 : ℝ) := by norm_num [base,twoMover,Fin.ext_iff] <;> ring
    change (1/8 : ℝ) ≤ distInt ((base c a (0 : Fin 8)-base c a (7 : Fin 8))*t)
    rw [he]
    rw [neg_mul,Fresh.Localisation.distInt_neg]
    exact hc
  · have hc := hclear ((a-1)) (by simp [train])
    have he : base c a (1 : Fin 8) - base c a 7 = (a-1) := by norm_num [base,twoMover,Fin.ext_iff] <;> ring
    change (1/8 : ℝ) ≤ distInt ((base c a (1 : Fin 8)-base c a (7 : Fin 8))*t)
    rw [he]
    exact hc
  · have hc := hclear ((a-1)+1) (by simp [train])
    have he : base c a (2 : Fin 8) - base c a 7 = (a-1)+1 := by norm_num [base,twoMover,Fin.ext_iff] <;> ring
    change (1/8 : ℝ) ≤ distInt ((base c a (2 : Fin 8)-base c a (7 : Fin 8))*t)
    rw [he]
    exact hc
  · have hc := hclear ((a-1)+2) (by simp [train])
    have he : base c a (3 : Fin 8) - base c a 7 = (a-1)+2 := by norm_num [base,twoMover,Fin.ext_iff] <;> ring
    change (1/8 : ℝ) ≤ distInt ((base c a (3 : Fin 8)-base c a (7 : Fin 8))*t)
    rw [he]
    exact hc
  · have hc := hclear ((a-1)+3) (by simp [train])
    have he : base c a (4 : Fin 8) - base c a 7 = (a-1)+3 := by norm_num [base,twoMover,Fin.ext_iff] <;> ring
    change (1/8 : ℝ) ≤ distInt ((base c a (4 : Fin 8)-base c a (7 : Fin 8))*t)
    rw [he]
    exact hc
  · have hc := hclear ((a-1)+4) (by simp [train])
    have he : base c a (5 : Fin 8) - base c a 7 = (a-1)+4 := by norm_num [base,twoMover,Fin.ext_iff] <;> ring
    change (1/8 : ℝ) ≤ distInt ((base c a (5 : Fin 8)-base c a (7 : Fin 8))*t)
    rw [he]
    exact hc
  · have hc := hclear ((a-1)+5) (by simp [train])
    have he : base c a (6 : Fin 8) - base c a 7 = (a-1)+5 := by norm_num [base,twoMover,Fin.ext_iff] <;> ring
    change (1/8 : ℝ) ≤ distInt ((base c a (6 : Fin 8)-base c a (7 : Fin 8))*t)
    rw [he]
    exact hc
  · exact False.elim (hi rfl)

theorem base_all (c a : ℝ) (ha : 1 < a) : ∀ k : Fin 8, Isolation (base c a) k := by
  have hp1 : ∀ k : Fin 8, k ≠ 0 → k ≠ 7 → 0 < |c-((c+a-1)+((k : ℕ) : ℝ))| := by
    intro k hk0 hk7
    have hkl : 1 ≤ (k : ℕ) := by have := Fin.val_ne_of_ne hk0; simp at this; omega
    have hklR : (1 : ℝ) ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hkl
    apply abs_pos.mpr
    linarith
  have hp2 : ∀ k : Fin 8, k ≠ 0 → k ≠ 7 → 0 < |c+1-((c+a-1)+((k : ℕ) : ℝ))| := by
    intro k hk0 hk7
    have hkl : 1 ≤ (k : ℕ) := by have := Fin.val_ne_of_ne hk0; simp at this; omega
    have hklR : (1 : ℝ) ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hkl
    apply abs_pos.mpr
    linarith
  intro k
  fin_cases k
  · exact base_subject_zero c a ha
  · have hd1 := hp1 (1 : Fin 8) (by decide) (by decide)
    have hd2 := hp2 (1 : Fin 8) (by decide) (by decide)
    obtain ⟨T,hlo,hf,_⟩ := landing_twoMoverComplete_12345 (c+a-1) c (c+1) (1 : Fin 8) 0 7 (by decide) (by decide) (by decide) (by decide) hd1 hd2
    refine ⟨T,lt_of_lt_of_le (by positivity) hlo,?_⟩
    exact (Fresh.Cascade.isolatedAt_iff_lonelyAt _ _ _).2 hf.1
  · have hd1 := hp1 (2 : Fin 8) (by decide) (by decide)
    have hd2 := hp2 (2 : Fin 8) (by decide) (by decide)
    obtain ⟨T,hlo,hf,_⟩ := landing_twoMoverComplete_1234 (c+a-1) c (c+1) (2 : Fin 8) 0 7 (by decide) (by decide) (by decide) (by decide) hd1 hd2
    refine ⟨T,lt_of_lt_of_le (by positivity) hlo,?_⟩
    exact (Fresh.Cascade.isolatedAt_iff_lonelyAt _ _ _).2 hf.1
  · have hd1 := hp1 (3 : Fin 8) (by decide) (by decide)
    have hd2 := hp2 (3 : Fin 8) (by decide) (by decide)
    obtain ⟨T,hlo,hf,_⟩ := landing_twoMoverComplete_123 (c+a-1) c (c+1) (3 : Fin 8) 0 7 (by decide) (by decide) (by decide) (by decide) hd1 hd2
    refine ⟨T,lt_of_lt_of_le (by positivity) hlo,?_⟩
    exact (Fresh.Cascade.isolatedAt_iff_lonelyAt _ _ _).2 hf.1
  · have hd1 := hp1 (4 : Fin 8) (by decide) (by decide)
    have hd2 := hp2 (4 : Fin 8) (by decide) (by decide)
    obtain ⟨T,hlo,hf,_⟩ := landing_twoMoverComplete_123 (c+a-1) c (c+1) (4 : Fin 8) 0 7 (by decide) (by decide) (by decide) (by decide) hd1 hd2
    refine ⟨T,lt_of_lt_of_le (by positivity) hlo,?_⟩
    exact (Fresh.Cascade.isolatedAt_iff_lonelyAt _ _ _).2 hf.1
  · have hd1 := hp1 (5 : Fin 8) (by decide) (by decide)
    have hd2 := hp2 (5 : Fin 8) (by decide) (by decide)
    obtain ⟨T,hlo,hf,_⟩ := landing_twoMoverComplete_1234 (c+a-1) c (c+1) (5 : Fin 8) 0 7 (by decide) (by decide) (by decide) (by decide) hd1 hd2
    refine ⟨T,lt_of_lt_of_le (by positivity) hlo,?_⟩
    exact (Fresh.Cascade.isolatedAt_iff_lonelyAt _ _ _).2 hf.1
  · have hd1 := hp1 (6 : Fin 8) (by decide) (by decide)
    have hd2 := hp2 (6 : Fin 8) (by decide) (by decide)
    obtain ⟨T,hlo,hf,_⟩ := landing_twoMoverComplete_12345 (c+a-1) c (c+1) (6 : Fin 8) 0 7 (by decide) (by decide) (by decide) (by decide) hd1 hd2
    refine ⟨T,lt_of_lt_of_le (by positivity) hlo,?_⟩
    exact (Fresh.Cascade.isolatedAt_iff_lonelyAt _ _ _).2 hf.1
  · exact base_subject_seven c a ha

theorem speeds_all (c a : ℝ) (ha : 1 < a) :
    ∀ k : Fin 8, Isolation (speeds c a) k := by
  intro k
  exact (Fresh.isolation_comp_perm _ displayPerm k).2 (base_all c a ha (displayPerm k))

/-- Explicit positivity and injectivity retain a physical arrangement at any
signed scale, drift, physical mirror and labeling. -/
-- STANDING: DEFINITION
def TranslatedSixArrangementClass (v : Fin 8 → ℝ) : Prop :=
  (∀ i, 0 < v i) ∧ Function.Injective v ∧
  ∃ (c a B s : ℝ) (σ : Equiv.Perm (Fin 8)),
    1 < a ∧ s ≠ 0 ∧ v = (fun i => B+s*speeds c a (σ i))

theorem translatedSixArrangement_isolation {v : Fin 8 → ℝ}
    (h : TranslatedSixArrangementClass v) (k : Fin 8) : Isolation v k := by
  obtain ⟨hpos,hinj,c,a,B,s,σ,ha,hs,hv⟩ := h
  rw [hv]
  have hi := Fresh.OneMover.subject_isolation_affine B s hs (speeds_all c a ha (σ k))
  exact (Fresh.isolation_comp_perm _ σ k).2 hi

#print axioms speeds_zero
#print axioms speeds_one
#print axioms speeds_train
#print axioms base_subject_zero
#print axioms base_subject_seven
#print axioms base_all
#print axioms speeds_all
#print axioms translatedSixArrangement_isolation
end Fresh.TranslatedSixArrangement
