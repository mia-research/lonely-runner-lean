import Fresh.TwoMoverSubjectAll

/-!
Rules: 1–4, 8–18. Unbounded extension of the all-subject family:
x<1/6 has no lower bound. In addition to exact first-exit retention for
subject c+x, 4(6-x)≤3d makes the other moved subject clear directly.
This places both moved subjects outside the retained six-speed AP group.
The threshold is derived by exact triangle inequalities, not sampling.
[PROVISIONAL: covering; counting tool] inherited only through S2 branches.
-/
open Classical
namespace Fresh.OneMover
open Fresh

theorem subject_other_separated_isolation (c x y : ℝ) (hx : x < 1/6)
    (hd : 4*(6-x) ≤ 3*|y-(c+x)|) :
    Isolation (twoMover c (c+x) y (0 : Fin 8) 7) 7 := by
  set d := |y-(c+x)| with hddef
  have hb : 0 < 6-x := by linarith
  have ha : 0 < d-(6-x) := by linarith
  refine ⟨1/(8*(d-(6-x))), by positivity, ?_⟩
  intro i hi7
  have hvi : |twoMover c (c+x) y (0 : Fin 8) 7 i - (c+x)| ≤ 6-x := by
    by_cases hi0 : i = (0 : Fin 8)
    · simp [twoMover, hi0]
      linarith
    · have hil : 1 ≤ (i : ℕ) := by have := Fin.val_ne_of_ne hi0; simp at this; omega
      have hir : (i : ℕ) ≤ 6 := by have := i.isLt; have := Fin.val_ne_of_ne hi7; simp at this; omega
      have hilR : (1 : ℝ) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hil
      have hirR : (((i : ℕ) : ℝ)) ≤ 6 := by exact_mod_cast hir
      simp only [twoMover, hi0, hi7, ↓reduceIte]
      rw [show c+((i : ℕ) : ℝ)-(c+x) = ((i : ℕ) : ℝ)-x by ring, abs_of_pos (by linarith)]
      linarith
  set z := twoMover c (c+x) y (0 : Fin 8) 7 i
  have htriangle : d ≤ |y-z| + |z-(c+x)| := by
    rw [hddef]
    exact le_trans (le_of_eq (congrArg abs (show y-(c+x) = (y-z)+(z-(c+x)) by ring))) (abs_add_le _ _)
  have hupper : |z-y| ≤ |z-(c+x)| + d := by
    rw [hddef, abs_sub_comm y (c+x)]
    exact le_trans (le_of_eq (congrArg abs (show z-y = (z-(c+x))+((c+x)-y) by ring))) (abs_add_le _ _)
  have hlower : d-(6-x) ≤ |z-y| := by rw [abs_sub_comm y z] at htriangle; linarith
  have htop : |z-y| ≤ 7*(d-(6-x)) := by linarith
  have hclear := thm8 ha hlower htop
  rw [distInt_abs_mul] at hclear
  simpa only [twoMover, show (7 : Fin 8) ≠ 0 by decide, ↓reduceIte] using hclear

theorem subject_end_all_separated (c x y : ℝ)
    (hphysical : IsArrangement (twoMover c (c+x) y (0 : Fin 8) 7))
    (hx : x < 1/6) (hd : 1-x ≤ |y-(c+x)|)
    (hsep : 4*(6-x) ≤ 3*|y-(c+x)|)
    (hretain : 2*(1-x)*(6-x) ≤ (1-6*x)*|y-(c+x)|) :
    ∀ k : Fin 8, Isolation (twoMover c (c+x) y (0 : Fin 8) 7) k := by
  have hd0 : 0 < |y-(c+x)| := lt_of_lt_of_le (by linarith) hd
  have hp1 : ∀ k : Fin 8, k ≠ 0 → k ≠ 7 → 0 < |c+x-(c+((k : ℕ) : ℝ))| := by
    intro k hk0 hk7
    have hkl : 1 ≤ (k : ℕ) := by have := Fin.val_ne_of_ne hk0; simp at this; omega
    have hklR : (1 : ℝ) ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hkl
    apply abs_pos.mpr
    linarith
  have hp2 : ∀ k : Fin 8, k ≠ 0 → k ≠ 7 → 0 < |y-(c+((k : ℕ) : ℝ))| := by
    intro k hk0 hk7
    apply abs_pos.mpr
    intro h
    have he : twoMover c (c+x) y (0 : Fin 8) 7 7 = twoMover c (c+x) y (0 : Fin 8) 7 k := by
      simp only [twoMover, hk0, hk7, show (7 : Fin 8) ≠ 0 by decide, ↓reduceIte]
      linarith
    exact hk7 (hphysical.2 he).symm
  intro k
  fin_cases k
  · obtain ⟨T, hT, _, hfirst⟩ := subject_end_first c x y hphysical hx hd hretain
    exact ⟨T, hT, hfirst.1⟩
  · have hd1 := hp1 (1 : Fin 8) (by decide) (by decide)
    have hd2 := hp2 (1 : Fin 8) (by decide) (by decide)
    obtain ⟨T, hlo, hf, _⟩ := landing_twoMoverComplete_12345 c (c+x) y (1 : Fin 8) 0 7 (by decide) (by decide) (by decide) (by decide) hd1 hd2
    refine ⟨T, lt_of_lt_of_le (by positivity) hlo, ?_⟩
    exact (Fresh.Cascade.isolatedAt_iff_lonelyAt _ _ _).2 hf.1
  · have hd1 := hp1 (2 : Fin 8) (by decide) (by decide)
    have hd2 := hp2 (2 : Fin 8) (by decide) (by decide)
    obtain ⟨T, hlo, hf, _⟩ := landing_twoMoverComplete_1234 c (c+x) y (2 : Fin 8) 0 7 (by decide) (by decide) (by decide) (by decide) hd1 hd2
    refine ⟨T, lt_of_lt_of_le (by positivity) hlo, ?_⟩
    exact (Fresh.Cascade.isolatedAt_iff_lonelyAt _ _ _).2 hf.1
  · have hd1 := hp1 (3 : Fin 8) (by decide) (by decide)
    have hd2 := hp2 (3 : Fin 8) (by decide) (by decide)
    obtain ⟨T, hlo, hf, _⟩ := landing_twoMoverComplete_123 c (c+x) y (3 : Fin 8) 0 7 (by decide) (by decide) (by decide) (by decide) hd1 hd2
    refine ⟨T, lt_of_lt_of_le (by positivity) hlo, ?_⟩
    exact (Fresh.Cascade.isolatedAt_iff_lonelyAt _ _ _).2 hf.1
  · have hd1 := hp1 (4 : Fin 8) (by decide) (by decide)
    have hd2 := hp2 (4 : Fin 8) (by decide) (by decide)
    obtain ⟨T, hlo, hf, _⟩ := landing_twoMoverComplete_123 c (c+x) y (4 : Fin 8) 0 7 (by decide) (by decide) (by decide) (by decide) hd1 hd2
    refine ⟨T, lt_of_lt_of_le (by positivity) hlo, ?_⟩
    exact (Fresh.Cascade.isolatedAt_iff_lonelyAt _ _ _).2 hf.1
  · have hd1 := hp1 (5 : Fin 8) (by decide) (by decide)
    have hd2 := hp2 (5 : Fin 8) (by decide) (by decide)
    obtain ⟨T, hlo, hf, _⟩ := landing_twoMoverComplete_1234 c (c+x) y (5 : Fin 8) 0 7 (by decide) (by decide) (by decide) (by decide) hd1 hd2
    refine ⟨T, lt_of_lt_of_le (by positivity) hlo, ?_⟩
    exact (Fresh.Cascade.isolatedAt_iff_lonelyAt _ _ _).2 hf.1
  · have hd1 := hp1 (6 : Fin 8) (by decide) (by decide)
    have hd2 := hp2 (6 : Fin 8) (by decide) (by decide)
    obtain ⟨T, hlo, hf, _⟩ := landing_twoMoverComplete_12345 c (c+x) y (6 : Fin 8) 0 7 (by decide) (by decide) (by decide) (by decide) hd1 hd2
    refine ⟨T, lt_of_lt_of_le (by positivity) hlo, ?_⟩
    exact (Fresh.Cascade.isolatedAt_iff_lonelyAt _ _ _).2 hf.1
  · exact subject_other_separated_isolation c x y hx hsep


#print axioms subject_other_separated_isolation
#print axioms subject_end_all_separated
end Fresh.OneMover
