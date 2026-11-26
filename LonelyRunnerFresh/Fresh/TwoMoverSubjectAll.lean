import Fresh.TwoMoverSubjectEnd
import Fresh.S2Below_Complete
import Fresh.OneMoverS1Self

/-!
Rules: 1–4, 8–18. All-subject assembly for the newly proved end-subject family.
The six unmoved subjects consume the established two-free-reading AP theorems
[PROVISIONAL: covering; counting tool, inherited only in these six branches].
The moved end subject uses its actual initial cascade displacement. The second
mover is separated from the compact physical group and isolates directly.
-/
open Classical
namespace Fresh.OneMover
open Fresh

theorem subject_end_large (x d : ℝ) (hx0 : 0 ≤ x) (hx : x < 1/6)
    (hd : 0 < d) (hretain : 2*(1-x)*(6-x) ≤ (1-6*x)*d) : 12 ≤ d := by
  have hp : 0 < 1-6*x := by linarith
  by_contra hn
  have hn' : d < 12 := lt_of_not_ge hn
  have hm := mul_lt_mul_of_pos_left hn' hp
  nlinarith [sq_nonneg x]

/-- The distant second mover isolates directly, retaining the moving subject
and all six physical AP speeds. -/
theorem subject_other_end_isolation (c x y : ℝ) (hx0 : 0 ≤ x) (hx : x < 1/6)
    (hd : 12 ≤ |y-(c+x)|) :
    Isolation (twoMover c (c+x) y (0 : Fin 8) 7) 7 := by
  set d := |y-(c+x)| with hddef
  have ha : 0 < d-6 := by linarith
  refine ⟨1/(8*(d-6)), by positivity, ?_⟩
  intro i hi7
  have hvi : |twoMover c (c+x) y (0 : Fin 8) 7 i - (c+x)| ≤ 6 := by
    by_cases hi0 : i = (0 : Fin 8)
    · simp [twoMover, hi0]
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
  have hlower : d-6 ≤ |z-y| := by rw [abs_sub_comm y z] at htriangle; linarith
  have htop : |z-y| ≤ 7*(d-6) := by linarith
  have hclear := thm8 ha hlower htop
  rw [distInt_abs_mul] at hclear
  simpa only [twoMover, show (7 : Fin 8) ≠ 0 by decide, ↓reduceIte] using hclear

/-- Every subject isolates for this physical two-mover arrangement. -/
theorem subject_end_all_isolation (c x y : ℝ)
    (hphysical : IsArrangement (twoMover c (c+x) y (0 : Fin 8) 7))
    (hx0 : 0 ≤ x) (hx : x < 1/6) (hd : 1-x ≤ |y-(c+x)|)
    (hretain : 2*(1-x)*(6-x) ≤ (1-6*x)*|y-(c+x)|) :
    ∀ k : Fin 8, Isolation (twoMover c (c+x) y (0 : Fin 8) 7) k := by
  have hd0 : 0 < |y-(c+x)| := lt_of_lt_of_le (by linarith) hd
  have hbig := subject_end_large x _ hx0 hx hd0 hretain
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
  · exact subject_other_end_isolation c x y hx0 hx hbig

/-- The exact retention inequality alone supplies the outsider separation on
0≤x<1/6. No additional size cutoff is imposed on this all-subject family. -/
theorem subject_end_all_of_retention (c x y : ℝ)
    (hphysical : IsArrangement (twoMover c (c+x) y (0 : Fin 8) 7))
    (hx0 : 0 ≤ x) (hx : x < 1/6)
    (hretain : 2*(1-x)*(6-x) ≤ (1-6*x)*|y-(c+x)|) :
    ∀ k : Fin 8, Isolation (twoMover c (c+x) y (0 : Fin 8) 7) k := by
  have hd0 : 0 < |y-(c+x)| := by
    have hx1 : 0 < 1-x := by linarith
    have hx6 : 0 < 6-x := by linarith
    have hp : 0 < 2*(1-x)*(6-x) := by positivity
    have hp' : 0 < 1-6*x := by linarith
    nlinarith
  have hbig := subject_end_large x _ hx0 hx hd0 hretain
  exact subject_end_all_isolation c x y hphysical hx0 hx (by linarith) hretain

#print axioms subject_end_large
#print axioms subject_other_end_isolation
#print axioms subject_end_all_isolation
#print axioms subject_end_all_of_retention
end Fresh.OneMover
