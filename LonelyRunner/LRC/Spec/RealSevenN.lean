import LonelyRunner.LRC.Spec.MergeSixN
import LonelyRunner.LRC.Spec.OrderSevenN
import LonelyRunner.LRC.Spec.RealSixN

/-!
# The conjecture at seven runners, for every arrangement of real speeds

2026-09-25.  Every set of at most six positive real disparities is lonely at `1/7`
(`existenceAtN_seven`), so the Lonely Runner Conjecture holds at seven runners for all real speeds
(`lonelyRunnerAtN_seven`).  The template is orders five and six (`RealFiveN`, `RealSixN`), one row
up:

* **Rows** over a whole-number basis of the disparities' span (`exists_rows`).
* **One class** (every two rows parallel: all disparities whole multiples of one unit): order seven
  on whole numbers (`lonely_seven_nat`, Barajas–Serra in framework form), scaled.
* **More than one class**: the exact merge for six rows (`exists_merge_model_six`) leaves at most
  five distinct readings; order six clears them at `1/6`; stepping (`lonely_of_model_many`)
  carries the model instant to a real time at `1/7`.  No density, no measure.

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.OrderSevenN

open MomentIterationN LRC.SpecN ConstructionN LRC.Stepping LRC.OrderFiveN LRC.OrderSixN

/-- **Order seven, real speeds.**  Every set of at most six positive real disparities is lonely at
`1/7`. -/
theorem existenceAtN_seven : ExistenceAtN 7 := by
  intro ds hpos hcard
  classical
  by_cases h3 : ds.card ≤ 5
  · obtain ⟨t, ht, hl⟩ := existenceAtN_six ds hpos (by simpa using h3)
    refine ⟨t, ht, fun d hd => le_trans ?_ (hl d hd)⟩
    norm_num
  have h4 : ds.card = 6 := by
    have : ds.card ≤ 6 := by simpa using hcard
    omega
  obtain ⟨d, β, hβ, l, hl0, a, hrep⟩ :=
    exists_rows ds (fun x hx => (hpos x hx).ne') (Finset.card_pos.mp (by omega))
  set e4 := ds.equivFinOfCardEq h4 with he4
  set xs : Fin 6 → ℝ := fun i => ((e4.symm i : ds) : ℝ) with hxs
  have hxs_mem : ∀ i, xs i ∈ ds := fun i => (e4.symm i).2
  have hxs_pos : ∀ i, 0 < xs i := fun i => hpos _ (hxs_mem i)
  set A : Fin 6 → Fin (d + 1) → ℤ := fun i => a (xs i) with hAdef
  have hxA : ∀ i, xs i = l * speed β (A i) := fun i => hrep _ (hxs_mem i)
  have hAnz : ∀ i, A i ≠ 0 := by
    intro i h
    have := hxA i
    rw [h, speed_zero, mul_zero] at this
    exact (hxs_pos i).ne' this
  have hcover : ∀ x ∈ ds, ∃ i, xs i = x := fun x hx => ⟨e4 ⟨x, hx⟩, by simp [hxs]⟩
  suffices H : ∃ t : ℝ, 0 < t ∧ ∀ i, (7 : ℝ)⁻¹ ≤ circDist (xs i * t) by
    obtain ⟨t, ht, hlt⟩ := H
    refine ⟨t, ht, fun x hx => ?_⟩
    obtain ⟨i, rfl⟩ := hcover x hx
    simpa using hlt i
  by_cases hallpar : ∀ i j, Parallel (A i) (A j)
  · -- one commensurability class: whole multiples of one unit
    obtain ⟨p, hp⟩ := Function.ne_iff.mp (hAnz 0)
    have hp' : (A 0 p : ℝ) ≠ 0 := by exact_mod_cast hp
    set u0 : ℝ := l * speed β (A 0) / (A 0 p : ℝ) with hu0
    have hxu : ∀ i, xs i = u0 * (A i p : ℝ) := by
      intro i
      have hsp := speed_mul_of_parallel β (hallpar i 0) p
      rw [hxA i, hu0]
      field_simp
      linear_combination hsp
    set mm : Fin 6 → ℕ := fun i => (A i p).natAbs with hmm
    have hxm : ∀ i, xs i = |u0| * mm i := by
      intro i
      have hpi := hxs_pos i
      rw [hxu i] at hpi ⊢
      rw [← abs_of_pos hpi, abs_mul, hmm]
      simp only [Nat.cast_natAbs, Int.cast_abs]
    have hmpos : ∀ i, 0 < mm i := by
      intro i
      rcases Nat.eq_zero_or_pos (mm i) with h | h
      · have := hxm i; rw [h] at this; simp at this; exact absurd this (hxs_pos i).ne'
      · exact h
    have hu : 0 < |u0| := by
      have := hxm 0
      have h0 := hxs_pos 0
      rw [this] at h0
      have : (0 : ℝ) < mm 0 := by exact_mod_cast hmpos 0
      exact pos_of_mul_pos_left h0 this.le
    obtain ⟨t, ht, hlt⟩ := lonely_seven_nat (Finset.univ.image mm)
      (fun x hx => by obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx; exact hmpos i)
      (le_trans Finset.card_image_le (by simp))
    refine ⟨t / |u0|, by positivity, fun i => ?_⟩
    rw [hxm i, show |u0| * (mm i : ℝ) * (t / |u0|) = (mm i : ℝ) * t by field_simp]
    exact hlt _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  · -- more than one class: the exact merge, order five, stepping
    push Not at hallpar
    obtain ⟨i0, j0', hnp⟩ := hallpar
    obtain ⟨y, hy, i1, j1, hij, hm⟩ := exists_merge_model_six A hAnz ⟨i0, j0', hnp⟩
    have hd : 0 < d := by
      by_contra hd0
      apply hnp
      intro q r
      have hqr : q = r := by
        apply Fin.ext
        have := q.isLt; have := r.isLt; omega
      rw [hqr]
    set j0 : Fin d := ⟨0, hd⟩
    set w : Fin 6 → ℝ := fun i => |((dotZ y (A i) : ℤ) : ℝ)| with hw
    set W : Finset ℝ := Finset.univ.image w with hW
    have hWpos : ∀ x ∈ W, 0 < x := by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact abs_pos.mpr (by exact_mod_cast hy i)
    have hWcard : W.card ≤ 5 := by
      have hle : W.card ≤ 6 := le_trans Finset.card_image_le (by simp)
      by_contra hgt
      have h4' : W.card = (Finset.univ : Finset (Fin 6)).card := by simp; omega
      have hinj := Finset.card_image_iff.mp h4'
      apply hij
      apply hinj (Finset.mem_coe.mpr (Finset.mem_univ i1)) (Finset.mem_coe.mpr (Finset.mem_univ j1))
      simp only [hw]
      rw [← Int.cast_abs, ← Int.cast_abs, Int.abs_eq_natAbs, Int.abs_eq_natAbs, hm]
    obtain ⟨τ, -, hlτ⟩ := existenceAtN_six W hWpos (by simpa using hWcard)
    have hτ : ∀ r ∈ Finset.univ.image A, ((7 : ℕ) - 1 : ℝ)⁻¹ ≤ circDist ((dotZ y r : ℝ) * τ) := by
      intro r hr
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hr
      have := hlτ (w i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
      simp only [hw] at this
      rw [circDist_abs_mul] at this
      have h54 : ((7 : ℕ) - 1 : ℝ) = ((6 : ℕ) : ℝ) := by norm_num
      rw [h54]; exact this
    obtain ⟨t, ht, hlt⟩ := lonely_of_model_many (n := 7) (by norm_num) hβ j0
      ⟨A 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩ y hτ
    refine ⟨t / |l|, div_pos ht (abs_pos.mpr hl0), fun i => ?_⟩
    have := hlt (A i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    rw [hxA i]
    rcases abs_choice l with h | h
    · rw [h, show l * speed β (A i) * (t / l) = speed β (A i) * t by field_simp]
      simpa using this
    · rw [h, show l * speed β (A i) * (t / -l) = -(speed β (A i) * t) by field_simp,
        circDist.symm_neg]
      simpa using this

/-- **The Lonely Runner Conjecture at seven runners**, for every injective arrangement of real
speeds, proved inside the framework. -/
theorem lonelyRunnerAtN_seven : LonelyRunnerAtN 7 :=
  lonelyRunnerAtN_of_existence existenceAtN_seven

end LRC.OrderSevenN
