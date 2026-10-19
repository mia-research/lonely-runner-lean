import LonelyRunner.LRC.Spec.ExactMergeN

/-! Transfer integer existence at an order to real speeds, using the preceding real order. -/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.RealTransferN
open MomentIterationN LRC.SpecN ConstructionN LRC.Stepping LRC.OrderFiveN

/-- Integer existence at `n + 3` and real existence at `n + 2` imply real existence at `n + 3`.
This covers every order at least three, using one exact merge and the stepping margin. -/
theorem existenceAtN_of_nat {n : ℕ}
    (hnat : ∀ S : Finset ℕ, (∀ d ∈ S, 0 < d) → S.card ≤ n + 2 →
      ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, ((n + 3 : ℕ) : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t))
    (hprev : ExistenceAtN (n + 2)) : ExistenceAtN (n + 3) := by
  intro ds hpos hcard
  classical
  by_cases hsmall : ds.card ≤ (n + 1)
  · obtain ⟨t, ht, hl⟩ := hprev ds hpos (by simpa using hsmall)
    refine ⟨t, ht, fun d hd => le_trans ?_ (hl d hd)⟩
    exact inv_anti₀ (by positivity) (by push_cast; linarith)
  have hfull : ds.card = (n + 2) := by
    have : ds.card ≤ (n + 2) := by simpa using hcard
    omega
  obtain ⟨d, β, hβ, l, hl0, a, hrep⟩ :=
    exists_rows ds (fun x hx => (hpos x hx).ne') (Finset.card_pos.mp (by omega))
  set enumeration := ds.equivFinOfCardEq hfull with henumeration
  set xs : Fin (n + 2) → ℝ := fun i => ((enumeration.symm i : ds) : ℝ) with hxs
  have hxs_mem : ∀ i, xs i ∈ ds := fun i => (enumeration.symm i).2
  have hxs_pos : ∀ i, 0 < xs i := fun i => hpos _ (hxs_mem i)
  set A : Fin (n + 2) → Fin (d + 1) → ℤ := fun i => a (xs i) with hAdef
  have hxA : ∀ i, xs i = l * speed β (A i) := fun i => hrep _ (hxs_mem i)
  have hAnz : ∀ i, A i ≠ 0 := by
    intro i h
    have := hxA i
    rw [h, speed_zero, mul_zero] at this
    exact (hxs_pos i).ne' this
  have hcover : ∀ x ∈ ds, ∃ i, xs i = x := fun x hx => ⟨enumeration ⟨x, hx⟩, by simp [hxs]⟩
  suffices H : ∃ t : ℝ, 0 < t ∧ ∀ i, ((n + 3) : ℝ)⁻¹ ≤ circDist (xs i * t) by
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
    set mm : Fin (n + 2) → ℕ := fun i => (A i p).natAbs with hmm
    have hxm : ∀ i, xs i = |u0| * mm i := by
      intro i
      have hpi := hxs_pos i
      rw [hxu i] at hpi ⊢
      rw [← abs_of_pos hpi, abs_mul, hmm]
      simp only [Nat.cast_natAbs, Int.cast_abs]
    have hmpos : ∀ i, 0 < mm i := by
      intro i
      rcases Nat.eq_zero_or_pos (mm i) with h | h
      · have hx := hxm i
        simp only [h, Nat.cast_zero, mul_zero] at hx
        exact absurd hx (hxs_pos i).ne'
      · exact h
    have hu : 0 < |u0| := by
      have := hxm 0
      have h0 := hxs_pos 0
      rw [this] at h0
      have : (0 : ℝ) < mm 0 := by exact_mod_cast hmpos 0
      exact pos_of_mul_pos_left h0 this.le
    obtain ⟨t, ht, hlt⟩ := hnat (Finset.univ.image mm)
      (fun x hx => by obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx; exact hmpos i)
      (le_trans Finset.card_image_le (by simp))
    refine ⟨t / |u0|, by positivity, fun i => ?_⟩
    rw [hxm i, show |u0| * (mm i : ℝ) * (t / |u0|) = (mm i : ℝ) * t by field_simp]
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      hlt _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  · -- More than one class: merge, apply the preceding order, then step.
    push Not at hallpar
    obtain ⟨i0, j0', hnp⟩ := hallpar
    obtain ⟨y, hy, i1, j1, hij, hm⟩ := LRC.OrderSevenN.exists_merge_model_all A hAnz ⟨i0, j0', hnp⟩
    have hd : 0 < d := by
      by_contra hd0
      apply hnp
      intro q r
      have hqr : q = r := by
        apply Fin.ext
        have := q.isLt; have := r.isLt; omega
      rw [hqr]
    set j0 : Fin d := ⟨0, hd⟩
    set w : Fin (n + 2) → ℝ := fun i => |((dotZ y (A i) : ℤ) : ℝ)| with hw
    set W : Finset ℝ := Finset.univ.image w with hW
    have hWpos : ∀ x ∈ W, 0 < x := by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact abs_pos.mpr (by exact_mod_cast hy i)
    have hWcard : W.card ≤ (n + 1) := by
      have hle : W.card ≤ (n + 2) := le_trans Finset.card_image_le (by simp)
      by_contra hgt
      have hfull' : W.card = (Finset.univ : Finset (Fin (n + 2))).card := by simp; omega
      have hinj := Finset.card_image_iff.mp hfull'
      apply hij
      apply hinj (Finset.mem_coe.mpr (Finset.mem_univ i1)) (Finset.mem_coe.mpr (Finset.mem_univ j1))
      simp only [hw]
      rw [← Int.cast_abs, ← Int.cast_abs, Int.abs_eq_natAbs, Int.abs_eq_natAbs, hm]
    obtain ⟨τ, -, hlτ⟩ := hprev W hWpos (by simpa using hWcard)
    have hτ : ∀ r ∈ Finset.univ.image A, (((n + 3) : ℕ) - 1 : ℝ)⁻¹ ≤ circDist ((dotZ y r : ℝ) * τ) := by
      intro r hr
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hr
      have := hlτ (w i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
      simp only [hw] at this
      rw [circDist_abs_mul] at this
      have hpreviousOrder : (((n + 3) : ℕ) - 1 : ℝ) = (((n + 2) : ℕ) : ℝ) := by push_cast; ring
      rw [hpreviousOrder]; exact this
    obtain ⟨t, ht, hlt⟩ := lonely_of_model_many (n := (n + 3)) (by omega) hβ j0
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

end LRC.RealTransferN
