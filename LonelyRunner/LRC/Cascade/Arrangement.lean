import LonelyRunner.LRC.Cascade.Flanks

/-!
# The framework's objects on an arrangement

Part of the cascade artefact (`LRC/Cascade/`).  Threshold `1/8`, eight runners.

Everything else in the artefact is stated on a **difference set** `ds : Finset ℝ`.  That form is
equivalent to the conjecture but demands machinery the conjecture does not: `Finset ℝ` forces
decidable equality, it **collapses duplicates** and so destroys the indexing, and `card ≤ 7` admits
difference sets no arrangement can produce.  Most importantly the **arrangement is gone** — gaps, the
AP structure, the coupling across the eight subjects, and "the subject and its two neighbours" are
arrangement-level and are not expressible in `ds` alone.

This module states the same objects on the arrangement itself, where the indexing survives.  See
`docs/n8/TARGET_AMENDMENT_2026_09_18_v1.md`.

* `sep v k i t` — the separation of runner `i` from runner `k`.  Neither is at `0`; both move.
* `InWay`, `LonelyAt` — in the way of the subject, and the subject lonely.
* `lonelyAt_iff_no_inWay`, `lonelyAt_iff_two_sided`, `lonelyAt_iff_neighbours` — loneliness is a
  statement about the subject's **two neighbours** and nothing else.
-/

set_option linter.unusedVariables false

namespace Arrangement

open ConstructionN MomentIterationN

/-- **The separation of runner `i` from runner `k` at time `t`.**  Nothing is placed at `0` and
nothing is held still: this is the gap between two moving runners. -/
def sep (v : Fin 8 → ℝ) (k i : Fin 8) (t : ℝ) : ℝ := v i * t - v k * t

/-- The separation is carried by the speed difference. -/
theorem sep_eq (v : Fin 8 → ℝ) (k i : Fin 8) (t : ℝ) : sep v k i t = (v i - v k) * t := by
  unfold sep; ring

/-- **`i` is in the way of `k` at `t`.** -/
def InWay (v : Fin 8 → ℝ) (k i : Fin 8) (t : ℝ) : Prop := circDist (sep v k i t) < (8 : ℝ)⁻¹

/-- **The subject `k` is lonely at `t`.** -/
def LonelyAt (v : Fin 8 → ℝ) (k : Fin 8) (t : ℝ) : Prop :=
  ∀ i : Fin 8, i ≠ k → (8 : ℝ)⁻¹ ≤ circDist (sep v k i t)

/-- **Lonely is exactly: nobody in the way.** -/
theorem lonelyAt_iff_no_inWay {v : Fin 8 → ℝ} {k : Fin 8} {t : ℝ} :
    LonelyAt v k t ↔ ∀ i : Fin 8, i ≠ k → ¬ InWay v k i t := by
  unfold LonelyAt InWay
  exact ⟨fun h i hi => not_lt.mpr (h i hi), fun h i hi => not_lt.mp (h i hi)⟩

/-- **Loneliness splits into one condition per side of the subject.** -/
theorem lonelyAt_iff_two_sided {v : Fin 8 → ℝ} {k : Fin 8} {t : ℝ} :
    LonelyAt v k t ↔
      (∀ i : Fin 8, i ≠ k → (8 : ℝ)⁻¹ ≤ Int.fract (sep v k i t)) ∧
      (∀ i : Fin 8, i ≠ k → Int.fract (sep v k i t) ≤ 1 - (8 : ℝ)⁻¹) := by
  unfold LonelyAt circDist
  constructor
  · intro h
    refine ⟨fun i hi => le_trans (h i hi) (min_le_left _ _), fun i hi => ?_⟩
    have := le_trans (h i hi) (min_le_right _ _); linarith
  · rintro ⟨h1, h2⟩ i hi
    exact le_min (h1 i hi) (by have := h2 i hi; linarith)

/-- The other seven runners form a nonempty set. -/
theorem others_nonempty (k : Fin 8) : (Finset.univ.erase k).Nonempty := by
  rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ k)]
  simp

/-- **Only the two neighbours matter.**  The subject is lonely exactly when the runner nearest ahead
— least fractional separation — is at least `1/8`, and the one nearest behind is at most `7/8`.  The
other five impose nothing.  This is the sense in which an isolation is affected by three speeds: the
subject's and its two neighbours'. -/
theorem lonelyAt_iff_neighbours {v : Fin 8 → ℝ} {k : Fin 8} {t : ℝ} :
    LonelyAt v k t ↔
      (8 : ℝ)⁻¹ ≤ (Finset.univ.erase k).inf' (others_nonempty k)
          (fun i => Int.fract (sep v k i t)) ∧
      (Finset.univ.erase k).sup' (others_nonempty k)
          (fun i => Int.fract (sep v k i t)) ≤ 1 - (8 : ℝ)⁻¹ := by
  rw [lonelyAt_iff_two_sided, Finset.le_inf'_iff, Finset.sup'_le_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i hi => h1 i (Finset.mem_erase.mp hi).1, fun i hi => h2 i (Finset.mem_erase.mp hi).1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i hi => h1 i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩),
           fun i hi => h2 i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)⟩

/-! ### The disparity of a runner with the subject

The framework's own quantity.  Not a position on a circle: the difference in speed between a runner
and the subject.  Injectivity makes it nonzero, and the separation depends on nothing else. -/

/-- **The disparity of runner `i` with the subject `k`.** -/
def disp (v : Fin 8 → ℝ) (k i : Fin 8) : ℝ := v i - v k

theorem sep_eq_disp_mul (v : Fin 8 → ℝ) (k i : Fin 8) (t : ℝ) :
    sep v k i t = disp v k i * t := by unfold sep disp; ring

/-- No two runners share a speed, so every disparity with the subject is nonzero. -/
theorem disp_ne_zero {v : Fin 8 → ℝ} (hv : Function.Injective v) {k i : Fin 8} (hi : i ≠ k) :
    disp v k i ≠ 0 := sub_ne_zero.mpr fun h => hi (hv h)

/-- **Being in the way is symmetric.**  `i` is in `k`'s way exactly when `k` is in `i`'s.  This is an
arrangement-level fact with no counterpart in a difference set, because it relates two *subjects*. -/
theorem inWay_comm {v : Fin 8 → ℝ} {k i : Fin 8} {t : ℝ} :
    InWay v k i t ↔ InWay v i k t := by
  unfold InWay
  rw [show sep v i k t = -(sep v k i t) by unfold sep; ring, Flanks.circDist_neg]

/-! ### Nothing is pinned and no scale is chosen -/

theorem sep_add_const (v : Fin 8 → ℝ) (c : ℝ) (k i : Fin 8) (t : ℝ) :
    sep (fun j => v j + c) k i t = sep v k i t := by unfold sep; ring

/-- **No runner is held at rest and none sits at the origin.**  Adding a constant to every speed
changes nothing, so the usual normalisation `v k = 0` is a convenience and never a hypothesis. -/
theorem lonelyAt_add_const {v : Fin 8 → ℝ} {c : ℝ} {k : Fin 8} {t : ℝ} :
    LonelyAt (fun j => v j + c) k t ↔ LonelyAt v k t := by
  unfold LonelyAt; simp only [sep_add_const]

theorem sep_const_mul (v : Fin 8 → ℝ) (c : ℝ) (k i : Fin 8) (t : ℝ) :
    sep (fun j => c * v j) k i t = sep v k i (c * t) := by unfold sep; ring

/-- **The scale is carried by the speeds, not chosen.**  Rescaling every speed by `c` rescales the
reading by `c`: there is no free scale anywhere in the statement. -/
theorem lonelyAt_const_mul {v : Fin 8 → ℝ} {c : ℝ} {k : Fin 8} {t : ℝ} :
    LonelyAt (fun j => c * v j) k t ↔ LonelyAt v k (c * t) := by
  unfold LonelyAt; simp only [sep_const_mul]

/-! ### The bridge to the flank machinery

For a **fixed** subject, loneliness factors through the seven disparities in magnitude, so
`LRC/Cascade/Flanks.lean` applies verbatim with no appeal to `ExistenceAt8`.  What a difference set
cannot carry is everything *across* subjects — `inWay_comm`, the gaps, the arrangement itself —
which is why the target is stated on `v` and a set appears only here, as one subject's own data. -/

theorem circDist_abs_mul (x t : ℝ) : circDist (|x| * t) = circDist (x * t) := by
  rcases abs_choice x with h | h
  · rw [h]
  · rw [h, show -x * t = -(x * t) by ring, Flanks.circDist_neg]

open Classical in
/-- **The subject's own difference set**: its seven disparities, in magnitude. -/
noncomputable def diffSet (v : Fin 8 → ℝ) (k : Fin 8) : Finset ℝ :=
  (Finset.univ.erase k).image (fun i => |v i - v k|)

open Classical in
theorem mem_diffSet {v : Fin 8 → ℝ} {k : Fin 8} {d : ℝ} :
    d ∈ diffSet v k ↔ ∃ i : Fin 8, i ≠ k ∧ |v i - v k| = d := by
  unfold diffSet
  simp [Finset.mem_image, Finset.mem_erase]

open Classical in
theorem diffSet_pos {v : Fin 8 → ℝ} (hv : Function.Injective v) (k : Fin 8) :
    ∀ d ∈ diffSet v k, 0 < d := by
  intro d hd
  obtain ⟨i, hi, rfl⟩ := mem_diffSet.mp hd
  exact abs_pos.mpr (sub_ne_zero.mpr fun h => hi (hv h))

open Classical in
theorem diffSet_nonempty (v : Fin 8 → ℝ) (k : Fin 8) : (diffSet v k).Nonempty := by
  obtain ⟨i, hi⟩ := others_nonempty k
  exact ⟨|v i - v k|, mem_diffSet.mpr ⟨i, (Finset.mem_erase.mp hi).1, rfl⟩⟩

open Classical in
/-- **A fixed subject's loneliness is exactly `Lonely` on its own difference set.**  This is the
transfer that makes the flank, opening, residue and cascade results arrangement-level results. -/
theorem lonelyAt_iff_lonely_diffSet {v : Fin 8 → ℝ} {k : Fin 8} {t : ℝ} :
    LonelyAt v k t ↔ Lonely 8 (diffSet v k) t := by
  unfold LonelyAt Lonely
  constructor
  · intro h d hd
    obtain ⟨i, hi, rfl⟩ := mem_diffSet.mp hd
    rw [circDist_abs_mul, ← sep_eq]
    exact h i hi
  · intro h i hi
    have hmem := h _ (mem_diffSet.mpr ⟨i, hi, rfl⟩)
    rwa [circDist_abs_mul, ← sep_eq] at hmem

/-! ### Named instants on an arrangement

The instant is written down, in the arrangement's own terms: a condition on each disparity
`v i − v k`, with no difference set and no existential over sets. -/

/-- **Whole-number speeds with no disparity a multiple of eight: the subject is lonely at `1/8`.** -/
theorem lonelyAt_inv_of_not_dvd {v : Fin 8 → ℝ} {k : Fin 8}
    (h : ∀ i : Fin 8, i ≠ k → ∃ a : ℤ, v i - v k = (a : ℝ) ∧ ¬ ((8 : ℤ) ∣ a)) :
    LonelyAt v k ((8 : ℝ)⁻¹) := by
  intro i hi
  obtain ⟨a, ha, hdvd⟩ := h i hi
  rw [sep_eq, ha]
  have := circDist_int_div (n := 8) (by norm_num) (c := a) (by exact_mod_cast hdvd)
  rw [show (a : ℝ) * (8 : ℝ)⁻¹ = (a : ℝ) / ((8 : ℕ) : ℝ) by push_cast; ring]
  exact this

/-- **So the target holds for that subject**, with the instant exhibited. -/
theorem exists_lonelyAt_of_not_dvd {v : Fin 8 → ℝ} {k : Fin 8}
    (h : ∀ i : Fin 8, i ≠ k → ∃ a : ℤ, v i - v k = (a : ℝ) ∧ ¬ ((8 : ℤ) ∣ a)) :
    ∃ t : ℝ, 0 < t ∧ LonelyAt v k t :=
  ⟨(8 : ℝ)⁻¹, by norm_num, lonelyAt_inv_of_not_dvd h⟩

/-- **The general named instant on an arrangement.**  Choose a whole number `c` and a lap `j`; the
subject is lonely at `(j + 1/8)/c` as soon as every disparity meets one residue condition.  `c` need
not be one of the disparities. -/
theorem lonelyAt_named_instant {v : Fin 8 → ℝ} {k : Fin 8} {c : ℤ} (hc : 0 < c) (j : ℕ)
    (h : ∀ i : Fin 8, i ≠ k → ∃ a : ℤ, v i - v k = (a : ℝ) ∧
      c ≤ a * (8 * (j : ℤ) + 1) % (8 * c) ∧ a * (8 * (j : ℤ) + 1) % (8 * c) ≤ 8 * c - c) :
    LonelyAt v k (Flanks.flankOpening 8 (c : ℝ) j) := by
  intro i hi
  obtain ⟨a, ha, h1, h2⟩ := h i hi
  rw [sep_eq, ha]
  have hkey := (Flanks.clear_at_int_flank_iff_emod (n := 8) hc j).mpr
    (by push_cast; exact ⟨h1, h2⟩)
  simpa using hkey

/-- **And the target for that subject**, again with the instant exhibited. -/
theorem exists_lonelyAt_of_named_instant {v : Fin 8 → ℝ} {k : Fin 8} {c : ℤ} (hc : 0 < c) (j : ℕ)
    (h : ∀ i : Fin 8, i ≠ k → ∃ a : ℤ, v i - v k = (a : ℝ) ∧
      c ≤ a * (8 * (j : ℤ) + 1) % (8 * c) ∧ a * (8 * (j : ℤ) + 1) % (8 * c) ≤ 8 * c - c) :
    ∃ t : ℝ, 0 < t ∧ LonelyAt v k t :=
  ⟨Flanks.flankOpening 8 (c : ℝ) j,
    Flanks.flankOpening_pos (by exact_mod_cast hc) j, lonelyAt_named_instant hc j h⟩


/-! ### The instants are read off the speeds

The framework does not search over instants.  For a given subject the candidate instants are the
openings of that subject's own disparities, and when the speeds are whole numbers the candidates
below one lap are finite in number — `∑ e` of them, not a continuum. -/

open Classical in
/-- **Every lonely instant of a subject is an opening of one of its own disparities**, and
conversely.  The disparities are the speeds' data, so the candidate list is fixed by the arrangement
and never chosen. -/
theorem exists_lonelyAt_iff_flank {v : Fin 8 → ℝ} (hv : Function.Injective v) (k : Fin 8) :
    (∃ t : ℝ, 0 < t ∧ LonelyAt v k t) ↔
      ∃ e ∈ diffSet v k, ∃ j : ℕ, LonelyAt v k (Flanks.flankOpening 8 e j) := by
  have hiff := Flanks.lonely_iff_exists_flank (n := 8) (diffSet_pos hv k) (diffSet_nonempty v k)
  constructor
  · rintro ⟨t, ht, hl⟩
    obtain ⟨e, he, j, hj⟩ := hiff.mp ⟨t, ht, lonelyAt_iff_lonely_diffSet.mp hl⟩
    exact ⟨e, he, j, lonelyAt_iff_lonely_diffSet.mpr hj⟩
  · rintro ⟨e, he, j, hj⟩
    obtain ⟨t, ht, hl⟩ := hiff.mpr ⟨e, he, j, lonelyAt_iff_lonely_diffSet.mp hj⟩
    exact ⟨t, ht, lonelyAt_iff_lonely_diffSet.mpr hl⟩

open Classical in
/-- **Whole-number speeds: the candidate list is finite.**  For each disparity `e` only the openings
`j < e` need be read, because the reading is periodic in `j` with period `e`. -/
theorem exists_lonelyAt_iff_bounded {v : Fin 8 → ℝ} (hv : Function.Injective v) (k : Fin 8)
    (hint : ∀ i : Fin 8, i ≠ k → ∃ a : ℤ, |v i - v k| = (a : ℝ)) :
    (∃ t : ℝ, 0 < t ∧ LonelyAt v k t) ↔
      ∃ e ∈ diffSet v k, ∃ j : ℕ, (j : ℝ) < e ∧ LonelyAt v k (Flanks.flankOpening 8 e j) := by
  have hds : ∀ d ∈ diffSet v k, ∃ a : ℤ, d = (a : ℝ) := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := mem_diffSet.mp hd
    obtain ⟨a, ha⟩ := hint i hi
    exact ⟨a, ha⟩
  have hiff := Flanks.lonely_iff_bounded_search (n := 8) (diffSet_pos hv k)
    (diffSet_nonempty v k) hds
  constructor
  · rintro ⟨t, ht, hl⟩
    obtain ⟨e, he, j, hj, hlj⟩ := hiff.mp ⟨t, ht, lonelyAt_iff_lonely_diffSet.mp hl⟩
    exact ⟨e, he, j, hj, lonelyAt_iff_lonely_diffSet.mpr hlj⟩
  · rintro ⟨e, he, j, hj, hlj⟩
    obtain ⟨t, ht, hl⟩ := hiff.mpr ⟨e, he, j, hj, lonelyAt_iff_lonely_diffSet.mp hlj⟩
    exact ⟨t, ht, lonelyAt_iff_lonely_diffSet.mpr hl⟩


/-! ### The subject's two gaps

`lonelyAt_iff_neighbours` says only the two neighbours bind.  Named as gaps, that reads: the subject
is lonely exactly when the gap **ahead** of it and the gap **behind** it each reach `1/8`.

This is the eight-runner picture, not a seven-runner one.  At an instant the eight runners cut the
circle into **eight** gaps summing to `1` — there is a gap between the last runner and the first,
because the circle closes.  The subject owns two of those eight, and `gapAhead_add_gapBehind_le_one`
is the part of that identity the obligation actually uses: the subject's own two gaps are part of a
whole of `1`.  So the demand is `1/8 + 1/8 = 1/4` of the circle, sitting in the subject's two gaps,
out of the `1` available across all eight.  Equality throughout is the arithmetic progression.

Verified against `LonelyAt` on 30,267 random instants, zero disagreements
(`experiments/n8/gap_frame_check_v1`). -/

/-- **The gap ahead of the subject**: the least fractional separation, i.e. the nearest runner in
front. -/
noncomputable def gapAhead (v : Fin 8 → ℝ) (k : Fin 8) (t : ℝ) : ℝ :=
  (Finset.univ.erase k).inf' (others_nonempty k) (fun i => Int.fract (sep v k i t))

/-- **The gap behind the subject**: what is left after the greatest fractional separation, i.e. the
nearest runner behind. -/
noncomputable def gapBehind (v : Fin 8 → ℝ) (k : Fin 8) (t : ℝ) : ℝ :=
  1 - (Finset.univ.erase k).sup' (others_nonempty k) (fun i => Int.fract (sep v k i t))

/-- **Lonely is: both of the subject's gaps reach `1/8`.** -/
theorem lonelyAt_iff_gaps {v : Fin 8 → ℝ} {k : Fin 8} {t : ℝ} :
    LonelyAt v k t ↔ (8 : ℝ)⁻¹ ≤ gapAhead v k t ∧ (8 : ℝ)⁻¹ ≤ gapBehind v k t := by
  rw [lonelyAt_iff_neighbours]
  unfold gapAhead gapBehind
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩

/-- **The subject's two gaps are part of a whole of `1`.**  The other six gaps of the eight hold the
rest, so the obligation asks for `1/4` of the circle out of `1` — not for more circle than exists. -/
theorem gapAhead_add_gapBehind_le_one (v : Fin 8 → ℝ) (k : Fin 8) (t : ℝ) :
    gapAhead v k t + gapBehind v k t ≤ 1 := by
  unfold gapAhead gapBehind
  obtain ⟨i, hi⟩ := others_nonempty k
  have h : (Finset.univ.erase k).inf' (others_nonempty k) (fun i => Int.fract (sep v k i t))
      ≤ (Finset.univ.erase k).sup' (others_nonempty k) (fun i => Int.fract (sep v k i t)) :=
    le_trans (Finset.inf'_le (fun i => Int.fract (sep v k i t)) hi)
      (Finset.le_sup' (fun i => Int.fract (sep v k i t)) hi)
  linarith

/-- **Both gaps are nonnegative**, so `1/4` is a demand on a circle of `1` and nothing is being asked
twice. -/
theorem gapAhead_nonneg (v : Fin 8 → ℝ) (k : Fin 8) (t : ℝ) : 0 ≤ gapAhead v k t := by
  unfold gapAhead
  exact Finset.le_inf' _ _ (fun i _ => Int.fract_nonneg _)

theorem gapBehind_nonneg (v : Fin 8 → ℝ) (k : Fin 8) (t : ℝ) : 0 ≤ gapBehind v k t := by
  unfold gapBehind
  have : (Finset.univ.erase k).sup' (others_nonempty k) (fun i => Int.fract (sep v k i t)) ≤ 1 :=
    Finset.sup'_le _ _ (fun i _ => le_of_lt (Int.fract_lt_one _))
  linarith


end Arrangement
