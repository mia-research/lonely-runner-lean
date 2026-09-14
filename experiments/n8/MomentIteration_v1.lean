import LonelyRunner.LRC.ConstructionN.Band

/-!
# The moment iteration (COMPLETE_PREDICTOR_v1 §1) over the reals

Experiment, outside both Lean trees.  For a subject with (positive) speed differences `ds`:

* `inWay d t`        — the runner at difference `d` is within `1/8` of the subject at `t`;
* `nextOpening d t`  — the least `(k + 1/8)/d` at or after `t`;
* `move ds t`        — the largest `nextOpening` over the runners in the way at `t` (or `t` if none).

Proved here:
* `inWay_until_opening` — a runner in the way at `t` stays in the way on `[t, nextOpening d t)`;
* `move_le_of_lonely`   — no move overshoots a lonely time;
* `lonely_of_fixed`     — a fixed point of `move` is a lonely time;
* `iterate_le_of_lonely`— every iterate from the start is a lower bound for every later lonely time;
* `first_isolation_of_fixed` — if an iterate from the bound `1/(8·d_min)` is fixed, it is lonely and no
  positive lonely time precedes it: it is the first isolation time.

**Not stated:** that some iterate is fixed.  That is the framework's open statement for this runner.
-/

namespace MomentIteration

open ConstructionN

noncomputable def inWay (d t : ℝ) : Prop := circDist (d * t) < (8 : ℝ)⁻¹

noncomputable def nextOpening (d t : ℝ) : ℝ := ((⌈d * t - (8 : ℝ)⁻¹⌉ : ℝ) + (8 : ℝ)⁻¹) / d

def Lonely (ds : Finset ℝ) (s : ℝ) : Prop := ∀ d ∈ ds, (8 : ℝ)⁻¹ ≤ circDist (d * s)

open Classical in
noncomputable def move (ds : Finset ℝ) (t : ℝ) : ℝ :=
  ds.fold max t (fun d => if inWay d t then nextOpening d t else t)

/-- In the way at `t` means within `1/8` of an integer `k`; then `nextOpening` is `(k + 1/8)/d`. -/
theorem nextOpening_eq {d t : ℝ} (_hd : 0 < d) {k : ℤ} (hk : |d * t - k| < (8 : ℝ)⁻¹) :
    nextOpening d t = ((k : ℝ) + (8 : ℝ)⁻¹) / d := by
  unfold nextOpening
  have hc : ⌈d * t - (8 : ℝ)⁻¹⌉ = k := by
    rw [Int.ceil_eq_iff]
    have := abs_lt.mp hk
    constructor <;> linarith
  rw [hc]

theorem exists_near_int {d t : ℝ} (h : inWay d t) : ∃ k : ℤ, |d * t - k| < (8 : ℝ)⁻¹ := by
  obtain ⟨k, hk⟩ := circDist_eq_abs_sub_some_int (d * t)
  exact ⟨k, by unfold inWay at h; rwa [hk] at h⟩

/-- A runner in the way at `t` stays in the way until its next opening. -/
theorem inWay_until_opening {d t s : ℝ} (hd : 0 < d) (h : inWay d t) (hts : t ≤ s)
    (hs : s < nextOpening d t) : inWay d s := by
  obtain ⟨k, hk⟩ := exists_near_int h
  rw [nextOpening_eq hd hk, lt_div_iff₀ hd] at hs
  have h1 := abs_lt.mp hk
  have hds : d * t ≤ d * s := mul_le_mul_of_nonneg_left hts hd.le
  unfold inWay
  refine lt_of_le_of_lt (circDist_le_abs_sub_int (d * s) k) ?_
  rw [abs_lt]; constructor <;> nlinarith

/-- The next opening is strictly later than `t`. -/
theorem lt_nextOpening {d t : ℝ} (hd : 0 < d) (h : inWay d t) : t < nextOpening d t := by
  obtain ⟨k, hk⟩ := exists_near_int h
  rw [nextOpening_eq hd hk, lt_div_iff₀ hd]
  have := abs_lt.mp hk
  nlinarith

/-- Lonely at `s ≥ t` forces `s` past the next opening of every runner in the way at `t`. -/
theorem nextOpening_le_of_lonely {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {t s : ℝ}
    (hl : Lonely ds s) (hts : t ≤ s) {d : ℝ} (hd : d ∈ ds) (hw : inWay d t) :
    nextOpening d t ≤ s := by
  by_contra hc
  push Not at hc
  have := inWay_until_opening (hpos d hd) hw hts hc
  exact absurd (hl d hd) (not_le.mpr this)

/-- **No move overshoots a lonely time.** -/
theorem move_le_of_lonely {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {t s : ℝ}
    (hl : Lonely ds s) (hts : t ≤ s) : move ds t ≤ s := by
  classical
  unfold move
  rw [Finset.fold_max_le]
  refine ⟨hts, fun d hd => ?_⟩
  split_ifs with hw
  · exact nextOpening_le_of_lonely hpos hl hts hd hw
  · exact hts

theorem le_move (ds : Finset ℝ) (t : ℝ) : t ≤ move ds t := by
  classical
  unfold move
  rw [Finset.le_fold_max]
  exact Or.inl le_rfl

/-- **A fixed point of the move is a lonely time.** -/
theorem lonely_of_fixed {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {t : ℝ} (hfix : move ds t = t) :
    Lonely ds t := by
  classical
  intro d hd
  by_contra hc
  push Not at hc
  have hw : inWay d t := hc
  have hlt := lt_nextOpening (hpos d hd) hw
  have hle : nextOpening d t ≤ move ds t := by
    unfold move
    rw [Finset.le_fold_max]
    exact Or.inr ⟨d, hd, by rw [if_pos hw]⟩
  linarith

/-- **Every iterate is a lower bound for every lonely time after the start.** -/
theorem iterate_le_of_lonely {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {b s : ℝ}
    (hl : Lonely ds s) (hbs : b ≤ s) : ∀ N : ℕ, (move ds)^[N] b ≤ s := by
  intro N
  induction N with
  | zero => simpa using hbs
  | succ N ih =>
    rw [Function.iterate_succ_apply']
    exact move_le_of_lonely hpos hl ih

/-- Nothing positive precedes the bound `1/(8·m)` when `m ∈ ds` is the nearest difference. -/
theorem bound_le_of_lonely {ds : Finset ℝ} {m s : ℝ} (hm : m ∈ ds) (hmpos : 0 < m)
    (hl : Lonely ds s) (hs : 0 < s) : 1 / (8 * m) ≤ s := by
  by_contra hc
  push Not at hc
  have := ConstructionN.before_floor (n := 8) (by norm_num) hmpos hs (by exact_mod_cast hc)
  have h8 := hl m hm
  norm_num at this h8
  linarith

/-- **The first isolation time.**  If some iterate of the move from the bound is fixed, it is a lonely
time, and every positive lonely time is at or after it. -/
theorem first_isolation_of_fixed {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : m ∈ ds)
    (N : ℕ) (hfix : move ds ((move ds)^[N] (1 / (8 * m))) = (move ds)^[N] (1 / (8 * m))) :
    Lonely ds ((move ds)^[N] (1 / (8 * m))) ∧
      ∀ s, 0 < s → Lonely ds s → (move ds)^[N] (1 / (8 * m)) ≤ s := by
  refine ⟨lonely_of_fixed hpos hfix, fun s hs hl => ?_⟩
  exact iterate_le_of_lonely hpos hl (bound_le_of_lonely hm (hpos m hm) hl hs) N

end MomentIteration

#print axioms MomentIteration.inWay_until_opening
#print axioms MomentIteration.move_le_of_lonely
#print axioms MomentIteration.lonely_of_fixed
#print axioms MomentIteration.iterate_le_of_lonely
#print axioms MomentIteration.first_isolation_of_fixed
