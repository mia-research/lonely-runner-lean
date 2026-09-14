import LonelyRunner.LRC.ConstructionN.Band

/-!
# The moment iteration (COMPLETE_PREDICTOR_v1 §1) over the reals — v4, with the flank lemma, the scale bridge, and the zone run

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

/-! ## v2 — the flank at the first isolation time

The moment is always a neighbour arriving at exactly one eighth.  Positions are signed: runner `j`
sits at `fract (w j * t)` relative to the subject, where `w j = v_j - v_i` and the subject's
differences are `ds = |w j|`. -/

theorem circDist_one_eighth : circDist ((8 : ℝ)⁻¹) = (8 : ℝ)⁻¹ := by
  unfold circDist
  have h : Int.fract ((8 : ℝ)⁻¹) = (8 : ℝ)⁻¹ := by
    rw [Int.fract_eq_self]; constructor <;> norm_num
  rw [h]; norm_num

/-- At its next opening, a runner is at exactly one eighth. -/
theorem circDist_at_nextOpening {d t : ℝ} (hd : 0 < d) :
    circDist (d * nextOpening d t) = (8 : ℝ)⁻¹ := by
  unfold nextOpening
  have e : d * (((⌈d * t - (8 : ℝ)⁻¹⌉ : ℝ) + (8 : ℝ)⁻¹) / d)
      = (8 : ℝ)⁻¹ + ((⌈d * t - (8 : ℝ)⁻¹⌉ : ℤ) : ℝ) := by field_simp; ring
  rw [e, ConstructionN.circDist_add_int, circDist_one_eighth]

/-- The move lands either where it started or on the next opening of a runner in the way. -/
theorem move_eq_self_or_opening (ds : Finset ℝ) (t : ℝ) :
    move ds t = t ∨ ∃ d ∈ ds, inWay d t ∧ move ds t = nextOpening d t := by
  classical
  unfold move
  induction ds using Finset.induction_on with
  | empty => left; simp
  | insert a s ha ih =>
    rw [Finset.fold_insert ha]
    rcases le_total (if inWay a t then nextOpening a t else t) (s.fold max t (fun d => if inWay d t then nextOpening d t else t)) with h | h
    · rw [max_eq_right h]
      rcases ih with h1 | ⟨d, hd, hw, he⟩
      · exact Or.inl h1
      · exact Or.inr ⟨d, Finset.mem_insert_of_mem hd, hw, he⟩
    · rw [max_eq_left h]
      by_cases hw : inWay a t
      · exact Or.inr ⟨a, Finset.mem_insert_self a s, hw, by rw [if_pos hw]⟩
      · left; rw [if_neg hw]

/-- **Every iterate from the bound has a runner at exactly one eighth.** -/
theorem iterate_has_threshold_runner {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ}
    (hm : m ∈ ds) : ∀ N : ℕ, ∃ d ∈ ds, circDist (d * (move ds)^[N] (1 / (8 * m))) = (8 : ℝ)⁻¹ := by
  intro N
  induction N with
  | zero =>
    refine ⟨m, hm, ?_⟩
    have hm0 := hpos m hm
    have e : m * (1 / (8 * m)) = (8 : ℝ)⁻¹ := by field_simp
    show circDist (m * (1 / (8 * m))) = (8 : ℝ)⁻¹
    rw [e]; exact circDist_one_eighth
  | succ N ih =>
    rw [Function.iterate_succ_apply']
    rcases move_eq_self_or_opening ds ((move ds)^[N] (1 / (8 * m))) with h | ⟨d, hd, _, he⟩
    · rw [h]; exact ih
    · exact ⟨d, hd, by rw [he]; exact circDist_at_nextOpening (hpos d hd)⟩

/-- **A runner at exactly one eighth from a lonely subject is a flank**: the nearest runner ahead
(position `1/8`) or the nearest behind (position `7/8`). -/
theorem flank_of_threshold {ι : Type*} (y : ι → ℝ) (hl : ∀ l, (8 : ℝ)⁻¹ ≤ circDist (y l))
    {j : ι} (hj : circDist (y j) = (8 : ℝ)⁻¹) :
    (Int.fract (y j) = (8 : ℝ)⁻¹ ∧ ∀ l, Int.fract (y j) ≤ Int.fract (y l)) ∨
    (Int.fract (y j) = 1 - (8 : ℝ)⁻¹ ∧ ∀ l, Int.fract (y l) ≤ Int.fract (y j)) := by
  have hmin : ∀ l, (8 : ℝ)⁻¹ ≤ Int.fract (y l) ∧ Int.fract (y l) ≤ 1 - (8 : ℝ)⁻¹ := by
    intro l; have := hl l; unfold circDist at this
    rw [le_min_iff] at this; exact ⟨this.1, by linarith [this.2]⟩
  unfold circDist at hj
  rcases min_choice (Int.fract (y j)) (1 - Int.fract (y j)) with h | h
  · rw [h] at hj; exact Or.inl ⟨hj, fun l => by rw [hj]; exact (hmin l).1⟩
  · rw [h] at hj
    have hf : Int.fract (y j) = 1 - (8 : ℝ)⁻¹ := by linarith
    exact Or.inr ⟨hf, fun l => by rw [hf]; exact (hmin l).2⟩

/-- **The flank at the first isolation time.**  Subject's signed differences `w` (all nonzero),
`ds = |w|`, nearest difference `m`.  If an iterate `T` of the move from the bound is fixed, then the
subject is lonely at `T`, no positive lonely time precedes `T`, and some runner `j` sits at exactly
one eighth as the nearest runner ahead or the nearest behind. -/
theorem flank_at_first_isolation {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℝ)
    (hw : ∀ j, w j ≠ 0) {m : ℝ} (hm : m ∈ Finset.univ.image (fun j => |w j|)) (N : ℕ)
    (hfix : move (Finset.univ.image (fun j => |w j|)) ((move (Finset.univ.image (fun j => |w j|)))^[N] (1 / (8 * m)))
        = (move (Finset.univ.image (fun j => |w j|)))^[N] (1 / (8 * m))) :
    let ds := Finset.univ.image (fun j => |w j|)
    let T := (move ds)^[N] (1 / (8 * m))
    (∀ j, (8 : ℝ)⁻¹ ≤ circDist (w j * T)) ∧
      (∀ s, 0 < s → (∀ j, (8 : ℝ)⁻¹ ≤ circDist (w j * s)) → T ≤ s) ∧
      ∃ j, circDist (w j * T) = (8 : ℝ)⁻¹ ∧
        ((Int.fract (w j * T) = (8 : ℝ)⁻¹ ∧ ∀ l, Int.fract (w j * T) ≤ Int.fract (w l * T)) ∨
         (Int.fract (w j * T) = 1 - (8 : ℝ)⁻¹ ∧ ∀ l, Int.fract (w l * T) ≤ Int.fract (w j * T))) := by
  intro ds T
  have hpos : ∀ d ∈ ds, 0 < d := by
    intro d hd; obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hd; exact abs_pos.mpr (hw j)
  have habs : ∀ j x, circDist (w j * x) = circDist (|w j| * x) := by
    intro j x; rcases abs_cases (w j) with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
    · rw [h, neg_mul, circDist.symm_neg]
  have lonely_iff : ∀ x, Lonely ds x ↔ ∀ j, (8 : ℝ)⁻¹ ≤ circDist (w j * x) := by
    intro x; constructor
    · intro h j; rw [habs]; exact h _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    · intro h d hd; obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hd; rw [← habs]; exact h j
  obtain ⟨hl, hleast⟩ := first_isolation_of_fixed hpos hm N hfix
  refine ⟨(lonely_iff T).mp hl, fun s hs h => hleast s hs ((lonely_iff s).mpr h), ?_⟩
  obtain ⟨d, hd, hdt⟩ := iterate_has_threshold_runner hpos hm N
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hd
  have hj : circDist (w j * T) = (8 : ℝ)⁻¹ := by rw [habs]; exact hdt
  exact ⟨j, hj, flank_of_threshold (fun l => w l * T) ((lonely_iff T).mp hl) hj⟩

/-! ## v3 — the move as a change of AP scale

At the instant `t = 1/(8D)` (the first spine point of the AP of gap `D`), runner `d` reads `s = d/D`.  It is in the
way exactly when `s` is within 1 of a multiple of 8, and its next opening is the first spine point of the AP of gap
`d/(8N+1)`. -/

theorem mul_inv_scale {d D : ℝ} (hD : 0 < D) : d * (1 / (8 * D)) = (d / D) / 8 := by
  field_simp

/-- **In the way at scale `D` iff the reading is within 1 of a multiple of 8.** -/
theorem inWay_at_scale_iff {d D : ℝ} (hD : 0 < D) :
    inWay d (1 / (8 * D)) ↔ ∃ N : ℤ, |d / D - 8 * N| < 1 := by
  unfold inWay
  rw [mul_inv_scale hD]
  have h := ConstructionN.band_identity 8 (by norm_num) (d / D)
  push_cast at h
  constructor
  · intro hlt
    by_contra hc
    push Not at hc
    exact absurd (h.mpr hc) (not_le.mpr hlt)
  · rintro ⟨N, hN⟩
    by_contra hc
    push Not at hc
    exact absurd (h.mp hc N) (not_le.mpr hN)

/-- **The next opening of a runner in the way at scale `D` is the spine point of scale `d/(8N+1)`.** -/
theorem nextOpening_at_scale {d D : ℝ} (hd : 0 < d) (hD : 0 < D) {N : ℤ} (hN : |d / D - 8 * N| < 1) :
    nextOpening d (1 / (8 * D)) = 1 / (8 * (d / (8 * N + 1))) := by
  have hk : |d * (1 / (8 * D)) - N| < (8 : ℝ)⁻¹ := by
    rw [mul_inv_scale hD]
    have e : d / D / 8 - (N : ℝ) = (d / D - 8 * N) / 8 := by ring
    rw [e, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
    have : |d / D - 8 * ↑N| / 8 < 1 / 8 := by linarith
    simpa using this
  have hN0 : (0 : ℝ) < 8 * N + 1 := by
    have hs : 0 < d / D := div_pos hd hD
    have := abs_lt.mp hN
    linarith
  rw [nextOpening_eq hd hk]
  field_simp

/-! ## v4 — the first isolation time as the end of the run of lap-completion zones

Runner `d` completes relative lap `N` at `N/d` and is in the way on the open zone `((N − 1/8)/d, (N + 1/8)/d)`.
A **run** from `b` is a list of such zones, each containing the end of the one before, starting with a zone that
contains `b`; its end is the right end of the last zone.  The first isolation time is the end of the run from the bound
that finishes at a lonely time — a statement about the lap-completion zones, with no iteration in it. -/

noncomputable def zoneLo (d : ℝ) (N : ℤ) : ℝ := ((N : ℝ) - (8 : ℝ)⁻¹) / d
noncomputable def zoneHi (d : ℝ) (N : ℤ) : ℝ := ((N : ℝ) + (8 : ℝ)⁻¹) / d

/-- **In the way iff inside one of the runner's lap zones.** -/
theorem inWay_iff_zone {d t : ℝ} (hd : 0 < d) :
    inWay d t ↔ ∃ N : ℤ, zoneLo d N < t ∧ t < zoneHi d N := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := exists_near_int h
    have := abs_lt.mp hk
    refine ⟨k, ?_, ?_⟩
    · unfold zoneLo; rw [div_lt_iff₀ hd]; nlinarith
    · unfold zoneHi; rw [lt_div_iff₀ hd]; nlinarith
  · rintro ⟨N, h1, h2⟩
    unfold zoneLo at h1; unfold zoneHi at h2
    rw [div_lt_iff₀ hd] at h1; rw [lt_div_iff₀ hd] at h2
    unfold inWay
    refine lt_of_le_of_lt (circDist_le_abs_sub_int (d * t) N) ?_
    rw [abs_lt]; constructor <;> nlinarith

/-- A run of lap zones from `b`, ending at `T`. -/
def Run (ds : Finset ℝ) : ℝ → List (ℝ × ℤ) → ℝ → Prop
  | b, [], T => T = b
  | b, (d, N) :: L, T => d ∈ ds ∧ zoneLo d N < b ∧ b < zoneHi d N ∧ Run ds (zoneHi d N) L T

/-- A run covers everything from its start up to its end: every such time is inside some runner's zone. -/
theorem Run.covers {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) :
    ∀ (L : List (ℝ × ℤ)) (b T : ℝ), Run ds b L T →
      b ≤ T ∧ ∀ t, b ≤ t → t < T → ∃ d ∈ ds, inWay d t := by
  intro L
  induction L with
  | nil =>
    intro b T h
    simp only [Run] at h
    subst h
    exact ⟨le_rfl, fun t h1 h2 => absurd h2 (not_lt.mpr h1)⟩
  | cons p L ih =>
    obtain ⟨d, N⟩ := p
    intro b T h
    obtain ⟨hd, hlo, hhi, hr⟩ := h
    obtain ⟨hT, hcov⟩ := ih _ _ hr
    refine ⟨le_trans hhi.le hT, fun t h1 h2 => ?_⟩
    by_cases ht : t < zoneHi d N
    · exact ⟨d, hd, (inWay_iff_zone (hpos d hd)).mpr ⟨N, lt_of_lt_of_le hlo h1, ht⟩⟩
    · exact hcov t (not_lt.mp ht) h2

/-- Extending a run by a zone that contains its end. -/
theorem Run.snoc {ds : Finset ℝ} {d : ℝ} {N : ℤ} (hd : d ∈ ds) :
    ∀ (L : List (ℝ × ℤ)) (b T : ℝ), Run ds b L T → zoneLo d N < T → T < zoneHi d N →
      Run ds b (L ++ [(d, N)]) (zoneHi d N) := by
  intro L
  induction L with
  | nil =>
    intro b T h h1 h2
    simp only [Run] at h
    subst h
    exact ⟨hd, h1, h2, rfl⟩
  | cons p L ih =>
    obtain ⟨d', N'⟩ := p
    intro b T h h1 h2
    obtain ⟨hd', hlo, hhi, hr⟩ := h
    exact ⟨hd', hlo, hhi, ih _ _ hr h1 h2⟩

/-- **The end of a run from the bound that finishes at a lonely time is the first isolation time** — proved from the
zones alone. -/
theorem first_isolation_of_run {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : m ∈ ds)
    {L : List (ℝ × ℤ)} {T : ℝ} (hr : Run ds (1 / (8 * m)) L T) (hT : Lonely ds T) :
    ∀ s, 0 < s → Lonely ds s → T ≤ s := by
  intro s hs hl
  by_contra hc
  push Not at hc
  obtain ⟨-, hcov⟩ := Run.covers hpos L _ _ hr
  obtain ⟨d, hd, hw⟩ := hcov s (bound_le_of_lonely hm (hpos m hm) hl hs) hc
  exact absurd (hl d hd) (not_le.mpr hw)

theorem iterate_ge (ds : Finset ℝ) (b : ℝ) : ∀ N : ℕ, b ≤ (move ds)^[N] b := by
  intro N
  induction N with
  | zero => simp
  | succ N ih => rw [Function.iterate_succ_apply']; exact le_trans ih (le_move ds _)

/-- **Every iterate of the move is the end of a run of zones from the start**: each move adds its setter's zone. -/
theorem run_of_iterate {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (b : ℝ) :
    ∀ N : ℕ, ∃ L, Run ds b L ((move ds)^[N] b) := by
  intro N
  induction N with
  | zero => exact ⟨[], by simp [Run]⟩
  | succ N ih =>
    obtain ⟨L, hL⟩ := ih
    rw [Function.iterate_succ_apply']
    rcases move_eq_self_or_opening ds ((move ds)^[N] b) with h | ⟨d, hd, hw, he⟩
    · exact ⟨L, by rw [h]; exact hL⟩
    · obtain ⟨k, hk⟩ := exists_near_int hw
      have hdpos := hpos d hd
      have hlo : zoneLo d k < (move ds)^[N] b := by
        have := abs_lt.mp hk; unfold zoneLo; rw [div_lt_iff₀ hdpos]; nlinarith
      have hhi : (move ds)^[N] b < zoneHi d k := by
        have := abs_lt.mp hk; unfold zoneHi; rw [lt_div_iff₀ hdpos]; nlinarith
      have hmv : move ds ((move ds)^[N] b) = zoneHi d k := by
        rw [he, nextOpening_eq hdpos hk]; rfl
      exact ⟨L ++ [(d, k)], by rw [hmv]; exact Run.snoc hd L _ _ hL hlo hhi⟩

/-- **A run from the bound ending at a lonely time ends at the fixed point of the iteration.** -/
theorem run_end_eq_fixed_point {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : m ∈ ds) (N : ℕ)
    (hfix : move ds ((move ds)^[N] (1 / (8 * m))) = (move ds)^[N] (1 / (8 * m)))
    {L : List (ℝ × ℤ)} {T : ℝ} (hr : Run ds (1 / (8 * m)) L T) (hT : Lonely ds T) :
    T = (move ds)^[N] (1 / (8 * m)) := by
  have hb : 0 < 1 / (8 * m) := by have := hpos m hm; positivity
  obtain ⟨hFl, hFleast⟩ := first_isolation_of_fixed hpos hm N hfix
  have hbT := (Run.covers hpos L _ _ hr).1
  have hFT : (move ds)^[N] (1 / (8 * m)) ≤ T := hFleast T (lt_of_lt_of_le hb hbT) hT
  have hTF : T ≤ (move ds)^[N] (1 / (8 * m)) :=
    first_isolation_of_run hpos hm hr hT _ (lt_of_lt_of_le hb (iterate_ge ds _ N)) hFl
  exact le_antisymm hTF hFT

/-- **The first isolation time as the end of the zone run.**  If the iteration from the bound reaches a fixed point
`F`, then `F` is the end of a run of lap-completion zones from the bound, the subject is lonely at `F`, no positive
lonely time precedes it, and every run from the bound that ends at a lonely time ends at `F`. -/
theorem first_isolation_as_zone_run {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : m ∈ ds) (N : ℕ)
    (hfix : move ds ((move ds)^[N] (1 / (8 * m))) = (move ds)^[N] (1 / (8 * m))) :
    (∃ L, Run ds (1 / (8 * m)) L ((move ds)^[N] (1 / (8 * m)))) ∧
      Lonely ds ((move ds)^[N] (1 / (8 * m))) ∧
      (∀ s, 0 < s → Lonely ds s → (move ds)^[N] (1 / (8 * m)) ≤ s) ∧
      (∀ L T, Run ds (1 / (8 * m)) L T → Lonely ds T → T = (move ds)^[N] (1 / (8 * m))) := by
  obtain ⟨hl, hleast⟩ := first_isolation_of_fixed hpos hm N hfix
  exact ⟨run_of_iterate hpos _ N, hl, hleast, fun L T hr hT => run_end_eq_fixed_point hpos hm N hfix hr hT⟩

end MomentIteration

#print axioms MomentIteration.inWay_until_opening
#print axioms MomentIteration.move_le_of_lonely
#print axioms MomentIteration.lonely_of_fixed
#print axioms MomentIteration.iterate_le_of_lonely
#print axioms MomentIteration.first_isolation_of_fixed
#print axioms MomentIteration.iterate_has_threshold_runner
#print axioms MomentIteration.flank_of_threshold
#print axioms MomentIteration.flank_at_first_isolation
#print axioms MomentIteration.inWay_at_scale_iff
#print axioms MomentIteration.nextOpening_at_scale
#print axioms MomentIteration.inWay_iff_zone
#print axioms MomentIteration.first_isolation_of_run
#print axioms MomentIteration.run_of_iterate
#print axioms MomentIteration.run_end_eq_fixed_point
#print axioms MomentIteration.first_isolation_as_zone_run
