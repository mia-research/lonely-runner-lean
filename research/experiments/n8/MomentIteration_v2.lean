import LonelyRunner.LRC.ConstructionN.Band

/-!
# The moment iteration (COMPLETE_PREDICTOR_v1 §1) over the reals — v2, with the flank lemma

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

end MomentIteration

#print axioms MomentIteration.inWay_until_opening
#print axioms MomentIteration.move_le_of_lonely
#print axioms MomentIteration.lonely_of_fixed
#print axioms MomentIteration.iterate_le_of_lonely
#print axioms MomentIteration.first_isolation_of_fixed
#print axioms MomentIteration.iterate_has_threshold_runner
#print axioms MomentIteration.flank_of_threshold
#print axioms MomentIteration.flank_at_first_isolation
