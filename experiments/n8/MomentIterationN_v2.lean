import LonelyRunner.LRC.ConstructionN.Band

/-!
# The moment iteration (COMPLETE_PREDICTOR_v1 §1) over the reals — v6, with the flank lemma, the scale bridge, the zone run, finiteness, drift lines and slot-sharers

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

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace MomentIterationN

open ConstructionN

variable {n : ℕ} [Fact (2 ≤ n)]

theorem n_pos : (0 : ℝ) < n := by
  have := (Fact.out : 2 ≤ n); exact_mod_cast (by omega : 0 < n)

theorem two_le_n : (2 : ℝ) ≤ n := by exact_mod_cast (Fact.out : 2 ≤ n)

theorem inv_le_half : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) two_le_n

noncomputable def inWay (n : ℕ) (d t : ℝ) : Prop := circDist (d * t) < (n : ℝ)⁻¹

noncomputable def nextOpening (n : ℕ) (d t : ℝ) : ℝ := ((⌈d * t - (n : ℝ)⁻¹⌉ : ℝ) + (n : ℝ)⁻¹) / d

def Lonely (n : ℕ) (ds : Finset ℝ) (s : ℝ) : Prop := ∀ d ∈ ds, (n : ℝ)⁻¹ ≤ circDist (d * s)

open Classical in
noncomputable def move (n : ℕ) (ds : Finset ℝ) (t : ℝ) : ℝ :=
  ds.fold max t (fun d => if inWay n d t then nextOpening n d t else t)

/-- In the way at `t` means within `1/8` of an integer `k`; then `nextOpening` is `(k + 1/8)/d`. -/
theorem nextOpening_eq {d t : ℝ} (_hd : 0 < d) {k : ℤ} (hk : |d * t - k| < (n : ℝ)⁻¹) :
    nextOpening n d t = ((k : ℝ) + (n : ℝ)⁻¹) / d := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  unfold nextOpening
  have hc : ⌈d * t - (n : ℝ)⁻¹⌉ = k := by
    rw [Int.ceil_eq_iff]
    have := abs_lt.mp hk
    constructor <;> linarith
  rw [hc]

theorem exists_near_int {d t : ℝ} (h : inWay n d t) : ∃ k : ℤ, |d * t - k| < (n : ℝ)⁻¹ := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  obtain ⟨k, hk⟩ := circDist_eq_abs_sub_some_int (d * t)
  exact ⟨k, by unfold inWay at h; rwa [hk] at h⟩

/-- A runner in the way at `t` stays in the way until its next opening. -/
theorem inWay_until_opening {d t s : ℝ} (hd : 0 < d) (h : inWay n d t) (hts : t ≤ s)
    (hs : s < nextOpening n d t) : inWay n d s := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  obtain ⟨k, hk⟩ := exists_near_int h
  rw [nextOpening_eq hd hk, lt_div_iff₀ hd] at hs
  have h1 := abs_lt.mp hk
  have hds : d * t ≤ d * s := mul_le_mul_of_nonneg_left hts hd.le
  unfold inWay
  refine lt_of_le_of_lt (circDist_le_abs_sub_int (d * s) k) ?_
  rw [abs_lt]; constructor <;> nlinarith

/-- The next opening is strictly later than `t`. -/
theorem lt_nextOpening {d t : ℝ} (hd : 0 < d) (h : inWay n d t) : t < nextOpening n d t := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  obtain ⟨k, hk⟩ := exists_near_int h
  rw [nextOpening_eq hd hk, lt_div_iff₀ hd]
  have := abs_lt.mp hk
  nlinarith

/-- Lonely at `s ≥ t` forces `s` past the next opening of every runner in the way at `t`. -/
theorem nextOpening_le_of_lonely {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {t s : ℝ}
    (hl : Lonely n ds s) (hts : t ≤ s) {d : ℝ} (hd : d ∈ ds) (hw : inWay n d t) :
    nextOpening n d t ≤ s := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  by_contra hc
  push Not at hc
  have := inWay_until_opening (hpos d hd) hw hts hc
  exact absurd (hl d hd) (not_le.mpr this)

/-- **No move overshoots a lonely time.** -/
theorem move_le_of_lonely {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {t s : ℝ}
    (hl : Lonely n ds s) (hts : t ≤ s) : move n ds t ≤ s := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  classical
  unfold move
  rw [Finset.fold_max_le]
  refine ⟨hts, fun d hd => ?_⟩
  split_ifs with hw
  · exact nextOpening_le_of_lonely hpos hl hts hd hw
  · exact hts

theorem le_move (ds : Finset ℝ) (t : ℝ) : t ≤ move n ds t := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  classical
  unfold move
  rw [Finset.le_fold_max]
  exact Or.inl le_rfl

/-- **A fixed point of the move is a lonely time.** -/
theorem lonely_of_fixed {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {t : ℝ} (hfix : move n ds t = t) :
    Lonely n ds t := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  classical
  intro d hd
  by_contra hc
  push Not at hc
  have hw : inWay n d t := hc
  have hlt := lt_nextOpening (hpos d hd) hw
  have hle : nextOpening n d t ≤ move n ds t := by
    unfold move
    rw [Finset.le_fold_max]
    exact Or.inr ⟨d, hd, by rw [if_pos hw]⟩
  linarith

/-- **Every iterate is a lower bound for every lonely time after the start.** -/
theorem iterate_le_of_lonely {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {b s : ℝ}
    (hl : Lonely n ds s) (hbs : b ≤ s) : ∀ N : ℕ, (move n ds)^[N] b ≤ s := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  intro N
  induction N with
  | zero => simpa using hbs
  | succ N ih =>
    rw [Function.iterate_succ_apply']
    exact move_le_of_lonely hpos hl ih

/-- Nothing positive precedes the bound `1/(8·m)` when `m ∈ ds` is the nearest difference. -/
theorem bound_le_of_lonely {ds : Finset ℝ} {m s : ℝ} (hm : m ∈ ds) (hmpos : 0 < m)
    (hl : Lonely n ds s) (hs : 0 < s) : 1 / (n * m) ≤ s := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  by_contra hc
  push Not at hc
  have := ConstructionN.before_floor (n := n) (by have := (Fact.out : 2 ≤ n); omega) hmpos hs (by exact_mod_cast hc)
  have h8 := hl m hm
  norm_num at this h8
  linarith

/-- **The first isolation time.**  If some iterate of the move from the bound is fixed, it is a lonely
time, and every positive lonely time is at or after it. -/
theorem first_isolation_of_fixed {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : m ∈ ds)
    (N : ℕ) (hfix : move n ds ((move n ds)^[N] (1 / (n * m))) = (move n ds)^[N] (1 / (n * m))) :
    Lonely n ds ((move n ds)^[N] (1 / (n * m))) ∧
      ∀ s, 0 < s → Lonely n ds s → (move n ds)^[N] (1 / (n * m)) ≤ s := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  refine ⟨lonely_of_fixed hpos hfix, fun s hs hl => ?_⟩
  exact iterate_le_of_lonely hpos hl (bound_le_of_lonely hm (hpos m hm) hl hs) N

/-! ## v2 — the flank at the first isolation time

The moment is always a neighbour arriving at exactly one eighth.  Positions are signed: runner `j`
sits at `fract (w j * t)` relative to the subject, where `w j = v_j - v_i` and the subject's
differences are `ds = |w j|`. -/

theorem circDist_one_eighth : circDist ((n : ℝ)⁻¹) = (n : ℝ)⁻¹ := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  unfold circDist
  have h2 := two_le_n (n := n)
  have hi : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) h2
  have h : Int.fract ((n : ℝ)⁻¹) = (n : ℝ)⁻¹ := by
    rw [Int.fract_eq_self]; constructor
    · positivity
    · linarith
  rw [h, min_eq_left]; linarith

/-- At its next opening, a runner is at exactly one eighth. -/
theorem circDist_at_nextOpening {d t : ℝ} (hd : 0 < d) :
    circDist (d * nextOpening n d t) = (n : ℝ)⁻¹ := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  unfold nextOpening
  have e : d * (((⌈d * t - (n : ℝ)⁻¹⌉ : ℝ) + (n : ℝ)⁻¹) / d)
      = (n : ℝ)⁻¹ + ((⌈d * t - (n : ℝ)⁻¹⌉ : ℤ) : ℝ) := by field_simp; ring
  rw [e, ConstructionN.circDist_add_int, circDist_one_eighth]

/-- The move lands either where it started or on the next opening of a runner in the way. -/
theorem move_eq_self_or_opening (ds : Finset ℝ) (t : ℝ) :
    move n ds t = t ∨ ∃ d ∈ ds, inWay n d t ∧ move n ds t = nextOpening n d t := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  classical
  unfold move
  induction ds using Finset.induction_on with
  | empty => left; simp
  | insert a s ha ih =>
    rw [Finset.fold_insert ha]
    rcases le_total (if inWay n a t then nextOpening n a t else t) (s.fold max t (fun d => if inWay n d t then nextOpening n d t else t)) with h | h
    · rw [max_eq_right h]
      rcases ih with h1 | ⟨d, hd, hw, he⟩
      · exact Or.inl h1
      · exact Or.inr ⟨d, Finset.mem_insert_of_mem hd, hw, he⟩
    · rw [max_eq_left h]
      by_cases hw : inWay n a t
      · exact Or.inr ⟨a, Finset.mem_insert_self a s, hw, by rw [if_pos hw]⟩
      · left; rw [if_neg hw]

/-- **Every iterate from the bound has a runner at exactly one eighth.** -/
theorem iterate_has_threshold_runner {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ}
    (hm : m ∈ ds) : ∀ N : ℕ, ∃ d ∈ ds, circDist (d * (move n ds)^[N] (1 / (n * m))) = (n : ℝ)⁻¹ := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  intro N
  induction N with
  | zero =>
    refine ⟨m, hm, ?_⟩
    have hm0 := hpos m hm
    have e : m * (1 / (n * m)) = (n : ℝ)⁻¹ := by field_simp
    show circDist (m * (1 / (n * m))) = (n : ℝ)⁻¹
    rw [e]; exact circDist_one_eighth (n := n)
  | succ N ih =>
    rw [Function.iterate_succ_apply']
    rcases move_eq_self_or_opening (n := n) ds ((move n ds)^[N] (1 / (n * m))) with h | ⟨d, hd, _, he⟩
    · rw [h]; exact ih
    · exact ⟨d, hd, by rw [he]; exact circDist_at_nextOpening (hpos d hd)⟩

/-- **A runner at exactly one eighth from a lonely subject is a flank**: the nearest runner ahead
(position `1/8`) or the nearest behind (position `7/8`). -/
theorem flank_of_threshold {ι : Type*} (y : ι → ℝ) (hl : ∀ l, (n : ℝ)⁻¹ ≤ circDist (y l))
    {j : ι} (hj : circDist (y j) = (n : ℝ)⁻¹) :
    (Int.fract (y j) = (n : ℝ)⁻¹ ∧ ∀ l, Int.fract (y j) ≤ Int.fract (y l)) ∨
    (Int.fract (y j) = 1 - (n : ℝ)⁻¹ ∧ ∀ l, Int.fract (y l) ≤ Int.fract (y j)) := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  have hmin : ∀ l, (n : ℝ)⁻¹ ≤ Int.fract (y l) ∧ Int.fract (y l) ≤ 1 - (n : ℝ)⁻¹ := by
    intro l; have := hl l; unfold circDist at this
    rw [le_min_iff] at this; exact ⟨this.1, by linarith [this.2]⟩
  unfold circDist at hj
  rcases min_choice (Int.fract (y j)) (1 - Int.fract (y j)) with h | h
  · rw [h] at hj; exact Or.inl ⟨hj, fun l => by rw [hj]; exact (hmin l).1⟩
  · rw [h] at hj
    have hf : Int.fract (y j) = 1 - (n : ℝ)⁻¹ := by linarith
    exact Or.inr ⟨hf, fun l => by rw [hf]; exact (hmin l).2⟩

/-- **The flank at the first isolation time.**  Subject's signed differences `w` (all nonzero),
`ds = |w|`, nearest difference `m`.  If an iterate `T` of the move from the bound is fixed, then the
subject is lonely at `T`, no positive lonely time precedes `T`, and some runner `j` sits at exactly
one eighth as the nearest runner ahead or the nearest behind. -/
theorem flank_at_first_isolation {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℝ)
    (hw : ∀ j, w j ≠ 0) {m : ℝ} (hm : m ∈ Finset.univ.image (fun j => |w j|)) (N : ℕ)
    (hfix : move n (Finset.univ.image (fun j => |w j|)) ((move n (Finset.univ.image (fun j => |w j|)))^[N] (1 / (n * m)))
        = (move n (Finset.univ.image (fun j => |w j|)))^[N] (1 / (n * m))) :
    let ds := Finset.univ.image (fun j => |w j|)
    let T := (move n ds)^[N] (1 / (n * m))
    (∀ j, (n : ℝ)⁻¹ ≤ circDist (w j * T)) ∧
      (∀ s, 0 < s → (∀ j, (n : ℝ)⁻¹ ≤ circDist (w j * s)) → T ≤ s) ∧
      ∃ j, circDist (w j * T) = (n : ℝ)⁻¹ ∧
        ((Int.fract (w j * T) = (n : ℝ)⁻¹ ∧ ∀ l, Int.fract (w j * T) ≤ Int.fract (w l * T)) ∨
         (Int.fract (w j * T) = 1 - (n : ℝ)⁻¹ ∧ ∀ l, Int.fract (w l * T) ≤ Int.fract (w j * T))) := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  intro ds T
  have hpos : ∀ d ∈ ds, 0 < d := by
    intro d hd; obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hd; exact abs_pos.mpr (hw j)
  have habs : ∀ j x, circDist (w j * x) = circDist (|w j| * x) := by
    intro j x; rcases abs_cases (w j) with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
    · rw [h, neg_mul, circDist.symm_neg]
  have lonely_iff : ∀ x, Lonely n ds x ↔ ∀ j, (n : ℝ)⁻¹ ≤ circDist (w j * x) := by
    intro x; constructor
    · intro h j; rw [habs]; exact h _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    · intro h d hd; obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hd; rw [← habs]; exact h j
  obtain ⟨hl, hleast⟩ := first_isolation_of_fixed hpos hm N hfix
  refine ⟨(lonely_iff T).mp hl, fun s hs h => hleast s hs ((lonely_iff s).mpr h), ?_⟩
  obtain ⟨d, hd, hdt⟩ := iterate_has_threshold_runner (n := n) hpos hm N
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hd
  have hj : circDist (w j * T) = (n : ℝ)⁻¹ := by rw [habs]; exact hdt
  exact ⟨j, hj, flank_of_threshold (fun l => w l * T) ((lonely_iff T).mp hl) hj⟩

/-! ## v3 — the move as a change of AP scale

At the instant `t = 1/(8D)` (the first spine point of the AP of gap `D`), runner `d` reads `s = d/D`.  It is in the
way exactly when `s` is within 1 of a multiple of 8, and its next opening is the first spine point of the AP of gap
`d/(8N+1)`. -/

theorem mul_inv_scale {d D : ℝ} (hD : 0 < D) : d * (1 / (n * D)) = (d / D) / n := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  field_simp

/-- **In the way at scale `D` iff the reading is within 1 of a multiple of 8.** -/
theorem inWay_at_scale_iff {d D : ℝ} (hD : 0 < D) :
    inWay n d (1 / (n * D)) ↔ ∃ N : ℤ, |d / D - n * N| < 1 := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  unfold inWay
  rw [mul_inv_scale hD]
  have h := ConstructionN.band_identity n (by have := (Fact.out : 2 ≤ n); omega) (d / D)
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
theorem nextOpening_at_scale {d D : ℝ} (hd : 0 < d) (hD : 0 < D) {N : ℤ} (hN : |d / D - n * N| < 1) :
    nextOpening n d (1 / (n * D)) = 1 / (n * (d / (n * N + 1))) := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  have hk : |d * (1 / (n * D)) - N| < (n : ℝ)⁻¹ := by
    rw [mul_inv_scale hD]
    have e : d / D / n - (N : ℝ) = (d / D - n * N) / n := by field_simp
    rw [e, abs_div, abs_of_pos hn0]
    have : |d / D - n * ↑N| / n < 1 / n := div_lt_div_of_pos_right hN hn0
    simpa using this
  have hN0 : (0 : ℝ) < n * N + 1 := by
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

noncomputable def zoneLo (n : ℕ) (d : ℝ) (N : ℤ) : ℝ := ((N : ℝ) - (n : ℝ)⁻¹) / d
noncomputable def zoneHi (n : ℕ) (d : ℝ) (N : ℤ) : ℝ := ((N : ℝ) + (n : ℝ)⁻¹) / d

/-- **In the way iff inside one of the runner's lap zones.** -/
theorem inWay_iff_zone {d t : ℝ} (hd : 0 < d) :
    inWay n d t ↔ ∃ N : ℤ, zoneLo n d N < t ∧ t < zoneHi n d N := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
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
def Run (n : ℕ) (ds : Finset ℝ) : ℝ → List (ℝ × ℤ) → ℝ → Prop
  | b, [], T => T = b
  | b, (d, N) :: L, T => d ∈ ds ∧ zoneLo n d N < b ∧ b < zoneHi n d N ∧ Run n ds (zoneHi n d N) L T

/-- A run covers everything from its start up to its end: every such time is inside some runner's zone. -/
theorem Run.covers {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) :
    ∀ (L : List (ℝ × ℤ)) (b T : ℝ), Run n ds b L T →
      b ≤ T ∧ ∀ t, b ≤ t → t < T → ∃ d ∈ ds, inWay n d t := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
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
    by_cases ht : t < zoneHi n d N
    · exact ⟨d, hd, (inWay_iff_zone (hpos d hd)).mpr ⟨N, lt_of_lt_of_le hlo h1, ht⟩⟩
    · exact hcov t (not_lt.mp ht) h2

/-- Extending a run by a zone that contains its end. -/
theorem Run.snoc {ds : Finset ℝ} {d : ℝ} {N : ℤ} (hd : d ∈ ds) :
    ∀ (L : List (ℝ × ℤ)) (b T : ℝ), Run n ds b L T → zoneLo n d N < T → T < zoneHi n d N →
      Run n ds b (L ++ [(d, N)]) (zoneHi n d N) := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
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
    {L : List (ℝ × ℤ)} {T : ℝ} (hr : Run n ds (1 / (n * m)) L T) (hT : Lonely n ds T) :
    ∀ s, 0 < s → Lonely n ds s → T ≤ s := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  intro s hs hl
  by_contra hc
  push Not at hc
  obtain ⟨-, hcov⟩ := Run.covers hpos L _ _ hr
  obtain ⟨d, hd, hw⟩ := hcov s (bound_le_of_lonely hm (hpos m hm) hl hs) hc
  exact absurd (hl d hd) (not_le.mpr hw)

theorem iterate_ge (ds : Finset ℝ) (b : ℝ) : ∀ N : ℕ, b ≤ (move n ds)^[N] b := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  intro N
  induction N with
  | zero => simp
  | succ N ih => rw [Function.iterate_succ_apply']; exact le_trans ih (le_move ds _)

/-- **Every iterate of the move is the end of a run of zones from the start**: each move adds its setter's zone. -/
theorem run_of_iterate {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (b : ℝ) :
    ∀ N : ℕ, ∃ L, Run n ds b L ((move n ds)^[N] b) := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  intro N
  induction N with
  | zero => exact ⟨[], by simp [Run]⟩
  | succ N ih =>
    obtain ⟨L, hL⟩ := ih
    rw [Function.iterate_succ_apply']
    rcases move_eq_self_or_opening (n := n) ds ((move n ds)^[N] b) with h | ⟨d, hd, hw, he⟩
    · exact ⟨L, by rw [h]; exact hL⟩
    · obtain ⟨k, hk⟩ := exists_near_int hw
      have hdpos := hpos d hd
      have hlo : zoneLo n d k < (move n ds)^[N] b := by
        have := abs_lt.mp hk; unfold zoneLo; rw [div_lt_iff₀ hdpos]; nlinarith
      have hhi : (move n ds)^[N] b < zoneHi n d k := by
        have := abs_lt.mp hk; unfold zoneHi; rw [lt_div_iff₀ hdpos]; nlinarith
      have hmv : move n ds ((move n ds)^[N] b) = zoneHi n d k := by
        rw [he, nextOpening_eq hdpos hk]; rfl
      exact ⟨L ++ [(d, k)], by rw [hmv]; exact Run.snoc hd L _ _ hL hlo hhi⟩

/-- **A run from the bound ending at a lonely time ends at the fixed point of the iteration.** -/
theorem run_end_eq_fixed_point {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : m ∈ ds) (N : ℕ)
    (hfix : move n ds ((move n ds)^[N] (1 / (n * m))) = (move n ds)^[N] (1 / (n * m)))
    {L : List (ℝ × ℤ)} {T : ℝ} (hr : Run n ds (1 / (n * m)) L T) (hT : Lonely n ds T) :
    T = (move n ds)^[N] (1 / (n * m)) := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  have hb : 0 < 1 / (n * m) := by have := hpos m hm; exact div_pos one_pos (mul_pos hn0 this)
  obtain ⟨hFl, hFleast⟩ := first_isolation_of_fixed hpos hm N hfix
  have hbT := (Run.covers hpos L _ _ hr).1
  have hFT : (move n ds)^[N] (1 / (n * m)) ≤ T := hFleast T (lt_of_lt_of_le hb hbT) hT
  have hTF : T ≤ (move n ds)^[N] (1 / (n * m)) :=
    first_isolation_of_run hpos hm hr hT _ (lt_of_lt_of_le hb (iterate_ge ds _ N)) hFl
  exact le_antisymm hTF hFT

/-- **The first isolation time as the end of the zone run.**  If the iteration from the bound reaches a fixed point
`F`, then `F` is the end of a run of lap-completion zones from the bound, the subject is lonely at `F`, no positive
lonely time precedes it, and every run from the bound that ends at a lonely time ends at `F`. -/
theorem first_isolation_as_zone_run {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : m ∈ ds) (N : ℕ)
    (hfix : move n ds ((move n ds)^[N] (1 / (n * m))) = (move n ds)^[N] (1 / (n * m))) :
    (∃ L, Run n ds (1 / (n * m)) L ((move n ds)^[N] (1 / (n * m)))) ∧
      Lonely n ds ((move n ds)^[N] (1 / (n * m))) ∧
      (∀ s, 0 < s → Lonely n ds s → (move n ds)^[N] (1 / (n * m)) ≤ s) ∧
      (∀ L T, Run n ds (1 / (n * m)) L T → Lonely n ds T → T = (move n ds)^[N] (1 / (n * m))) := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  obtain ⟨hl, hleast⟩ := first_isolation_of_fixed hpos hm N hfix
  exact ⟨run_of_iterate hpos _ N, hl, hleast, fun L T hr hT => run_end_eq_fixed_point hpos hm N hfix hr hT⟩

/-! ## v5 — finiteness: a lonely time forces the run to end

If the subject is lonely at some `s > 0`, every iterate of the move from the bound lies in the finite set
`{bound} ∪ {(k + 1/8)/d : d ∈ ds, 0 ≤ k ≤ ⌈d·s⌉}`; an iteration that never stops is strictly increasing and cannot
stay in a finite set.  So the iteration stops, and the zone run from the bound ends. -/

/-- The openings that can occur at or before `s`. -/
noncomputable def openingsUpTo (n : ℕ) (ds : Finset ℝ) (s : ℝ) : Finset ℝ :=
  ds.biUnion (fun d => (Finset.Icc (0 : ℤ) ⌈d * s⌉).image (fun k : ℤ => ((k : ℝ) + (n : ℝ)⁻¹) / d))

/-- Every iterate from a positive start below a lonely time is the start or one of those openings. -/
theorem iterate_mem_openings {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {b s : ℝ} (hb : 0 < b)
    (hl : Lonely n ds s) (hbs : b ≤ s) :
    ∀ N : ℕ, (move n ds)^[N] b ∈ insert b (openingsUpTo n ds s) := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply']
    set x := (move n ds)^[N] b with hx
    rcases move_eq_self_or_opening (n := n) ds x with h | ⟨d, hd, hw, he⟩
    · rw [h]; exact ih
    · obtain ⟨k, hk⟩ := exists_near_int hw
      have hdpos := hpos d hd
      have hval : move n ds x = ((k : ℝ) + (n : ℝ)⁻¹) / d := by rw [he, nextOpening_eq hdpos hk]
      have hxs : x ≤ s := iterate_le_of_lonely hpos hl hbs N
      have hmove_le : move n ds x ≤ s := move_le_of_lonely hpos hl hxs
      have hxb : b ≤ x := iterate_ge ds b N
      have hgt : x < move n ds x := by rw [he]; exact lt_nextOpening hdpos hw
      rw [hval] at hmove_le hgt
      have hk_up : (k : ℝ) ≤ d * s := by
        rw [div_le_iff₀ hdpos] at hmove_le; nlinarith
      have hk_lo : (0 : ℝ) < (k : ℝ) + (n : ℝ)⁻¹ := by
        have : 0 < ((k : ℝ) + (n : ℝ)⁻¹) / d := lt_trans (lt_of_lt_of_le hb hxb) hgt
        exact (div_pos_iff_of_pos_right hdpos).mp this
      have hk0 : (0 : ℤ) ≤ k := by
        by_contra hc
        push Not at hc
        have hk1 : k ≤ -1 := by omega
        have : (k : ℝ) ≤ -1 := by exact_mod_cast hk1
        norm_num at hk_lo; linarith
      have hkc : k ≤ ⌈d * s⌉ := by
        have := Int.le_ceil (d * s)
        exact_mod_cast le_trans hk_up this
      rw [hval]
      refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_image.mpr ⟨k, ?_, rfl⟩⟩)
      exact Finset.mem_Icc.mpr ⟨hk0, hkc⟩

/-- **A lonely time forces the iteration from the bound to stop.** -/
theorem exists_fixed_of_lonely {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m s : ℝ} (hm : m ∈ ds)
    (hs : 0 < s) (hl : Lonely n ds s) :
    ∃ N : ℕ, move n ds ((move n ds)^[N] (1 / (n * m))) = (move n ds)^[N] (1 / (n * m)) := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  classical
  set b := 1 / (n * m) with hbdef
  have hb : 0 < b := by have := hpos m hm; exact div_pos one_pos (mul_pos hn0 this)
  have hbs : b ≤ s := bound_le_of_lonely hm (hpos m hm) hl hs
  by_contra hne
  push Not at hne
  have hsm : StrictMono (fun N : ℕ => (move n ds)^[N] b) := by
    refine strictMono_nat_of_lt_succ (fun N => ?_)
    show (move n ds)^[N] b < (move n ds)^[N + 1] b
    rw [Function.iterate_succ_apply']
    exact lt_of_le_of_ne (le_move ds _) (fun h => hne N h.symm)
  let T : Finset ℝ := insert b (openingsUpTo n ds s)
  let g : ℕ → T := fun N => ⟨(move n ds)^[N] b, iterate_mem_openings hpos hb hl hbs N⟩
  have hg : Function.Injective g := by
    intro i j hij
    exact hsm.injective (congrArg Subtype.val hij)
  exact not_injective_infinite_finite g hg

/-- **The run of lap zones from the bound ends iff the subject is ever lonely.**  Lonely at some positive time ⟺ the
iteration from the bound reaches a fixed point ⟺ there is a run of lap zones from the bound ending at a lonely time. -/
theorem lonely_iff_run_ends {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : m ∈ ds) :
    ((∃ s, 0 < s ∧ Lonely n ds s) ↔
      ∃ N : ℕ, move n ds ((move n ds)^[N] (1 / (n * m))) = (move n ds)^[N] (1 / (n * m))) ∧
    ((∃ s, 0 < s ∧ Lonely n ds s) ↔ ∃ L T, Run n ds (1 / (n * m)) L T ∧ Lonely n ds T) := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  have hb : 0 < 1 / (n * m) := by have := hpos m hm; exact div_pos one_pos (mul_pos hn0 this)
  have h1 : (∃ s, 0 < s ∧ Lonely n ds s) ↔
      ∃ N : ℕ, move n ds ((move n ds)^[N] (1 / (n * m))) = (move n ds)^[N] (1 / (n * m)) := by
    constructor
    · rintro ⟨s, hs, hl⟩; exact exists_fixed_of_lonely hpos hm hs hl
    · rintro ⟨N, hfix⟩
      exact ⟨_, lt_of_lt_of_le hb (iterate_ge ds _ N), lonely_of_fixed hpos hfix⟩
  refine ⟨h1, ?_⟩
  constructor
  · intro h
    obtain ⟨N, hfix⟩ := h1.mp h
    obtain ⟨L, hL⟩ := run_of_iterate (n := n) hpos (1 / (n * m)) N
    exact ⟨L, _, hL, lonely_of_fixed hpos hfix⟩
  · rintro ⟨L, T, hr, hT⟩
    exact ⟨T, lt_of_lt_of_le hb (Run.covers hpos L _ _ hr).1, hT⟩

/-! ## v5 — drift lines: the lap zones in the AP-deviation frame

The subject's nearest difference is `m`.  A runner's reading is `a + e`: AP index `a` (an integer) plus deviation `e`,
so its difference is `(a + e)·m`.  At the subject's AP instant `n = 8K + r` (time `n/(8m)`) the runner sits at its AP
slot `r·a` plus its drift `n·e`, in eighths, plus `K·a` whole laps.  It is in the way exactly while that drift line is
within one eighth of the subject — equivalently, while `n` lies in one of the explicit intervals
`((8M − 1)/(a+e), (8M + 1)/(a+e))`, which are its lap zones read at AP instants. -/

/-- **Position at an AP instant: AP slot plus drift, in eighths, plus whole laps.** -/
theorem drift_position {m : ℝ} (hm : 0 < m) (a K r : ℤ) (e : ℝ) :
    ((a : ℝ) + e) * m * (((n * K + r : ℤ) : ℝ) / (n * m))
      = ((r * a : ℤ) + ((n * K + r : ℤ) : ℝ) * e) / n + ((K * a : ℤ) : ℝ) := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  push_cast
  field_simp
  ring

/-- **In the way at an AP instant iff the drift line is within one slot of the subject.** -/
theorem inWay_at_ap_instant_iff_drift {m : ℝ} (hm : 0 < m) (a K r : ℤ) (e : ℝ) :
    inWay n (((a : ℝ) + e) * m) (((n * K + r : ℤ) : ℝ) / (n * m)) ↔
      ∃ M : ℤ, |((r * a : ℤ) : ℝ) + ((n * K + r : ℤ) : ℝ) * e - n * M| < 1 := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  unfold inWay
  rw [drift_position hm, ConstructionN.circDist_add_int]
  have h := ConstructionN.band_identity n (by have := (Fact.out : 2 ≤ n); omega) (((r * a : ℤ) : ℝ) + ((n * K + r : ℤ) : ℝ) * e)
  push_cast at h ⊢
  constructor
  · intro hlt
    by_contra hc
    push Not at hc
    exact absurd (h.mpr hc) (not_le.mpr hlt)
  · rintro ⟨M, hM⟩
    by_contra hc
    push Not at hc
    exact absurd (h.mp hc M) (not_le.mpr hM)

/-- **The blocked AP instants are explicit intervals in the instant count `n`.** -/
theorem drift_blocked_iff_interval (a K r : ℤ) {e : ℝ} (hs : 0 < (a : ℝ) + e) :
    (∃ M : ℤ, |((r * a : ℤ) : ℝ) + ((n * K + r : ℤ) : ℝ) * e - n * M| < 1) ↔
      ∃ M' : ℤ, (n * (M' : ℝ) - 1) / ((a : ℝ) + e) < ((n * K + r : ℤ) : ℝ) ∧
        ((n * K + r : ℤ) : ℝ) < (n * (M' : ℝ) + 1) / ((a : ℝ) + e) := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  have key : ∀ M : ℤ, ((r * a : ℤ) : ℝ) + ((n * K + r : ℤ) : ℝ) * e - n * M
      = ((n * K + r : ℤ) : ℝ) * ((a : ℝ) + e) - n * ((M + K * a : ℤ) : ℝ) := by
    intro M; push_cast; ring
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M + K * a, ?_, ?_⟩
    · rw [div_lt_iff₀ hs]; have := abs_lt.mp (key M ▸ hM); push_cast at this ⊢; linarith
    · rw [lt_div_iff₀ hs]; have := abs_lt.mp (key M ▸ hM); push_cast at this ⊢; linarith
  · rintro ⟨M', h1, h2⟩
    refine ⟨M' - K * a, ?_⟩
    rw [div_lt_iff₀ hs] at h1; rw [lt_div_iff₀ hs] at h2
    rw [key, abs_lt]
    push_cast at h1 h2 ⊢
    constructor <;> linarith

/-- **Those intervals are the runner's lap zones read at the subject's AP instants.** -/
theorem zone_at_ap_instant_iff {m : ℝ} (hm : 0 < m) {s : ℝ} (hs : 0 < s) (j M : ℤ) :
    (zoneLo n (s * m) M < (j : ℝ) / (n * m) ∧ (j : ℝ) / (n * m) < zoneHi n (s * m) M) ↔
      ((n * (M : ℝ) - 1) / s < j ∧ (j : ℝ) < (n * (M : ℝ) + 1) / s) := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  have hsm : 0 < s * m := mul_pos hs hm
  unfold zoneLo zoneHi
  rw [div_lt_div_iff₀ hsm (by positivity), div_lt_div_iff₀ (by positivity) hsm,
      div_lt_iff₀ hs, lt_div_iff₀ hs]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith

/-! ## v6 — an exact slot-sharer removes every own-AP instant

A runner whose difference is `8b·m` — AP index a multiple of 8, deviation 0 — sits a whole number of laps from the
subject at every AP instant `j/(8m)`.  It is in the way at all of them, so the subject is lonely at none. -/

theorem circDist_intCast' (k : ℤ) : circDist (k : ℝ) = 0 := by
  unfold circDist
  rw [Int.fract_intCast]
  simp

/-- **An exact slot-sharer is in the way at every AP instant of the subject.** -/
theorem sharer_inWay_at_ap_instant {m : ℝ} (hm : 0 < m) (b j : ℤ) :
    inWay n (((n * b : ℤ) : ℝ) * m) ((j : ℝ) / (n * m)) := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  unfold inWay
  have e : ((n * b : ℤ) : ℝ) * m * ((j : ℝ) / (n * m)) = ((b * j : ℤ) : ℝ) := by
    have : 0 < n := by have := (Fact.out : 2 ≤ n); omega
    push_cast; field_simp
  rw [e, circDist_intCast']
  exact inv_pos.mpr hn0

/-- **With an exact slot-sharer present, the subject is lonely at no AP instant `j/(8m)`.** -/
theorem not_lonely_at_ap_instant_of_sharer {ds : Finset ℝ} {m : ℝ} (hm : 0 < m) {b : ℤ}
    (hb : ((n * b : ℤ) : ℝ) * m ∈ ds) (j : ℤ) :
    ¬ Lonely n ds ((j : ℝ) / (n * m)) := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmi : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnn
  intro hl
  have h1 := hl _ hb
  have h2 := sharer_inWay_at_ap_instant (n := n) hm b j
  unfold inWay at h2
  exact absurd h1 (not_le.mpr h2)

/-! ## Specialisation check: `n = 8` recovers the v6 statements. -/

instance : Fact (2 ≤ 8) := ⟨by norm_num⟩

example {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : m ∈ ds) :
    ((∃ s, 0 < s ∧ Lonely 8 ds s) ↔
      ∃ N : ℕ, move 8 ds ((move 8 ds)^[N] (1 / ((8 : ℕ) * m))) = (move 8 ds)^[N] (1 / ((8 : ℕ) * m))) :=
  (lonely_iff_run_ends (n := 8) hpos hm).1

-- v6 is not importable (outside the tree); its definition is `circDist (d * t) < (8 : ℝ)⁻¹`.
example (d t : ℝ) : inWay 8 d t ↔ circDist (d * t) < (8 : ℝ)⁻¹ := by
  unfold inWay; norm_num

end MomentIterationN

#print axioms MomentIterationN.inWay_until_opening
#print axioms MomentIterationN.move_le_of_lonely
#print axioms MomentIterationN.lonely_of_fixed
#print axioms MomentIterationN.iterate_le_of_lonely
#print axioms MomentIterationN.first_isolation_of_fixed
#print axioms MomentIterationN.iterate_has_threshold_runner
#print axioms MomentIterationN.flank_of_threshold
#print axioms MomentIterationN.flank_at_first_isolation
#print axioms MomentIterationN.inWay_at_scale_iff
#print axioms MomentIterationN.nextOpening_at_scale
#print axioms MomentIterationN.inWay_iff_zone
#print axioms MomentIterationN.first_isolation_of_run
#print axioms MomentIterationN.run_of_iterate
#print axioms MomentIterationN.run_end_eq_fixed_point
#print axioms MomentIterationN.first_isolation_as_zone_run
#print axioms MomentIterationN.iterate_mem_openings
#print axioms MomentIterationN.exists_fixed_of_lonely
#print axioms MomentIterationN.lonely_iff_run_ends
#print axioms MomentIterationN.drift_position
#print axioms MomentIterationN.inWay_at_ap_instant_iff_drift
#print axioms MomentIterationN.drift_blocked_iff_interval
#print axioms MomentIterationN.zone_at_ap_instant_iff
#print axioms MomentIterationN.sharer_inWay_at_ap_instant
#print axioms MomentIterationN.not_lonely_at_ap_instant_of_sharer

/-! ## v2 — n = 3: the iteration from the bound stops within one move

Threshold `1/3`, at most two differences, bound `1/(3m)` at the nearest difference `m`.  At the bound `m` reads 1
(exactly on the threshold).  If the other runner `b` is in the way, its reading `b/m` is within 1 of `3N` with `N ≥ 1`,
and the move goes to the spine point of scale `b/(3N+1)`.  There `b` reads `3N+1` (on the threshold) and `m` reads
`(3N+1)·m/b ∈ (1, 2]`, inside the clear window.  So the iterate after one move is fixed.  Proved from the scale bridge
(`inWay_at_scale_iff`, `nextOpening_at_scale`) and the move lemmas only. -/

namespace TerminationThree

open ConstructionN MomentIterationN

instance fact_two_le_three : Fact (2 ≤ 3) := ⟨by norm_num⟩

/-- A lonely instant is fixed by the move. -/
theorem move_eq_self_of_lonely {n : ℕ} [Fact (2 ≤ n)] {ds : Finset ℝ} {t : ℝ} (hl : Lonely n ds t) :
    move n ds t = t := by
  rcases move_eq_self_or_opening (n := n) ds t with h | ⟨d, hd, hw, -⟩
  · exact h
  · exact absurd (hl d hd) (not_le.mpr hw)

/-- **The nearest runner's reading after the move lies in `(1, 2]`, so it is clear.** -/
theorem nearest_clear_after_move {m b : ℝ} (hm : 0 < m) (hmb : m ≤ b) {N : ℤ}
    (hN : |b / m - 3 * N| < 1) :
    (3 : ℝ)⁻¹ ≤ circDist (m * (1 / (3 * (b / (3 * N + 1))))) := by
  have hb : 0 < b := lt_of_lt_of_le hm hmb
  have h1 := abs_lt.mp hN
  have hr : 1 ≤ b / m := by rw [le_div_iff₀ hm]; linarith
  have hN1 : (1 : ℝ) ≤ N := by
    have h0 : (0 : ℝ) < N := by linarith
    have h0' : (0 : ℤ) < N := by exact_mod_cast h0
    exact_mod_cast (show (1 : ℤ) ≤ N by omega)
  have hup : b < (3 * N + 1) * m := (div_lt_iff₀ hm).mp (by linarith)
  have hlo : (3 * N - 1) * m < b := (lt_div_iff₀ hm).mp (by linarith)
  have hpos : (0 : ℝ) < 3 * N + 1 := by linarith
  have e : m * (1 / (3 * (b / (3 * N + 1)))) = (m * (3 * N + 1) / b) / 3 := by
    field_simp
  have hx1 : 1 < m * (3 * N + 1) / b := by
    rw [lt_div_iff₀ hb]; linarith
  have hx2 : m * (3 * N + 1) / b ≤ 2 := by
    rw [div_le_iff₀ hb]; nlinarith
  rw [e]
  unfold circDist
  have hf : Int.fract (m * (3 * N + 1) / b / 3) = m * (3 * N + 1) / b / 3 := by
    rw [Int.fract_eq_self]; constructor <;> linarith
  rw [hf]
  apply le_min <;> linarith

/-- **n = 3: the iteration from the bound stops within one move.**  For at most two positive differences with nearest
`m`, the first iterate of the move from `1/(3m)` is fixed. -/
theorem three_stops_within_one_move {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ 2)
    {m : ℝ} (hm : m ∈ ds) (hmin : ∀ d ∈ ds, m ≤ d) :
    move 3 ds (move 3 ds (1 / ((3 : ℕ) * m))) = move 3 ds (1 / ((3 : ℕ) * m)) := by
  have hm0 := hpos m hm
  rcases move_eq_self_or_opening (n := 3) ds (1 / ((3 : ℕ) * m)) with h | ⟨d, hd, hw, he⟩
  · rw [h, h]
  · have hd0 := hpos d hd
    have hdm : d ≠ m := by
      rintro rfl
      unfold inWay at hw
      have e : d * (1 / ((3 : ℕ) * d)) = ((3 : ℕ) : ℝ)⁻¹ := by field_simp
      rw [e, circDist_one_eighth (n := 3)] at hw
      exact lt_irrefl _ hw
    have hall : ∀ e ∈ ds, e = m ∨ e = d := by
      intro e he'
      by_contra hc
      push Not at hc
      have hsub : ({m, d, e} : Finset ℝ) ⊆ ds := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      have h3 : ({m, d, e} : Finset ℝ).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hc.2)]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hdm, Ne.symm hc.1⟩
      have := Finset.card_le_card hsub
      omega
    obtain ⟨N, hN⟩ := (inWay_at_scale_iff (n := 3) hm0).mp hw
    have hN' : |d / m - 3 * N| < 1 := by push_cast at hN; exact hN
    rw [he]
    apply move_eq_self_of_lonely
    intro e he'
    rcases hall e he' with rfl | rfl
    · rw [nextOpening_at_scale (n := 3) hd0 hm0 hN]
      push_cast
      exact nearest_clear_after_move hm0 (hmin d hd) hN'
    · exact (circDist_at_nextOpening (n := 3) hd0).ge

/-- **n = 3: the first isolation time is the first iterate.**  The subject is lonely there and at no earlier positive
time. -/
theorem three_first_isolation {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ 2)
    {m : ℝ} (hm : m ∈ ds) (hmin : ∀ d ∈ ds, m ≤ d) :
    Lonely 3 ds (move 3 ds (1 / ((3 : ℕ) * m))) ∧
      ∀ s, 0 < s → Lonely 3 ds s → move 3 ds (1 / ((3 : ℕ) * m)) ≤ s := by
  have hfix := three_stops_within_one_move hpos hcard hm hmin
  have := first_isolation_of_fixed (n := 3) hpos hm 1 (by simpa using hfix)
  simpa using this

end TerminationThree

#print axioms TerminationThree.three_stops_within_one_move
#print axioms TerminationThree.three_first_isolation
