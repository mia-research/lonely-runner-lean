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

/-! ## v3 — n = 4: the iteration from the bound stops within three moves

Threshold `1/4`, at most three differences, nearest `a`, bound `t₀ = 1/(4a)`.  Every move lands on the opening
`(k + 1/n)/x` of a runner `x` in the way (`step_cases`); a runner is never in the way at its own opening.

**Return lemma** (every `n`): if `x` sits at its lap-`P` opening, the next move is set by `y` at lap `Q`, and `x` is in the
way again after that move, then `Q·(n − 2) < 2P + 1`.  At `n = 4`: `Q ≤ P`.

**n = 4.** With `τ = a·t`: after move 1 (setter `x₁`, lap `k₁ ≥ 1`) `τ < 5/12`; after move 2 (setter `x₂ ≠ x₁`, lap `k₂ ≥ 1`)
`3t₂ < 5t₁`, so `τ < 25/36`.  In both `a` is clear, so a third setter is `x₁` again: the return lemma gives `k₂ ≤ k₁`,
and returning forces `k₃ ≥ k₁ + 1` and `3k₃ ≤ 5k₁ + 1`, whence `τ < 3/4` and `a` is still clear.  A fourth setter would
be `x₂`, and the return lemma would give `k₃ ≤ k₂ ≤ k₁ < k₃`. -/

namespace TerminationFour

open ConstructionN MomentIterationN TerminationThree

instance fact_two_le_four : Fact (2 ≤ 4) := ⟨by norm_num⟩

theorem inWay_of_near {n : ℕ} {x t : ℝ} {k : ℤ} (h : |x * t - k| < (n : ℝ)⁻¹) : inWay n x t := by
  unfold inWay
  exact lt_of_le_of_lt (circDist_le_abs_sub_int (x * t) k) h

/-- The move stays, or lands on the opening `(k + 1/n)/x` of a runner `x` in the way at `t`. -/
theorem step_cases {n : ℕ} [Fact (2 ≤ n)] {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (t : ℝ) :
    move n ds t = t ∨
      ∃ x ∈ ds, ∃ k : ℤ, |x * t - k| < (n : ℝ)⁻¹ ∧ move n ds t = ((k : ℝ) + (n : ℝ)⁻¹) / x := by
  rcases move_eq_self_or_opening (n := n) ds t with h | ⟨x, hx, hw, he⟩
  · exact Or.inl h
  · obtain ⟨k, hk⟩ := exists_near_int hw
    exact Or.inr ⟨x, hx, k, hk, by rw [he, nextOpening_eq (hpos x hx) hk]⟩

/-- A runner is not in the way at its own opening. -/
theorem not_inWay_at_own_opening {n : ℕ} [Fact (2 ≤ n)] {x : ℝ} (hx : 0 < x) (k : ℤ) :
    ¬ inWay n x (((k : ℝ) + (n : ℝ)⁻¹) / x) := by
  unfold inWay
  have e : x * (((k : ℝ) + (n : ℝ)⁻¹) / x) = (n : ℝ)⁻¹ + ((k : ℤ) : ℝ) := by field_simp; ring
  rw [e, ConstructionN.circDist_add_int, circDist_one_eighth (n := n)]
  exact lt_irrefl _

/-- **Return lemma.**  `x` sits at its lap-`P` opening `t`; `y` is in the way at `t` near lap `Q`; the move goes to `y`'s
opening `t'` after `t`.  If `x` is in the way at `t'`, then `Q·(n − 2) < 2P + 1`. -/
theorem return_lemma {n : ℕ} [Fact (2 ≤ n)] {x y : ℝ} (hx : 0 < x) (hy : 0 < y) {P Q : ℤ} (hP : 0 ≤ P)
    (hyQ : |y * (((P : ℝ) + (n : ℝ)⁻¹) / x) - Q| < (n : ℝ)⁻¹)
    (hlater : ((P : ℝ) + (n : ℝ)⁻¹) / x < ((Q : ℝ) + (n : ℝ)⁻¹) / y)
    (hret : inWay n x (((Q : ℝ) + (n : ℝ)⁻¹) / y)) :
    Q * ((n : ℤ) - 2) < 2 * P + 1 := by
  have hn2 : (2 : ℝ) ≤ n := two_le_n
  have hn0 : (0 : ℝ) < n := n_pos
  set h : ℝ := (n : ℝ)⁻¹ with hh
  have hhn : (n : ℝ) * h = 1 := mul_inv_cancel₀ hn0.ne'
  have hh0 : 0 < h := inv_pos.mpr hn0
  have hhle : h ≤ 1 / 2 := by have := inv_le_half (n := n); rw [hh]; linarith
  have hPr : (0 : ℝ) ≤ P := by exact_mod_cast hP
  obtain ⟨k, hk⟩ := exists_near_int hret
  have hk' := abs_lt.mp hk
  -- `x t' > x t = P + h`, so the lap `k` is past `P`
  have hxt : x * (((P : ℝ) + h) / x) = P + h := by field_simp
  have hxt' : (P : ℝ) + h < x * (((Q : ℝ) + h) / y) := by
    rw [← hxt]; exact mul_lt_mul_of_pos_left hlater hx
  have hkP : (P : ℝ) + 1 ≤ k := by
    have : (P : ℝ) < k := by linarith
    have : P < k := by exact_mod_cast this
    exact_mod_cast (show P + 1 ≤ k by omega)
  have hxQ : x * (((Q : ℝ) + h) / y) = x * (Q + h) / y := by ring
  -- (i) `(P + 1 − h)·y < x·(Q + h)`
  have h1 : ((P : ℝ) + 1 - h) * y < x * (Q + h) := by
    have : (P : ℝ) + 1 - h < x * (Q + h) / y := by rw [← hxQ]; linarith
    exact (lt_div_iff₀ hy).mp this
  -- (ii) `(Q − h)·x < y·(P + h)`
  have hyQ' := abs_lt.mp hyQ
  have hyP : y * (((P : ℝ) + h) / x) = y * (P + h) / x := by ring
  have h2 : ((Q : ℝ) - h) * x < y * (P + h) := by
    have : (Q : ℝ) - h < y * (P + h) / x := by rw [← hyP]; linarith
    exact (lt_div_iff₀ hx).mp this
  have hPh : 0 < (P : ℝ) + h := by linarith
  have hPh1 : 0 < (P : ℝ) + 1 - h := by linarith
  have m1 := mul_lt_mul_of_pos_left h2 hPh1
  have m2 := mul_lt_mul_of_pos_left h1 hPh
  have h3 : ((P : ℝ) + 1 - h) * ((Q : ℝ) - h) * x < ((Q : ℝ) + h) * ((P : ℝ) + h) * x := by nlinarith
  have h4 : ((P : ℝ) + 1 - h) * ((Q : ℝ) - h) < ((Q : ℝ) + h) * ((P : ℝ) + h) :=
    lt_of_mul_lt_mul_right h3 hx.le
  have h5 : (Q : ℝ) < 2 * h * Q + 2 * h * P + h := by nlinarith
  have h6 : (n : ℝ) * Q < 2 * Q + 2 * P + 1 := by
    have := mul_lt_mul_of_pos_left h5 hn0
    have e : (n : ℝ) * (2 * h * Q + 2 * h * P + h) = 2 * Q + 2 * P + 1 := by
      have : (n : ℝ) * (2 * h * Q + 2 * h * P + h) = ((n : ℝ) * h) * (2 * Q + 2 * P + 1) := by ring
      rw [this, hhn, one_mul]
    linarith
  have : ((Q * ((n : ℤ) - 2) : ℤ) : ℝ) < ((2 * P + 1 : ℤ) : ℝ) := by push_cast; linarith
  exact_mod_cast this

/-- At threshold `1/4`, a runner whose position lies in `[1/4, 3/4]` is clear. -/
theorem clear_in_window {y : ℝ} (h1 : 1 / 4 ≤ y) (h2 : y ≤ 3 / 4) : ((4 : ℕ) : ℝ)⁻¹ ≤ circDist y := by
  unfold circDist
  have hf : Int.fract y = y := by rw [Int.fract_eq_self]; constructor <;> linarith
  rw [hf]; push_cast
  apply le_min <;> linarith

theorem mem_three {ds : Finset ℝ} (hcard : ds.card ≤ 3) {a b c : ℝ} (ha : a ∈ ds) (hb : b ∈ ds)
    (hc : c ∈ ds) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : ∀ e ∈ ds, e = a ∨ e = b ∨ e = c := by
  intro e he
  by_contra hne
  push Not at hne
  have hsub : ({a, b, c, e} : Finset ℝ) ⊆ ds := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> assumption
  have h4 : ({a, b, c, e} : Finset ℝ).card = 4 := by
    simp [Finset.card_insert_of_notMem, hab, hac, hbc, hne.1.symm, hne.2.1.symm, hne.2.2.symm]
  have := Finset.card_le_card hsub
  omega

/-- **n = 4: the iteration from the bound stops within three moves, before the nearest runner reads 3.**  For at most
three positive differences with nearest `a`, the third iterate of the move from `1/(4a)` is fixed, and `a·T < 3/4`. -/
theorem four_stops_within_three_moves {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ 3)
    {a : ℝ} (ha : a ∈ ds) (hmin : ∀ d ∈ ds, a ≤ d) :
    move 4 ds ((move 4 ds)^[3] (1 / ((4 : ℕ) * a))) = (move 4 ds)^[3] (1 / ((4 : ℕ) * a)) ∧
      a * (move 4 ds)^[3] (1 / ((4 : ℕ) * a)) < 3 / 4 := by
  have ha0 := hpos a ha
  have h4 : ((4 : ℕ) : ℝ)⁻¹ = 1 / 4 := by norm_num
  set t0 := 1 / ((4 : ℕ) * a) with ht0
  show move 4 ds (move 4 ds (move 4 ds (move 4 ds t0))) = move 4 ds (move 4 ds (move 4 ds t0)) ∧
    a * move 4 ds (move 4 ds (move 4 ds t0)) < 3 / 4
  have hat0 : a * t0 = 1 / 4 := by rw [ht0]; push_cast; field_simp
  have ht00 : 0 < t0 := by rw [ht0]; positivity
  have aclear : ∀ t, 1 / 4 ≤ a * t → a * t ≤ 3 / 4 → ¬ inWay 4 a t := by
    intro t h1 h2 hw
    unfold inWay at hw
    exact absurd (clear_in_window h1 h2) (not_le.mpr hw)
  -- move 1
  rcases step_cases (n := 4) hpos t0 with e1 | ⟨x1, hx1, k1, hk1, e1⟩
  · refine ⟨by simp only [e1], ?_⟩
    simp only [e1]; linarith
  set t1 := move 4 ds t0 with ht1
  have hx10 := hpos x1 hx1
  have hw1 : inWay 4 x1 t0 := inWay_of_near hk1
  have hx1a : x1 ≠ a := fun h => aclear t0 (by linarith) (by linarith) (h ▸ hw1)
  have hk1' : |x1 * t0 - k1| < 1 / 4 := by rwa [h4] at hk1
  have e1' : t1 = ((k1 : ℝ) + 1 / 4) / x1 := by rw [e1, h4]
  have hk1a := abs_lt.mp hk1'
  have hx1t0 : 1 / 4 ≤ x1 * t0 := by
    rw [← hat0]; exact mul_le_mul_of_nonneg_right (hmin x1 hx1) (by positivity)
  have hk1pos : (1 : ℤ) ≤ k1 := by
    have : (0 : ℝ) < k1 := by linarith
    have : (0 : ℤ) < k1 := by exact_mod_cast this
    omega
  have hk1r : (1 : ℝ) ≤ k1 := by exact_mod_cast hk1pos
  have hx1t1 : x1 * t1 = k1 + 1 / 4 := by rw [e1']; field_simp
  have hx1big : a * (4 * k1 - 1) < x1 := by
    have e : x1 * t0 = x1 / (4 * a) := by rw [ht0]; push_cast; field_simp
    have : (k1 : ℝ) - 1 / 4 < x1 / (4 * a) := by rw [← e]; linarith
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * a)).mp this
    linear_combination this
  have hlt1 : t0 < t1 := by
    have : x1 * t0 < x1 * t1 := by rw [hx1t1]; linarith
    exact lt_of_mul_lt_mul_left this hx10.le
  have hat1lo : 1 / 4 < a * t1 := by rw [← hat0]; exact mul_lt_mul_of_pos_left hlt1 ha0
  have hat1 : a * t1 < 5 / 12 := by
    have hp : 0 ≤ a * ((k1 : ℝ) - 1) := mul_nonneg ha0.le (by linarith)
    rw [e1', ← mul_div_assoc, div_lt_iff₀ hx10]
    linear_combination (5 / 12) * hx1big + (2 / 3) * hp
  -- move 2
  rcases step_cases (n := 4) hpos t1 with e2 | ⟨x2, hx2, k2, hk2, e2⟩
  · refine ⟨by simp only [e2], ?_⟩
    simp only [e2]; linarith
  set t2 := move 4 ds t1 with ht2
  have hx20 := hpos x2 hx2
  have hw2 : inWay 4 x2 t1 := inWay_of_near hk2
  have hx2a : x2 ≠ a := fun h => aclear t1 (by linarith) (by linarith) (h ▸ hw2)
  have hx21 : x2 ≠ x1 := by
    intro h; rw [h, e1] at hw2; exact not_inWay_at_own_opening hx10 k1 hw2
  have hk2' : |x2 * t1 - k2| < 1 / 4 := by rwa [h4] at hk2
  have e2' : t2 = ((k2 : ℝ) + 1 / 4) / x2 := by rw [e2, h4]
  have hk2a := abs_lt.mp hk2'
  have hx2t1 : 1 / 4 < x2 * t1 := by
    have : a * t1 ≤ x2 * t1 := mul_le_mul_of_nonneg_right (hmin x2 hx2) (by linarith)
    linarith
  have hk2pos : (1 : ℤ) ≤ k2 := by
    have : (0 : ℝ) < k2 := by linarith
    have : (0 : ℤ) < k2 := by exact_mod_cast this
    omega
  have hk2r : (1 : ℝ) ≤ k2 := by exact_mod_cast hk2pos
  have hx2t2 : x2 * t2 = k2 + 1 / 4 := by rw [e2']; field_simp
  have hlt2 : t1 < t2 := by
    have : x2 * t1 < x2 * t2 := by rw [hx2t2]; linarith
    exact lt_of_mul_lt_mul_left this hx20.le
  have h35 : 3 * t2 < 5 * t1 := by
    have : x2 * (3 * t2) < x2 * (5 * t1) := by
      linear_combination 3 * hx2t2 + 5 * hk2a.1 + 2 * hk2r
    exact lt_of_mul_lt_mul_left this hx20.le
  have hat2lo : 1 / 4 < a * t2 := by linarith [mul_lt_mul_of_pos_left hlt2 ha0]
  have hat2 : a * t2 < 25 / 36 := by
    have m := mul_lt_mul_of_pos_left h35 ha0
    linear_combination (1 / 3) * m + (5 / 3) * hat1
  -- move 3
  rcases step_cases (n := 4) hpos t2 with e3 | ⟨x3, hx3, k3, hk3, e3⟩
  · refine ⟨by simp only [e3], ?_⟩
    simp only [e3]; linarith
  set t3 := move 4 ds t2 with ht3
  have hw3 : inWay 4 x3 t2 := inWay_of_near hk3
  have hx3a : x3 ≠ a := fun h => aclear t2 (by linarith) (by linarith) (h ▸ hw3)
  have hx32 : x3 ≠ x2 := by
    intro h; rw [h, e2] at hw3; exact not_inWay_at_own_opening hx20 k2 hw3
  have hx31 : x3 = x1 := by
    rcases mem_three hcard ha hx1 hx2 (Ne.symm hx1a) (Ne.symm hx2a) (Ne.symm hx21) x3 hx3 with h | h | h
    · exact absurd h hx3a
    · exact h
    · exact absurd h hx32
  rw [hx31] at hw3 hk3 e3
  have hk21 : k2 ≤ k1 := by
    have := return_lemma (n := 4) (x := x1) (y := x2) (P := k1) (Q := k2) hx10 hx20 (by omega)
      (by rw [← e1]; exact hk2) (by rw [← e1, ← e2]; exact hlt2) (by rw [← e2]; exact hw3)
    push_cast at this
    omega
  have hk3' : |x1 * t2 - k3| < 1 / 4 := by rwa [h4] at hk3
  have e3' : t3 = ((k3 : ℝ) + 1 / 4) / x1 := by rw [e3, h4]
  have hk3a := abs_lt.mp hk3'
  have hx1t2 : (k1 : ℝ) + 1 / 4 < x1 * t2 := by rw [← hx1t1]; exact mul_lt_mul_of_pos_left hlt2 hx10
  have hk31 : k1 + 1 ≤ k3 := by
    have : (k1 : ℝ) < k3 := by linarith
    have : k1 < k3 := by exact_mod_cast this
    omega
  have hk3up : 3 * k3 ≤ 5 * k1 + 1 := by
    have hA : 3 * (x1 * t2) < 5 * (x1 * t1) := by
      have m := mul_lt_mul_of_pos_left h35 hx10
      linear_combination m
    have : (3 * k3 : ℝ) < 5 * k1 + 2 := by rw [hx1t1] at hA; linarith
    have : 3 * k3 < 5 * k1 + 2 := by exact_mod_cast this
    omega
  have hx1t3 : x1 * t3 = k3 + 1 / 4 := by rw [e3']; field_simp
  have hlt3 : t2 < t3 := by
    have : x1 * t2 < x1 * t3 := by rw [hx1t3]; linarith
    exact lt_of_mul_lt_mul_left this hx10.le
  have hat3lo : 1 / 4 < a * t3 := by linarith [mul_lt_mul_of_pos_left hlt3 ha0]
  have hint : 4 * k3 + 1 ≤ 12 * k1 - 3 := by omega
  have hintr : (4 * k3 + 1 : ℝ) ≤ 12 * k1 - 3 := by exact_mod_cast hint
  have hat3 : a * t3 < 3 / 4 := by
    have m := mul_le_mul_of_nonneg_left hintr ha0.le
    rw [e3', ← mul_div_assoc, div_lt_iff₀ hx10]
    linear_combination (1 / 4) * m + (3 / 4) * hx1big
  -- no fourth move
  rcases step_cases (n := 4) hpos t3 with e4 | ⟨x4, hx4, k4, hk4, e4⟩
  · exact ⟨e4, hat3⟩
  exfalso
  have hw4 : inWay 4 x4 t3 := inWay_of_near hk4
  have hx4a : x4 ≠ a := fun h => aclear t3 (by linarith) (by linarith) (h ▸ hw4)
  have hx41 : x4 ≠ x1 := by
    intro h; rw [h, e3] at hw4; exact not_inWay_at_own_opening hx10 k3 hw4
  have hx42 : x4 = x2 := by
    rcases mem_three hcard ha hx1 hx2 (Ne.symm hx1a) (Ne.symm hx2a) (Ne.symm hx21) x4 hx4 with h | h | h
    · exact absurd h hx4a
    · exact absurd h hx41
    · exact h
  rw [hx42] at hw4
  have := return_lemma (n := 4) (x := x2) (y := x1) (P := k2) (Q := k3) hx20 hx10 (by omega)
    (by rw [← e2]; exact hk3) (by rw [← e2, ← e3]; exact hlt3) (by rw [← e3]; exact hw4)
  push_cast at this
  omega

/-- **n = 4: the first isolation time is the third iterate, before `3/(4a)`.** -/
theorem four_first_isolation {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ 3)
    {a : ℝ} (ha : a ∈ ds) (hmin : ∀ d ∈ ds, a ≤ d) :
    Lonely 4 ds ((move 4 ds)^[3] (1 / ((4 : ℕ) * a))) ∧
      (∀ s, 0 < s → Lonely 4 ds s → (move 4 ds)^[3] (1 / ((4 : ℕ) * a)) ≤ s) ∧
      a * (move 4 ds)^[3] (1 / ((4 : ℕ) * a)) < 3 / 4 := by
  obtain ⟨hfix, hlt⟩ := four_stops_within_three_moves hpos hcard ha hmin
  obtain ⟨hl, hleast⟩ := first_isolation_of_fixed (n := 4) hpos ha 3 hfix
  exact ⟨hl, hleast, hlt⟩

end TerminationFour

#print axioms TerminationFour.return_lemma
#print axioms TerminationFour.four_stops_within_three_moves
#print axioms TerminationFour.four_first_isolation

/-! ## v4 — every `n`: a capped chain stops; the growth of one move; the growth a return needs

At `n = 5` the chain has no fixed length (137 moves observed), so termination cannot come from counting moves as at
`n = 3, 4`.  These three lemmas hold at every `n` and split the problem:

* `exists_fixed_of_capped` — if every iterate stays at or below a time `U`, some iterate is fixed (the iterates are
  openings below `U`, and there are finitely many).  Termination is reduced to a cap.
* `move_growth` — a move set at lap `Q ≥ 1` from `t` lands before `(Q + 1/n)/(Q − 1/n) · t`.
* `return_growth` — a runner that left at its lap-`P` opening `t` is in the way at `t' > t` only if
  `t' > (P + 1 − 1/n)/(P + 1/n) · t`.

Together: a runner returns after `m` intervening moves (laps `Q₁ … Q_m`) only if
`∏ (nQⱼ + 1)/(nQⱼ − 1) > (nP + n − 1)/(nP + 1)`; the one-move case is `return_lemma`, and the nearest runner (`P = 0`)
needs the product to exceed `n − 1`. -/

namespace ChainBounds

open ConstructionN MomentIterationN TerminationFour

/-- Every iterate from `b` below a cap `U` is `b` or an opening at or before `U`. -/
theorem iterate_mem_openings_of_capped {n : ℕ} [Fact (2 ≤ n)] {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d)
    {b U : ℝ} (hb : 0 < b) (hcap : ∀ N : ℕ, (move n ds)^[N] b ≤ U) :
    ∀ N : ℕ, (move n ds)^[N] b ∈ insert b (openingsUpTo n ds U) := by
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
      have hmove_le : move n ds x ≤ U := by
        have := hcap (N + 1); rwa [Function.iterate_succ_apply'] at this
      have hxb : b ≤ x := iterate_ge ds b N
      have hgt : x < move n ds x := by rw [he]; exact lt_nextOpening hdpos hw
      rw [hval] at hmove_le hgt
      have hn0 : (0 : ℝ) < n := n_pos
      have hk_up : (k : ℝ) ≤ d * U := by
        rw [div_le_iff₀ hdpos] at hmove_le
        have : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn0
        nlinarith
      have hk_lo : (0 : ℝ) < (k : ℝ) + (n : ℝ)⁻¹ := by
        have : 0 < ((k : ℝ) + (n : ℝ)⁻¹) / d := lt_trans (lt_of_lt_of_le hb hxb) hgt
        exact (div_pos_iff_of_pos_right hdpos).mp this
      have hk0 : (0 : ℤ) ≤ k := by
        by_contra hc
        push Not at hc
        have hk1 : k ≤ -1 := by omega
        have : (k : ℝ) ≤ -1 := by exact_mod_cast hk1
        have : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
        linarith
      have hkc : k ≤ ⌈d * U⌉ := by
        have := Int.le_ceil (d * U)
        exact_mod_cast le_trans hk_up this
      rw [hval]
      refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_image.mpr ⟨k, ?_, rfl⟩⟩)
      exact Finset.mem_Icc.mpr ⟨hk0, hkc⟩

/-- **A capped chain stops.**  If every iterate of the move from a positive start stays at or below `U`, some iterate
is fixed. -/
theorem exists_fixed_of_capped {n : ℕ} [Fact (2 ≤ n)] {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d)
    {b U : ℝ} (hb : 0 < b) (hcap : ∀ N : ℕ, (move n ds)^[N] b ≤ U) :
    ∃ N : ℕ, move n ds ((move n ds)^[N] b) = (move n ds)^[N] b := by
  classical
  by_contra hne
  push Not at hne
  have hsm : StrictMono (fun N : ℕ => (move n ds)^[N] b) := by
    refine strictMono_nat_of_lt_succ (fun N => ?_)
    show (move n ds)^[N] b < (move n ds)^[N + 1] b
    rw [Function.iterate_succ_apply']
    exact lt_of_le_of_ne (le_move ds _) (fun h => hne N h.symm)
  let T : Finset ℝ := insert b (openingsUpTo n ds U)
  let g : ℕ → T := fun N => ⟨(move n ds)^[N] b, iterate_mem_openings_of_capped hpos hb hcap N⟩
  have hg : Function.Injective g := by
    intro i j hij
    exact hsm.injective (congrArg Subtype.val hij)
  exact not_injective_infinite_finite g hg

/-- **Growth of one move.**  If `x` is within `1/n` of lap `Q ≥ 1` at `t > 0`, its opening `(Q + 1/n)/x` is before
`(Q + 1/n)/(Q − 1/n) · t`. -/
theorem move_growth {n : ℕ} [Fact (2 ≤ n)] {x t : ℝ} (hx : 0 < x) (ht : 0 < t) {Q : ℤ} (hQ : 1 ≤ Q)
    (hk : |x * t - Q| < (n : ℝ)⁻¹) :
    ((Q : ℝ) + (n : ℝ)⁻¹) / x < ((Q : ℝ) + (n : ℝ)⁻¹) / ((Q : ℝ) - (n : ℝ)⁻¹) * t := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hh : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hh0 : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn0
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQh : 0 < (Q : ℝ) - (n : ℝ)⁻¹ := by linarith
  have hxt : (Q : ℝ) - (n : ℝ)⁻¹ < x * t := by have := (abs_lt.mp hk).1; linarith
  rw [div_mul_eq_mul_div, div_lt_div_iff₀ hx hQh]
  have hQp : 0 < (Q : ℝ) + (n : ℝ)⁻¹ := by linarith
  nlinarith [mul_lt_mul_of_pos_left hxt hQp]

/-- **Growth a return needs.**  If `x` left at its lap-`P` opening `t = (P + 1/n)/x` and is in the way at `t' > t`, then
`t' > (P + 1 − 1/n)/(P + 1/n) · t`. -/
theorem return_growth {n : ℕ} [Fact (2 ≤ n)] {x t t' : ℝ} (hx : 0 < x) {P : ℤ} (hP : 0 ≤ P)
    (ht : t = ((P : ℝ) + (n : ℝ)⁻¹) / x) (hlt : t < t') (hw : inWay n x t') :
    ((P : ℝ) + 1 - (n : ℝ)⁻¹) / ((P : ℝ) + (n : ℝ)⁻¹) * t < t' := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hh0 : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn0
  have hPr : (0 : ℝ) ≤ P := by exact_mod_cast hP
  have hPh : 0 < (P : ℝ) + (n : ℝ)⁻¹ := by linarith
  obtain ⟨k, hk⟩ := exists_near_int hw
  have hk' := abs_lt.mp hk
  have hxt : (P : ℝ) + (n : ℝ)⁻¹ < x * t' := by
    have e : x * t = (P : ℝ) + (n : ℝ)⁻¹ := by rw [ht]; field_simp
    rw [← e]; exact mul_lt_mul_of_pos_left hlt hx
  have hkP : (P : ℝ) + 1 ≤ k := by
    have : (P : ℝ) < k := by linarith
    have : P < k := by exact_mod_cast this
    exact_mod_cast (show P + 1 ≤ k by omega)
  have hlow : (P : ℝ) + 1 - (n : ℝ)⁻¹ < x * t' := by linarith
  rw [ht, div_mul_div_comm, div_lt_iff₀ (mul_pos hPh hx)]
  have m := mul_lt_mul_of_pos_left hlow hPh
  linear_combination m

end ChainBounds

#print axioms ChainBounds.exists_fixed_of_capped
#print axioms ChainBounds.move_growth
#print axioms ChainBounds.return_growth

/-! ## v5 — word rules for the setter sequence, every `n ≥ 4`

* `no_return_after_faster` (W1) — a runner is never in the way straight after a move set by a runner at least as fast
  as itself.  So `x y x` needs `y` slower than `x`.
* `no_four_alternation` (W2) — two runners cannot set four consecutive moves `y z y z`.

At `n = 5` with the nearest runner clear and the others `b < c < d` by speed, W1 forbids `bcb`, `bdb`, `cdc`: the settings
of `b` are separated by `cd`, `dc` or `dcd`, each containing exactly one `c`. -/

namespace WordRules

open ConstructionN MomentIterationN TerminationFour

/-- **W1.**  `x` sits at its lap-`P` opening `t`; `y`, at least as fast, is in the way at `t` near lap `Q` and sets the
move to its opening `t' > t`.  Then `x` is not in the way at `t'` (for `n ≥ 4`). -/
theorem no_return_after_faster {n : ℕ} [Fact (2 ≤ n)] (hn4 : 4 ≤ n) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    {P Q : ℤ} (hP : 0 ≤ P)
    (hyQ : |y * (((P : ℝ) + (n : ℝ)⁻¹) / x) - Q| < (n : ℝ)⁻¹)
    (hlater : ((P : ℝ) + (n : ℝ)⁻¹) / x < ((Q : ℝ) + (n : ℝ)⁻¹) / y) :
    ¬ inWay n x (((Q : ℝ) + (n : ℝ)⁻¹) / y) := by
  intro hret
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hlem := return_lemma hx hy hP hyQ hlater hret
  have hn0 : (0 : ℝ) < n := n_pos
  have hh0 : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn0
  have hPr : (0 : ℝ) ≤ P := by exact_mod_cast hP
  -- `y t ≥ x t = P + 1/n`, so `Q > P`
  have hxt : x * (((P : ℝ) + (n : ℝ)⁻¹) / x) = P + (n : ℝ)⁻¹ := by field_simp
  have hyt : (P : ℝ) + (n : ℝ)⁻¹ ≤ y * (((P : ℝ) + (n : ℝ)⁻¹) / x) := by
    have hm := mul_le_mul_of_nonneg_right hxy (div_pos (by linarith : (0 : ℝ) < P + (n : ℝ)⁻¹) hx).le
    linarith
  have hQ : (P : ℝ) < Q := by have := (abs_lt.mp hyQ).2; linarith
  have hQ' : P < Q := by exact_mod_cast hQ
  have hn4' : (4 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn4
  nlinarith

/-- **W2.**  Moves `y` (lap `P`, opening `t₁`), `z` (lap `Q`, opening `t₂`), `y` (lap `P'`, opening `t₃`): if `z` is in the way
at `t₃`, contradiction (for `n ≥ 4`). -/
theorem no_four_alternation {n : ℕ} [Fact (2 ≤ n)] (hn4 : 4 ≤ n) {y z : ℝ} (hy : 0 < y) (hz : 0 < z)
    {P Q P' : ℤ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (h1 : |z * (((P : ℝ) + (n : ℝ)⁻¹) / y) - Q| < (n : ℝ)⁻¹)
    (h12 : ((P : ℝ) + (n : ℝ)⁻¹) / y < ((Q : ℝ) + (n : ℝ)⁻¹) / z)
    (h2 : |y * (((Q : ℝ) + (n : ℝ)⁻¹) / z) - P'| < (n : ℝ)⁻¹)
    (h23 : ((Q : ℝ) + (n : ℝ)⁻¹) / z < ((P' : ℝ) + (n : ℝ)⁻¹) / y)
    (h3 : inWay n z (((P' : ℝ) + (n : ℝ)⁻¹) / y)) : False := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hh0 : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn0
  -- `y` returns at `t₂`, so the first return condition holds, and `P' > P`
  have hyret : inWay n y (((Q : ℝ) + (n : ℝ)⁻¹) / z) := inWay_of_near h2
  have r1 := return_lemma hy hz hP h1 h12 hyret
  have r2 := return_lemma hz hy hQ h2 h23 h3
  have hyt1 : y * (((P : ℝ) + (n : ℝ)⁻¹) / y) = P + (n : ℝ)⁻¹ := by field_simp
  have hyt2 : (P : ℝ) + (n : ℝ)⁻¹ < y * (((Q : ℝ) + (n : ℝ)⁻¹) / z) := by
    rw [← hyt1]; exact mul_lt_mul_of_pos_left h12 hy
  have hPP : (P : ℝ) < P' := by have := (abs_lt.mp h2).2; linarith
  have hPP' : P < P' := by exact_mod_cast hPP
  have hn4' : (4 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn4
  nlinarith

end WordRules

#print axioms WordRules.no_return_after_faster
#print axioms WordRules.no_four_alternation

/-! ## v6 — every `n`: a setter repeats within `n − 1` moves; the nearest runner's reading as the chain state

* `setter_repeat` (abstract pigeonhole) — `k + 1` setters drawn from a set of size `≤ k` include two equal ones.
* `nearest_clear_general` — while `1/n ≤ m·t ≤ 1 − 1/n`, the runner at `m` is not in the way.
* `repeat_within` — with `card ds ≤ n − 1`, nearest `m` clear at `n − 1` consecutive moving iterates: some other runner
  sets two of those moves.
* `nearest_reading_recurrence` — along the iteration from `1/(n·m)` (`m` the nearest difference), `m·t_N ≤ (1/n)·∏ F(Q_j)`
  where `Q_j ≥ 1` is the lap of the setter of move `j` (or `1` if the move stays) and `F(Q) = (Q + 1/n)/(Q − 1/n)`.
* `nearest_return_needs_product` — if the nearest runner is in the way at iterate `N`, that product exceeds `n − 1`. -/

namespace NearestState

open ConstructionN MomentIterationN TerminationFour ChainBounds

/-- **Abstract pigeonhole.**  `k + 1` values in a set of size at most `k` include two equal ones at positions `i < j`. -/
theorem setter_repeat {α : Type*} [DecidableEq α] {S : Finset α} {k : ℕ} (hS : S.card ≤ k)
    (s : Fin (k + 1) → α) (hs : ∀ i, s i ∈ S) : ∃ i j : Fin (k + 1), i < j ∧ s i = s j := by
  have hlt : S.card < (Finset.univ : Finset (Fin (k + 1))).card := by simp; omega
  obtain ⟨i, -, j, -, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt (fun i _ => hs i)
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨i, j, h, heq⟩
  · exact ⟨j, i, h, heq.symm⟩

/-- While `1/n ≤ m·t ≤ 1 − 1/n`, the runner at difference `m` is clear. -/
theorem nearest_clear_general {n : ℕ} [Fact (2 ≤ n)] {m t : ℝ} (h1 : (n : ℝ)⁻¹ ≤ m * t)
    (h2 : m * t ≤ 1 - (n : ℝ)⁻¹) : ¬ inWay n m t := by
  intro hw
  unfold inWay circDist at hw
  have hn : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hf : Int.fract (m * t) = m * t := by
    rw [Int.fract_eq_self]; constructor <;> linarith [inv_pos.mpr (n_pos (n := n))]
  rw [hf] at hw
  rcases min_lt_iff.mp hw with h | h <;> linarith

/-- **A setter repeats within `n − 1` moves.** -/
theorem repeat_within {n : ℕ} [Fact (2 ≤ n)] {ds : Finset ℝ} (hcard : ds.card ≤ n - 1) {m : ℝ} (hm : m ∈ ds)
    (ts : Fin (n - 1) → ℝ) (hmove : ∀ j, move n ds (ts j) ≠ ts j)
    (hclear : ∀ j, (n : ℝ)⁻¹ ≤ m * ts j ∧ m * ts j ≤ 1 - (n : ℝ)⁻¹) :
    ∃ j k : Fin (n - 1), j < k ∧ ∃ x ∈ ds, x ≠ m ∧
      inWay n x (ts j) ∧ move n ds (ts j) = nextOpening n x (ts j) ∧
      inWay n x (ts k) ∧ move n ds (ts k) = nextOpening n x (ts k) := by
  classical
  have hn2 : 2 ≤ n := Fact.out
  have hex : ∀ j, ∃ x ∈ ds, inWay n x (ts j) ∧ move n ds (ts j) = nextOpening n x (ts j) := by
    intro j
    rcases move_eq_self_or_opening (n := n) ds (ts j) with h | h
    · exact absurd h (hmove j)
    · exact h
  choose s hsd hsw hse using hex
  have hne : ∀ j, s j ≠ m := by
    intro j h
    exact nearest_clear_general (hclear j).1 (hclear j).2 (h ▸ hsw j)
  have hlt : (ds.erase m).card < (Finset.univ : Finset (Fin (n - 1))).card := by
    rw [Finset.card_erase_of_mem hm, Finset.card_univ, Fintype.card_fin]; omega
  obtain ⟨i, -, j, -, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt
    (fun i _ => Finset.mem_erase.mpr ⟨hne i, hsd i⟩)
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨i, j, h, s i, hsd i, hne i, hsw i, hse i, heq ▸ hsw j, heq ▸ hse j⟩
  · exact ⟨j, i, h, s j, hsd j, hne j, hsw j, hse j, heq.symm ▸ hsw i, heq.symm ▸ hse i⟩

/-- **The nearest runner's reading as the chain state.**  Along the iteration from `1/(n·m)`, with `m` the nearest
difference: there are laps `Q_j ≥ 1`, each the lap of the setter of move `j` (or the move stays), such that
`m·t_N ≤ (1/n)·∏_{j<N} (Q_j + 1/n)/(Q_j − 1/n)`. -/
theorem nearest_reading_recurrence {n : ℕ} [Fact (2 ≤ n)] {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d)
    {m : ℝ} (hm : m ∈ ds) (hmin : ∀ d ∈ ds, m ≤ d) (N : ℕ) :
    ∃ Q : ℕ → ℤ,
      (∀ j < N, 1 ≤ Q j ∧
        ((move n ds)^[j + 1] (1 / (n * m)) = (move n ds)^[j] (1 / (n * m)) ∨
          ∃ x ∈ ds, |x * (move n ds)^[j] (1 / (n * m)) - Q j| < (n : ℝ)⁻¹ ∧
            (move n ds)^[j + 1] (1 / (n * m)) = ((Q j : ℝ) + (n : ℝ)⁻¹) / x)) ∧
      m * (move n ds)^[N] (1 / (n * m)) ≤
        (n : ℝ)⁻¹ * ∏ j ∈ Finset.range N, (((Q j : ℝ) + (n : ℝ)⁻¹) / ((Q j : ℝ) - (n : ℝ)⁻¹)) := by
  have hm0 := hpos m hm
  have hn0 : (0 : ℝ) < n := n_pos
  have hh0 : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn0
  have hhle : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  set b := 1 / (n * m) with hb
  have hmb : m * b = (n : ℝ)⁻¹ := by rw [hb]; field_simp
  have hb0 : 0 < b := by rw [hb]; positivity
  have Fpos : ∀ q : ℤ, 1 ≤ q → 1 ≤ ((q : ℝ) + (n : ℝ)⁻¹) / ((q : ℝ) - (n : ℝ)⁻¹) := by
    intro q hq
    have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
    rw [le_div_iff₀ (by linarith)]; linarith
  induction N with
  | zero => exact ⟨fun _ => 1, fun j hj => absurd hj (Nat.not_lt_zero _), by simp [hmb]⟩
  | succ N ih =>
    obtain ⟨Q, hQ, hbound⟩ := ih
    set tN := (move n ds)^[N] b with htN
    have htNb : b ≤ tN := iterate_ge ds b N
    have hmtN : (n : ℝ)⁻¹ ≤ m * tN := by rw [← hmb]; exact mul_le_mul_of_nonneg_left htNb hm0.le
    have hprod0 : 0 ≤ ∏ j ∈ Finset.range N, (((Q j : ℝ) + (n : ℝ)⁻¹) / ((Q j : ℝ) - (n : ℝ)⁻¹)) :=
      Finset.prod_nonneg (fun j hj => le_trans zero_le_one (Fpos _ (hQ j (Finset.mem_range.mp hj)).1))
    have hsucc : (move n ds)^[N + 1] b = move n ds tN := Function.iterate_succ_apply' _ _ _
    rcases step_cases (n := n) hpos tN with hfix | ⟨x, hx, k, hk, he⟩
    · -- the move stays: use lap 1
      refine ⟨Function.update Q N 1, ?_, ?_⟩
      · intro j hj
        by_cases hjN : j = N
        · subst hjN; rw [Function.update_self]; exact ⟨le_refl _, Or.inl (by rw [hsucc, hfix])⟩
        · rw [Function.update_of_ne hjN]; exact hQ j (by omega)
      · rw [Finset.prod_range_succ, Function.update_self, hsucc, hfix]
        rw [Finset.prod_congr rfl (fun j hj => by
          rw [Function.update_of_ne (by have := Finset.mem_range.mp hj; omega)])]
        have := Fpos 1 le_rfl
        push_cast at this ⊢
        nlinarith
    · have hx0 := hpos x hx
      have hkpos : 1 ≤ k := by
        have hxt : m * tN ≤ x * tN := mul_le_mul_of_nonneg_right (hmin x hx) (le_trans hb0.le htNb)
        have := (abs_lt.mp hk).2
        have : (0 : ℝ) < k := by linarith
        have : (0 : ℤ) < k := by exact_mod_cast this
        omega
      refine ⟨Function.update Q N k, ?_, ?_⟩
      · intro j hj
        by_cases hjN : j = N
        · subst hjN; rw [Function.update_self]; exact ⟨hkpos, Or.inr ⟨x, hx, hk, by rw [hsucc, he]⟩⟩
        · rw [Function.update_of_ne hjN]; exact hQ j (by omega)
      · rw [Finset.prod_range_succ, Function.update_self, hsucc, he]
        rw [Finset.prod_congr rfl (fun j hj => by
          rw [Function.update_of_ne (by have := Finset.mem_range.mp hj; omega)])]
        have hg := move_growth hx0 (lt_of_lt_of_le hb0 htNb) hkpos hk
        have hmg := mul_lt_mul_of_pos_left hg hm0
        have hF := Fpos k hkpos
        set P := ∏ j ∈ Finset.range N, (((Q j : ℝ) + (n : ℝ)⁻¹) / ((Q j : ℝ) - (n : ℝ)⁻¹))
        set Fk := ((k : ℝ) + (n : ℝ)⁻¹) / ((k : ℝ) - (n : ℝ)⁻¹)
        have e1 : m * (Fk * tN) = Fk * (m * tN) := by ring
        have h3 : Fk * (m * tN) ≤ Fk * ((n : ℝ)⁻¹ * P) := mul_le_mul_of_nonneg_left hbound (by linarith)
        have e2 : Fk * ((n : ℝ)⁻¹ * P) = (n : ℝ)⁻¹ * (P * Fk) := by ring
        linarith

/-- **The two accounts meet.**  If the nearest runner is in the way at iterate `N`, the setter-lap product exceeds
`n − 1`. -/
theorem nearest_return_needs_product {n : ℕ} [Fact (2 ≤ n)] {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d)
    {m : ℝ} (hm : m ∈ ds) (hmin : ∀ d ∈ ds, m ≤ d) (N : ℕ)
    (hw : inWay n m ((move n ds)^[N] (1 / (n * m)))) :
    ∃ Q : ℕ → ℤ,
      (∀ j < N, 1 ≤ Q j ∧
        ((move n ds)^[j + 1] (1 / (n * m)) = (move n ds)^[j] (1 / (n * m)) ∨
          ∃ x ∈ ds, |x * (move n ds)^[j] (1 / (n * m)) - Q j| < (n : ℝ)⁻¹ ∧
            (move n ds)^[j + 1] (1 / (n * m)) = ((Q j : ℝ) + (n : ℝ)⁻¹) / x)) ∧
      (n : ℝ) - 1 < ∏ j ∈ Finset.range N, (((Q j : ℝ) + (n : ℝ)⁻¹) / ((Q j : ℝ) - (n : ℝ)⁻¹)) := by
  obtain ⟨Q, hQ, hbound⟩ := nearest_reading_recurrence (n := n) hpos hm hmin N
  refine ⟨Q, hQ, ?_⟩
  have hm0 := hpos m hm
  have hn0 : (0 : ℝ) < n := n_pos
  have hh0 : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn0
  set b := 1 / (n * m) with hb
  have hbeq : b = ((0 : ℤ) + (n : ℝ)⁻¹) / m := by
    rw [hb, Int.cast_zero, zero_add]; field_simp
  have hlt : b < (move n ds)^[N] b := by
    rcases lt_or_eq_of_le (iterate_ge (n := n) ds b N) with h | h
    · exact h
    · exfalso; rw [← h, hbeq] at hw
      exact not_inWay_at_own_opening (n := n) hm0 0 hw
  have hr := return_growth hm0 le_rfl hbeq hlt hw
  have hmb : m * b = (n : ℝ)⁻¹ := by rw [hb]; field_simp
  have hnn : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hn0.ne'
  -- `m·t_N > (n − 1)·(1/n)`
  have hq : ((0 : ℤ) + 1 - (n : ℝ)⁻¹) / ((0 : ℤ) + (n : ℝ)⁻¹) = (n : ℝ) - 1 := by
    rw [Int.cast_zero, zero_add, zero_add]; field_simp
  rw [hq] at hr
  have h1 : ((n : ℝ) - 1) * (n : ℝ)⁻¹ < m * (move n ds)^[N] b := by
    have := mul_lt_mul_of_pos_left hr hm0
    have e : m * (((n : ℝ) - 1) * b) = ((n : ℝ) - 1) * (m * b) := by ring
    rw [e, hmb] at this; exact this
  have h2 := lt_of_lt_of_le h1 hbound
  have h3 : (n : ℝ)⁻¹ * ((n : ℝ) - 1) < (n : ℝ)⁻¹ * ∏ j ∈ Finset.range N,
      (((Q j : ℝ) + (n : ℝ)⁻¹) / ((Q j : ℝ) - (n : ℝ)⁻¹)) := by linarith
  exact lt_of_mul_lt_mul_left h3 hh0.le

end NearestState

#print axioms NearestState.setter_repeat
#print axioms NearestState.repeat_within
#print axioms NearestState.nearest_reading_recurrence
#print axioms NearestState.nearest_return_needs_product
