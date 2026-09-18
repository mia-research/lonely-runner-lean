import LonelyRunner.LRC.ConstructionN.Band

/-!
# The cascade (moment iteration) at threshold `1/n`

Part of the cascade artefact (`LRC/Cascade/`).  Real speeds, no runner pinned, every lap.  For a subject with positive
speed differences `ds`:

* `inWay n d t`       — the runner at difference `d` is within `1/n` of the subject at `t`;
* `nextOpening n d t` — the least `(k + 1/n)/d` at or after `t`;
* `move n ds t`       — the largest `nextOpening` over the runners in the way at `t` (or `t` if none).

Proved here, every `n ≥ 2`: soundness and first-ness of a fixed point (`lonely_of_fixed`, `first_isolation_of_fixed`);
the flank at the first isolation time; the move as a change of AP scale (`inWay_at_scale_iff`, `nextOpening_at_scale`);
the first isolation time as the end of the run of lap-completion zones (`first_isolation_as_zone_run`); finiteness
(`lonely_iff_run_ends`); drift lines at the subject's own-AP instants; slot-sharers.
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

/-- **One move clears every runner that was in the way, not only the setter.**  `move` is a fold of
`max` over `ds`, so it reaches at least `nextOpening n d t` for *each* `d` in the way at `t` — the
setter is merely the one attaining the maximum.

So a single exact max-opening step exhausts the current blocking interval of every active runner
simultaneously.  A consequence worth naming: between two successive times the same `d` is in the
way, its lap strictly increases, since the move carries the instant past `d`'s current opening. -/
theorem nextOpening_le_move {ds : Finset ℝ} {d t : ℝ} (hd : d ∈ ds) (hw : inWay n d t) :
    nextOpening n d t ≤ move n ds t := by
  classical
  unfold move
  rw [Finset.le_fold_max]
  refine Or.inr ⟨d, hd, ?_⟩
  simp [hw]

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

/-! ## the flank at the first isolation time

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
theorem flank_at_first_isolation {ι : Type*} [Fintype ι] (w : ι → ℝ)
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

/-! ## the move as a change of AP scale

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

/-! ### the spine pattern  (§6.6)

The manuscript records this as proved arithmetic, checked on 95,776 spine instants, but not formalised.
A runner of slot `a` (a whole number of `n`-ths) and deviation `ε` has reading `a + ε`.  At the spine
instant `r/n` its position reduces to `(c + r·ε)/n` with `c = a·r mod n`, so **the pattern depends only on
the slot and the deviation** — not on the scale it is read at.
-/

/-- **The spine position depends only on slot and deviation.**  At the spine instant `r/n` a reading
`a + ε` sits where `(c + r·ε)/n` sits, with `c = a·r mod n`. -/
theorem spine_reduce (a r : ℤ) (ε : ℝ) :
    circDist (((a : ℝ) + ε) * r / n) = circDist (((((a * r) % n : ℤ) : ℝ) + r * ε) / n) := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hdm : a * r = n * (a * r / n) + (a * r) % n := (Int.mul_ediv_add_emod (a * r) n).symm
  have key : ((a : ℝ) + ε) * r / n
      = ((((a * r) % n : ℤ) : ℝ) + r * ε) / n + (((a * r / n : ℤ)) : ℝ) := by
    have : ((a * r : ℤ) : ℝ) = ((n : ℤ) : ℝ) * ((a * r / n : ℤ) : ℝ) + (((a * r) % n : ℤ) : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hdm
    push_cast at this ⊢
    field_simp
    linarith [this]
  rw [key, circDist_add_int]

/-- **Scaled by `n`, the zone is a band of width 2 around the multiples of `n`.** -/
theorem circDist_div_lt_iff (y : ℝ) :
    circDist (y / n) < (n : ℝ)⁻¹ ↔ ∃ m : ℤ, |y - n * m| < 1 := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hsplit : ∀ m : ℤ, y / n - (m : ℝ) = (y - n * m) / n := by intro m; field_simp
  have hinv : (n : ℝ)⁻¹ * n = 1 := inv_mul_cancel₀ hnn
  constructor
  · intro h
    obtain ⟨m, hm⟩ := circDist_eq_abs_sub_some_int (y / n)
    rw [hm, hsplit, abs_div, abs_of_pos hn0, div_lt_iff₀ hn0, hinv] at h
    exact ⟨m, h⟩
  · rintro ⟨m, hm⟩
    refine lt_of_le_of_lt (circDist_le_abs_sub_int _ m) ?_
    rw [hsplit, abs_div, abs_of_pos hn0, div_lt_iff₀ hn0, hinv]
    exact hm

/-- **In the way at a spine instant**, exactly: the reduced value `c + r·ε` lies within 1 of a multiple
of `n`.  At `n = 8` with `c ∈ [0, 8)` the only multiples in reach are `0` and `8`, which is the
manuscript's `c + r·ε < 1` or `7 < c + r·ε < 9`. -/
theorem spine_inWay_iff (a r : ℤ) (ε : ℝ) :
    inWay n ((a : ℝ) + ε) ((r : ℝ) / n) ↔
      ∃ m : ℤ, |((((a * r) % n : ℤ) : ℝ) + r * ε) - n * m| < 1 := by
  have hmul : ((a : ℝ) + ε) * ((r : ℝ) / n) = ((a : ℝ) + ε) * r / n := by ring
  unfold inWay
  rw [hmul, spine_reduce (n := n) a r ε]
  exact circDist_div_lt_iff (n := n) _

/-! ### the step as one dilation  (§6.2)

The manuscript records these as proved arithmetic but not formalised. With `D' = d_x/(n·N+1)` the scale
the setter hands over, and `λ = D/D'`:

* every reading is multiplied by the same `λ`, and `λ > 1`;
* the setter lands exactly on `n·N + 1`;
* every other reading moves by `g·(d_y/d_x)`, with `g = n·N + 1 − s_x ∈ (0, 2)` the distance the setter
  sat below `n·N + 1`.
-/

/-- The scale a setter in the way at scale `D` hands over. -/
noncomputable def nextScale (n : ℕ) (d : ℝ) (N : ℤ) : ℝ := d / (n * N + 1)

theorem nextScale_pos {d D : ℝ} (hd : 0 < d) (hD : 0 < D) {N : ℤ} (hN : |d / D - n * N| < 1) :
    0 < nextScale n d N := by
  have hs : 0 < d / D := div_pos hd hD
  have := abs_lt.mp hN
  exact div_pos hd (by linarith)

/-- **A step is one dilation.**  Every reading is multiplied by the same factor `λ = D/D'`. -/
theorem reading_at_nextScale {d dx D : ℝ} (hdx : 0 < dx) (hD : 0 < D) {N : ℤ}
    (hN : |dx / D - n * N| < 1) :
    d / nextScale n dx N = (D / nextScale n dx N) * (d / D) := by
  have h0 := nextScale_pos (n := n) hdx hD hN
  field_simp
theorem dilation_factor {dx D : ℝ} (hdx : 0 < dx) (hD : 0 < D) {N : ℤ}
    (hN : |dx / D - n * N| < 1) :
    D / nextScale n dx N = ((n : ℝ) * N + 1) / (dx / D) := by
  have hs : 0 < dx / D := div_pos hdx hD
  have := abs_lt.mp hN
  unfold nextScale
  field_simp

/-- **The factor exceeds 1**: the setter's reading sits strictly below `n·N + 1`. -/
theorem one_lt_dilation_factor {dx D : ℝ} (hdx : 0 < dx) (hD : 0 < D) {N : ℤ}
    (hN : |dx / D - n * N| < 1) : 1 < D / nextScale n dx N := by
  have hs : 0 < dx / D := div_pos hdx hD
  have h := abs_lt.mp hN
  rw [dilation_factor (n := n) hdx hD hN, lt_div_iff₀ hs]
  linarith [h.2]

/-- **The setter lands exactly on `n·N + 1`.** -/
theorem setter_reading_at_nextScale {dx : ℝ} (hdx : 0 < dx) {N : ℤ} (hN0 : (0 : ℝ) < n * N + 1) :
    dx / nextScale n dx N = (n : ℝ) * N + 1 := by
  unfold nextScale; field_simp

/-- **What every other reading moves by.**  `g = n·N + 1 − s_x` is how far the setter sat below
`n·N + 1`, and the shift is `g·(d/d_x)` — a ratio fixed by the speeds. -/
theorem other_reading_shift {d dx D : ℝ} (hdx : 0 < dx) (hD : 0 < D) {N : ℤ}
    (hN : |dx / D - n * N| < 1) :
    d / nextScale n dx N - d / D = ((n : ℝ) * N + 1 - dx / D) * (d / dx) := by
  have hs : 0 < dx / D := div_pos hdx hD
  have := abs_lt.mp hN
  unfold nextScale
  field_simp

/-- **The shift's coefficient lies in `(0, 2)`.** -/
theorem shift_coeff_mem {dx D : ℝ} (hD : 0 < D) {N : ℤ} (hN : |dx / D - n * N| < 1) :
    0 < (n : ℝ) * N + 1 - dx / D ∧ (n : ℝ) * N + 1 - dx / D < 2 := by
  have h := abs_lt.mp hN
  exact ⟨by linarith [h.2], by linarith [h.1]⟩

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

/-! ## the first isolation time as the end of the run of lap-completion zones

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

/-! ## finiteness: a lonely time forces the run to end

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

/-! ## drift lines: the lap zones in the AP-deviation frame

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

/-! ### the own-AP residue rule  (Proposition 6.7)

The manuscript records this as derived and verified on 40,000 runners, but not formalised.  With rational
readings `s = c/κ`, put `h = gcd(c, nκ)`, `m' = nκ/h` and `u = c/h`.  Then being in the way at the own AP
instant `ν` is a condition on `u·ν mod m'` alone — and, cleared of the division, it is an inequality
between whole numbers, so a concrete runner is decided by arithmetic.
-/

/-- **Proposition 6.7, the own-AP residue rule.**  The hypotheses `c = h·u` and `n·κ = h·m'` are what the
common factor `h = gcd(c, nκ)` supplies; the rule needs no more of it than that.  The right-hand side is
an inequality between whole numbers, so a concrete runner is decided by arithmetic. -/
theorem own_ap_residue_rule {m : ℝ} (hm : 0 < m) {c κ h u m' : ℤ}
    (hκ : 0 < κ) (hh : 0 < h) (hc : c = h * u) (hnκ : (n : ℤ) * κ = h * m') (ν : ℤ) :
    inWay n (((c : ℝ) / (κ : ℝ)) * m) ((ν : ℝ) / (n * m)) ↔
      ∃ M : ℤ, (n : ℤ) * |u * ν - m' * M| < m' := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hκ0 : (0 : ℝ) < (κ : ℝ) := by exact_mod_cast hκ
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hnZ : (0 : ℤ) < (n : ℤ) := by have := (Fact.out : 2 ≤ n); omega
  -- the numerator identity, entirely in ℤ
  have hnum : ∀ M : ℤ, c * ν - (n : ℤ) * κ * M = h * (u * ν - m' * M) := by
    intro M; rw [hc, hnκ]; ring
  have hκZ : (n : ℤ) * κ = h * m' := hnκ
  have hm'0 : (0 : ℤ) < m' := by nlinarith [hκ, hh, hnZ, hκZ]
  have hposn : ((c : ℝ) / (κ : ℝ) * m) * ((ν : ℝ) / (n * m)) = ((c : ℝ) * ν / κ) / n := by
    field_simp
  unfold inWay
  rw [hposn, circDist_div_lt_iff (n := n)]
  -- one equivalence, used for both directions
  have key : ∀ M : ℤ, |(c : ℝ) * ν / κ - n * M| < 1 ↔ (n : ℤ) * |u * ν - m' * M| < m' := by
    intro M
    have hR : (c : ℝ) * ν / κ - (n : ℝ) * M = (h : ℝ) * ((u : ℝ) * ν - (m' : ℝ) * M) / (κ : ℝ) := by
      have e := congrArg (fun z : ℤ => (z : ℝ)) (hnum M)
      push_cast at e
      field_simp
      linarith [e]
    rw [hR, abs_div, abs_of_pos hκ0, div_lt_one hκ0, abs_mul, abs_of_pos hh0]
    have habs : |(u : ℝ) * ν - (m' : ℝ) * M| = ((|u * ν - m' * M| : ℤ) : ℝ) := by
      rw [Int.cast_abs]; push_cast; ring_nf
    rw [habs]
    -- `h·|·| < κ`  ↔  `n·|·| < m'`, since `n·κ = h·m'`
    constructor
    · intro hlt
      have h1 : (n : ℝ) * ((h : ℝ) * ((|u * ν - m' * M| : ℤ) : ℝ)) < (n : ℝ) * (κ : ℝ) :=
        by nlinarith [hlt, hn0]
      have h2 : (n : ℝ) * (κ : ℝ) = (h : ℝ) * (m' : ℝ) := by
        have e := congrArg (fun z : ℤ => (z : ℝ)) hκZ; push_cast at e; linarith [e]
      rw [h2] at h1
      have h3 : (n : ℝ) * ((|u * ν - m' * M| : ℤ) : ℝ) < (m' : ℝ) := by nlinarith [h1, hh0]
      exact_mod_cast h3
    · intro hlt
      have h3 : (n : ℝ) * ((|u * ν - m' * M| : ℤ) : ℝ) < (m' : ℝ) := by exact_mod_cast hlt
      have h2 : (n : ℝ) * (κ : ℝ) = (h : ℝ) * (m' : ℝ) := by
        have e := congrArg (fun z : ℤ => (z : ℝ)) hκZ; push_cast at e; linarith [e]
      nlinarith [h3, hh0, hn0, h2]
  exact ⟨fun ⟨M, hM⟩ => ⟨M, (key M).mp hM⟩, fun ⟨M, hM⟩ => ⟨M, (key M).mpr hM⟩⟩

/-- **Proposition 6.7, second clause: `m' = 1` is a slot-sharer.**  It is in the way at *every* own AP
instant, so it never leaves. -/
theorem slot_sharer_of_m'_eq_one {m : ℝ} (hm : 0 < m) {c κ h u : ℤ}
    (hκ : 0 < κ) (hh : 0 < h) (hc : c = h * u) (hnκ : (n : ℤ) * κ = h * 1) (ν : ℤ) :
    inWay n (((c : ℝ) / (κ : ℝ)) * m) ((ν : ℝ) / (n * m)) := by
  rw [own_ap_residue_rule hm hκ hh hc hnκ ν]
  exact ⟨u * ν, by simp⟩

/-- **Proposition 6.7, third clause: an even `m'` with `m' ≤ n` is never in the way at an odd `ν`.**
The coprimality of `u` and `m'` is what the common factor `h = gcd(c, nκ)` supplies. -/
theorem not_inWay_odd_of_m'_even_le {m : ℝ} (hm : 0 < m) {c κ h u m' : ℤ}
    (hκ : 0 < κ) (hh : 0 < h) (hc : c = h * u) (hnκ : (n : ℤ) * κ = h * m')
    (hcop : IsCoprime u m') (heven : (2 : ℤ) ∣ m') (hle : m' ≤ (n : ℤ)) {ν : ℤ} (hodd : ¬ (2 : ℤ) ∣ ν) :
    ¬ inWay n (((c : ℝ) / (κ : ℝ)) * m) ((ν : ℝ) / (n * m)) := by
  rw [own_ap_residue_rule hm hκ hh hc hnκ ν]
  rintro ⟨M, hM⟩
  have hnZ : (0 : ℤ) < (n : ℤ) := by have := (Fact.out : 2 ≤ n); omega
  have hm'0 : (0 : ℤ) < m' := by nlinarith [hκ, hh, hnZ, hnκ]
  -- `n·|·| < m' ≤ n` forces `|·| = 0`, so `m' ∣ u*ν`
  have hzero : u * ν - m' * M = 0 := by
    rcases eq_or_lt_of_le (abs_nonneg (u * ν - m' * M)) with h0 | h0
    · exact abs_eq_zero.mp h0.symm
    · exfalso; nlinarith [hM, h0, hle, hnZ]
  have hdvd : m' ∣ ν * u := ⟨M, by linear_combination hzero⟩
  -- coprime to `u`, so `m' ∣ ν`; `m'` even then makes `ν` even
  have hdvdν : m' ∣ ν := hcop.symm.dvd_of_dvd_mul_right hdvd
  exact hodd (dvd_trans heven hdvdν)

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

/-! ## an exact slot-sharer removes every own-AP instant

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
