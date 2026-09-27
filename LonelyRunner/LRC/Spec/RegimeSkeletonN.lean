import LonelyRunner.LRC.Spec.SlowestSkeletonN
import LonelyRunner.LRC.Spec.TwoBlockN

/-!
# The regime skeleton: every proved regime feeds the target; the gap is two named coverings

2026-09-28.  Running record: `RUNNING_LOG_order8_v1.md` E156–E158.

`SlowestSkeletonN.lonelyRunnerAt8_of_cases T` reduces the conjecture at eight runners to `CaseB8 T` and `CaseC8 T`
(Case A, spread at most 7, is R1 and proved there).  This module states what the arrangement's own structure gives in each
case as **regimes**, each a condition on the readings that is **proved sufficient** for loneliness, and names the one
statement still owed in each case: that every set of the case satisfies some regime (`CoverB8`, `CoverC8`, both
registered OWED in `scripts/nN/spec_gate.sh`).

The regimes (readings `S`, least reading `m`):
* `BoundClear8 S m`: every reading clear at the bound `1/(8m)` (the AP at the nearest runner's scale).
* `GridClass8 S e mm c`: the grid through reading `e` at scale `e/mm`, class `c`: every reading `d` sits at a grid point
  `n` with `|n·e − mm·d| < e` (the floor or the ceiling of `mm·d/e`), on lap `⌊c·n/8⌋` (one lap less when `c·n ≡ 0 mod 8`),
  and these laps are pairwise compatible.  Sufficient by `TwoBlock.lonely_eight_of_pairwise_laps` (1-D Helly).  The lap
  assignment is fixed by `S` up to finitely many choices, so the regime is a restriction, not loneliness renamed.  The
  owner's "AP/grid plus a deviation": the grid is the arrangement's own, at `1/mm` of one of its readings.
* `WithinTwoBlocks8 S m`: lonely at some instant inside the nearest runner's first two clear blocks (`t ≤ 15/(8m)`).
  Used only in Case C, for a captured middle reading released by its own exit and a few fast nudges (E157).  **A
  placeholder**: those sets are two runners in one slot (the captured runner shares the subject's slot at every grid
  instant) and the isolation waits for them to separate, the captured runner's exit.  That is the same event as the near
  pair, the grid nudge, the doubled edge and the late band's carry to `R = 9`, and it is exactly one move of the cascade
  (owner, E158).  The separation regime belongs here once it is stated.

The coverings, and what has been checked (exact, `LonelyRunner/experiments/nN/redo/`):
* `CoverB8`: every set with spread in `(7, 24]` is in `BoundClear8` or a `GridClass8` with `mm ≤ 4`, `c ∈ {1,3,5,7}`.
  Checked on all 210,335 sets with readings `≤ 24`: least `mm` 1/2/3/4 for 201,698/8,422/210/5, none uncovered
  (`grid_class_caseB_c7_v1.out`, E132).  Not proved.
* `CoverC8`: every set with spread above 24 is in `BoundClear8`, a `GridClass8` with `mm ≤ 8`, `c ∈ {1,3,5,7}`, or
  `WithinTwoBlocks8`.  Checked: all 635,334 sets with least reading 1 and readings `≤ 32` by `GridClass8` with `mm ≤ 4`;
  19,610 of 19,625 random wide sets by `GridClass8` (`mm ≤ 7`), the other 15 captures released at `R ≤ 1.09`, inside
  `WithinTwoBlocks8`; the 547 constructed residual Case C members by `GridClass8` (`mm ≤ 5`)
  (`casec_gridclass_v1.out`, `casec_leftover_cascade_v1.out`, E157).  Not proved; the infinite range is the open part.

`lonelyRunnerAt8_of_covers : CoverB8 → CoverC8 → LonelyRunnerAt8`.

Everything here is proved; no `sorry`, no `native_decide`.  The two coverings are hypotheses, not theorems.
-/

namespace LRC.RegimeSkeleton

open LRC.Order8Skeleton LRC.SlowestSkeleton

/-- **Bound regime.**  Every reading is clear at the bound `1/(8m)`. -/
def BoundClear8 (S : Finset ℕ) (m : ℕ) : Prop :=
  ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * (1 / (8 * m)))

/-- **Grid-class regime.**  The grid through reading `e` at scale `e/mm`, class `c`: each reading `d` at a grid point `n`
with `|n·e − mm·d| < e`, on lap `⌊c·n/8⌋` (or one less when `c·n ≡ 0 mod 8`), the laps pairwise compatible. -/
def GridClass8 (S : Finset ℕ) (e mm c : ℕ) : Prop :=
  ∃ k : ℕ → ℕ,
    (∀ d ∈ S, ∃ n : ℕ, 1 ≤ n ∧ n * e < mm * d + e ∧ mm * d < n * e + e ∧
      (k d = c * n / 8 ∨ (c * n % 8 = 0 ∧ k d + 1 = c * n / 8))) ∧
    ∀ d ∈ S, ∀ d' ∈ S, (8 * k d + 1) * d' ≤ (8 * k d' + 7) * d

/-- **Window regime (Case C only).**  Lonely inside the nearest runner's first two clear blocks. -/
def WithinTwoBlocks8 (S : Finset ℕ) (m : ℕ) : Prop :=
  ∃ t : ℝ, 1 / (8 * (m : ℝ)) ≤ t ∧ t ≤ 15 / (8 * (m : ℝ)) ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t)

/-- The regimes of Case B. -/
def RegimeB8 (S : Finset ℕ) (m : ℕ) : Prop :=
  BoundClear8 S m ∨
    ∃ e ∈ S, ∃ mm c : ℕ, 1 ≤ mm ∧ mm ≤ 4 ∧ (c = 1 ∨ c = 3 ∨ c = 5 ∨ c = 7) ∧ GridClass8 S e mm c

/-- The regimes of Case C. -/
def RegimeC8 (S : Finset ℕ) (m : ℕ) : Prop :=
  BoundClear8 S m ∨
    (∃ e ∈ S, ∃ mm c : ℕ, 1 ≤ mm ∧ mm ≤ 8 ∧ (c = 1 ∨ c = 3 ∨ c = 5 ∨ c = 7) ∧ GridClass8 S e mm c) ∨
    WithinTwoBlocks8 S m

/-- **OWED: the Case B covering.**  Every set of whole-number readings with spread in `(7, 24]` is in a Case B regime. -/
def CoverB8 : Prop :=
  ∀ S : Finset ℕ, (∀ d ∈ S, 0 < d) → ∀ m ∈ S, (∀ d ∈ S, m ≤ d) → (∃ d ∈ S, 7 * m < d) →
    (∀ d ∈ S, d ≤ 24 * m) → RegimeB8 S m

/-- **OWED: the Case C covering.**  Every set of whole-number readings with spread above 24 is in a Case C regime. -/
def CoverC8 : Prop :=
  ∀ S : Finset ℕ, (∀ d ∈ S, 0 < d) → ∀ m ∈ S, (∀ d ∈ S, m ≤ d) → (∃ d ∈ S, 24 * m < d) → RegimeC8 S m

/-- The bound regime is sufficient. -/
theorem lonely_of_boundClear8 {S : Finset ℕ} {m : ℕ} (hm : 0 < m) (h : BoundClear8 S m) : Lonely8 S := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  exact ⟨1 / (8 * m), by positivity, h⟩

/-- The grid-class regime is sufficient (1-D Helly on its lap assignment). -/
theorem lonely_of_gridClass8 {S : Finset ℕ} (hS : S.Nonempty) (hpos : ∀ d ∈ S, 0 < d) {e mm c : ℕ}
    (h : GridClass8 S e mm c) : Lonely8 S := by
  obtain ⟨k, -, hpair⟩ := h
  exact LRC.TwoBlock.lonely_eight_of_pairwise_laps hS hpos k hpair

/-- The window regime is sufficient. -/
theorem lonely_of_withinTwoBlocks8 {S : Finset ℕ} {m : ℕ} (hm : 0 < m) (h : WithinTwoBlocks8 S m) : Lonely8 S := by
  obtain ⟨t, h1, -, h⟩ := h
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have : (0 : ℝ) < 1 / (8 * (m : ℝ)) := by positivity
  exact ⟨t, lt_of_lt_of_le this h1, h⟩

/-- Every Case B regime is sufficient. -/
theorem lonely_of_regimeB8 {S : Finset ℕ} {m : ℕ} (hS : S.Nonempty) (hpos : ∀ d ∈ S, 0 < d) (hm : 0 < m)
    (h : RegimeB8 S m) : Lonely8 S := by
  rcases h with h | ⟨e, -, mm, c, -, -, -, hg⟩
  · exact lonely_of_boundClear8 hm h
  · exact lonely_of_gridClass8 hS hpos hg

/-- Every Case C regime is sufficient. -/
theorem lonely_of_regimeC8 {S : Finset ℕ} {m : ℕ} (hS : S.Nonempty) (hpos : ∀ d ∈ S, 0 < d) (hm : 0 < m)
    (h : RegimeC8 S m) : Lonely8 S := by
  rcases h with h | ⟨e, -, mm, c, -, -, -, hg⟩ | h
  · exact lonely_of_boundClear8 hm h
  · exact lonely_of_gridClass8 hS hpos hg
  · exact lonely_of_withinTwoBlocks8 hm h

/-- **Case B from its covering.** -/
theorem caseB8_of_cover (h : CoverB8) : CaseB8 24 := by
  intro v hv _ m hm hmin hsp hT
  have hpos := readingsOf_pos hv 0
  exact lonely_of_regimeB8 (readingsOf_nonempty v 0) hpos (hpos m hm) (h _ hpos m hm hmin hsp hT)

/-- **Case C from its covering.** -/
theorem caseC8_of_cover (h : CoverC8) : CaseC8 24 := by
  intro v hv _ m hm hmin hsp
  have hpos := readingsOf_pos hv 0
  exact lonely_of_regimeC8 (readingsOf_nonempty v 0) hpos (hpos m hm) (h _ hpos m hm hmin hsp)

/-- **The conjecture at eight runners from the two coverings.**  Case A is R1 (inside `lonelyRunnerAt8_of_cases`); Case B
and Case C follow from their coverings through the proved regimes. -/
theorem lonelyRunnerAt8_of_covers (hB : CoverB8) (hC : CoverC8) : LRC.Spec.LonelyRunnerAt8 :=
  lonelyRunnerAt8_of_cases 24 (caseB8_of_cover hB) (caseC8_of_cover hC)

end LRC.RegimeSkeleton
