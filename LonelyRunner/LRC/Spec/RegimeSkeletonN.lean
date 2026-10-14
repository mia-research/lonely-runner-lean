import LonelyRunner.LRC.Spec.SlowestSkeletonN
import LonelyRunner.LRC.Spec.TwoBlockN

/-!
# The regime skeleton: the conjecture at eight runners from one spread-free covering

2026-09-28.  Running record: `RUNNING_LOG_order8_v1.md` E156–E166.

**The one owed statement is `Cover8 M`** (registered OWED in `scripts/nN/spec_gate.sh`): every set of at most seven whole-number
readings (least reading `m`) is lonely at the bound `1/(8m)`, or at a relocated grid-class instant of a grid through one of
its own readings `e` with step `e/mm ≥ m/M` and a class `c ∈ {1, 3, 5, 7}` (the units mod 8).  **`lonelyRunnerAt8_of_cover8
M : Cover8 M → LonelyRunnerAt8`**, for every `M`, with no case split: sets of spread at most 7 are lonely at the bound (R1).

* `BoundClear8 S m`: every reading clear at the bound (the AP at the nearest runner's scale).
* `GridClass8 S e mm c`: the grid through reading `e` at scale `e/mm`, class `c`: each reading `d` at a grid point `n` with
  `|n·e − mm·d| < e`, on lap `⌊c·n/8⌋` (one less when `c·n ≡ 0 mod 8`), the laps pairwise compatible.  Sufficient by
  `TwoBlock.lonely_eight_of_pairwise_laps` (1-D Helly).  The owner's "AP/grid plus a deviation": the grid is the
  arrangement's own, the lap is free (the grid is infinite), the scale is a reading's own (the AP is scale invariant).
* `GridStep8 S m M`: one of the two, with the grid step at least `m/M` (the reference no finer than a fixed fraction of the
  nearest runner, so the covering is a restriction and not loneliness renamed).

**Measured** `[VERIFIED — these populations; not proved]` (`experiments/nN/redo/cover8_step_v1.out`, E165): `Cover8 2`
holds on all 210,335 Case B sets to readings `≤ 24`; every tenth Case C set with least reading 1 and readings `≤ 32`; the
547 constructed residual Case C members; 24,000 random sets of spread up to 2,000; 10,000 random fine shapes; 5,400 late
band shapes (the only population needing a step below `m`, down to `m/2`).  None uncovered.

**Retired** (E166): the spread split (`SlowestSkeletonN.CaseB8`/`CaseC8` at `T = 24`, from the range of the old
certificates) and its coverings `CoverB8`, `CoverC8`, `RegimeB8`, `RegimeC8`, `WithinTwoBlocks8` (in git history before
this commit).  Owner: *"because of scale invariance and infinite grid the spread of 7–24 is irrelevant."*

Everything here is proved; no `sorry`, no `native_decide`.  `Cover8` is a hypothesis, not a theorem.
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

/-- The bound regime is sufficient. -/
theorem lonely_of_boundClear8 {S : Finset ℕ} {m : ℕ} (hm : 0 < m) (h : BoundClear8 S m) : Lonely8 S := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  exact ⟨1 / (8 * m), by positivity, h⟩

/-- The grid-class regime is sufficient (1-D Helly on its lap assignment). -/
theorem lonely_of_gridClass8 {S : Finset ℕ} (hS : S.Nonempty) (hpos : ∀ d ∈ S, 0 < d) {e mm c : ℕ}
    (h : GridClass8 S e mm c) : Lonely8 S := by
  obtain ⟨k, -, hpair⟩ := h
  exact LRC.TwoBlock.lonely_eight_of_pairwise_laps hS hpos k hpair

/-! ### The spread-free covering (E164–E165) -/

/-- **The grid regime with a step bound.**  Lonely at the bound, or at a grid-class instant of a grid through one of the
arrangement's own readings `e` at step `e/mm` at least `m/M` (`mm·m ≤ M·e`), with a class that is a unit mod 8. -/
def GridStep8 (S : Finset ℕ) (m M : ℕ) : Prop :=
  BoundClear8 S m ∨
    ∃ e ∈ S, ∃ mm c : ℕ, 1 ≤ mm ∧ mm * m ≤ M * e ∧ (c = 1 ∨ c = 3 ∨ c = 5 ∨ c = 7) ∧ GridClass8 S e mm c

/-- **OWED: the spread-free covering.**  Every set of at most seven positive whole-number
readings, least reading `m`, is in `GridStep8 S m M`. The cardinality bound is essential. -/
def Cover8 (M : ℕ) : Prop :=
  ∀ S : Finset ℕ, S.card ≤ 7 → (∀ d ∈ S, 0 < d) →
    ∀ m ∈ S, (∀ d ∈ S, m ≤ d) → GridStep8 S m M

/-- The grid regime with a step bound is sufficient. -/
theorem lonely_of_gridStep8 {S : Finset ℕ} {m M : ℕ} (hS : S.Nonempty) (hpos : ∀ d ∈ S, 0 < d) (hm : 0 < m)
    (h : GridStep8 S m M) : Lonely8 S := by
  rcases h with h | ⟨e, -, mm, c, -, -, -, hg⟩
  · exact lonely_of_boundClear8 hm h
  · exact lonely_of_gridClass8 hS hpos hg

/-- A grid with step at least half the nearest reading puts that reading on lap zero or
one at every permitted class. Thus `GridStep8 S m 2` supplies isolation with nearest reading
`8*m*t` between 1 and 15. This is a consequence of the proposed covering, not a proof of it. -/
theorem gridStep8_two_bounded {S : Finset ℕ} {m : ℕ}
    (hpos : ∀ d ∈ S, 0 < d) (hmS : m ∈ S) (h : GridStep8 S m 2) :
    ∃ t : ℝ, 0 < t ∧ 1 ≤ 8 * m * t ∧ 8 * m * t ≤ 15 ∧
      ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast hpos m hmS
  rcases h with hb | ⟨e, heS, mm, c, _, hstep, hc, k, hgrid, hpair⟩
  · refine ⟨1 / (8 * m), by positivity, ?_, ?_, hb⟩ <;>
      field_simp <;> nlinarith
  · obtain ⟨n, _, hn, _, hkm⟩ := hgrid m hmS
    have he : 0 < e := hpos e heS
    have hn2 : n ≤ 2 := by nlinarith
    have hk : k m ≤ 1 := by
      rcases hc with rfl | rfl | rfl | rfl <;> omega
    obtain ⟨t, ht, hblocks⟩ := LRC.TwoBlock.exists_in_assigned_blocks
      ⟨m, hmS⟩ hpos k hpair
    have hbm := hblocks m hmS
    have hkR : (k m : ℝ) ≤ 1 := by exact_mod_cast hk
    refine ⟨t, ht, ?_, by linarith, ?_⟩
    · have : (0 : ℝ) ≤ k m := by positivity
      linarith
    · intro d hd
      obtain ⟨h1, h2⟩ := hblocks d hd
      exact LRC.TwoPinner.clear_of_band (N := k d) (by push_cast; nlinarith)
        (by push_cast; nlinarith)

/-- **The conjecture at eight runners from the spread-free covering**, for any step bound `M`.  No Case A/B/C split. -/
theorem lonelyRunnerAt8_of_cover8 (M : ℕ) (h : Cover8 M) : LRC.Spec.LonelyRunnerAt8 :=
  LRC.EndRunner.lonelyRunnerAt8_of_slowest fun v hv _ => by
    classical
    have hne := readingsOf_nonempty v 0
    have hpos := readingsOf_pos hv 0
    have hcard : (readingsOf v 0).card ≤ 7 := by
      unfold readingsOf
      exact le_trans Finset.card_image_le (by simp)
    have hmS : (readingsOf v 0).min' hne ∈ readingsOf v 0 := Finset.min'_mem _ hne
    exact lonely_of_gridStep8 hne hpos (hpos _ hmS)
      (h _ hcard hpos _ hmS (fun d hd => Finset.min'_le _ d hd))

end LRC.RegimeSkeleton
