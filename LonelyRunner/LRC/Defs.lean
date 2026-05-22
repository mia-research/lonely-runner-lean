import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# Lonely Runner Conjecture — Core Definitions

Source: `lrc_proof_v11_draft.md` §2 (Setup and Notation).

We work with the "integer speeds, gcd = 1" normalisation established in §2.2.
All speeds are positive integers; distances are measured as `circDist` below.
-/

open MeasureTheory Set

/-! ## §2.1  Circle distance -/

/-- The distance from `x` to the nearest integer; equivalently, distance on the
    unit circle from `{x}` to 0.  Ranges in `[0, 1/2]`. -/
noncomputable def circDist (x : ℝ) : ℝ := min (Int.fract x) (1 - Int.fract x)

namespace circDist

theorem nonneg (x : ℝ) : 0 ≤ circDist x := by
  unfold circDist
  apply le_min
  · exact Int.fract_nonneg x
  · linarith [Int.fract_lt_one x]

theorem le_half (x : ℝ) : circDist x ≤ 1 / 2 := by
  unfold circDist
  simp only [min_le_iff]
  by_cases h : Int.fract x ≤ 1 / 2
  · left; linarith
  · right; linarith [Int.fract_nonneg x]

theorem le_one (x : ℝ) : circDist x ≤ 1 := by
  linarith [circDist.le_half x]

/-- `circDist` is periodic with period 1. -/
theorem periodic (x : ℝ) : circDist (x + 1) = circDist x := by
  unfold circDist
  simp [Int.fract_add_one]

/-- `circDist x = circDist (-x)` (symmetry). -/
theorem symm_neg (x : ℝ) : circDist (-x) = circDist x := by
  unfold circDist
  by_cases h : Int.fract x = 0
  · -- When x is an integer, Int.fract(-x) = 0 as well
    sorry
  · rw [Int.fract_neg h]
    ring_nf
    rw [min_comm]

end circDist

/-! ## §2.2  Good and bad sets (§2.3 of manuscript) -/

/-- `goodSet v n` is the set of times `t` at which runner with speed `v`
    is at distance ≥ `1/n` from the origin.  -/
noncomputable def goodSet (v n : ℕ) : Set ℝ :=
  { t : ℝ | circDist ((v : ℝ) * t) ≥ (1 : ℝ) / (n : ℝ) }

/-- `badSet v n` is the complement of `goodSet v n`. -/
noncomputable def badSet (v n : ℕ) : Set ℝ := (goodSet v n)ᶜ

/-- The simultaneous good set for a finite indexed family of runners.
    This is `G_s` in the manuscript when `speeds` enumerates the slow runners. -/
noncomputable def jointGoodSet {k : ℕ} (speeds : Fin k → ℕ) (n : ℕ) : Set ℝ :=
  ⋂ i, goodSet (speeds i) n

/-! ## §2.3  Measurability of good sets -/

/-- `goodSet v n` is measurable (as a preimage of a closed set under a continuous map). -/
theorem goodSet_measurable (v n : ℕ) : MeasurableSet (goodSet v n) := by
  unfold goodSet circDist
  -- The set {t | min (fract(v*t)) (1 - fract(v*t)) ≥ 1/n} is measurable.
  -- BLOCKER: Need `Int.fract` to be measurable, then measurability is composition.
  -- MATHLIB_SEARCH: `Measurable.min`, `measurable_fract`, `MeasurableSet.preimage`
  -- STATUS: sorry
  sorry

/-- `goodSet v n` has period `1/v` (assuming `v > 0`). -/
theorem goodSet_periodic (v n : ℕ) (hv : 0 < v) :
    ∀ t : ℝ, t ∈ goodSet v n ↔ t + (1 : ℝ) / v ∈ goodSet v n := by
  intro t
  simp only [goodSet, Set.mem_setOf_eq, circDist]
  have key : Int.fract ((v : ℝ) * (t + 1 / (v : ℝ))) = Int.fract ((v : ℝ) * t) := by
    have heq : (v : ℝ) * (t + 1 / (v : ℝ)) = (v : ℝ) * t + 1 := by field_simp
    rw [heq, Int.fract_add_one]
  rw [key]

/-! ## §2.4  The LRC predicate -/

/-- The Lonely Runner Conjecture for exactly `n` runners (including the stationary one).
    We state it for integer speeds with the gcd = 1 normalisation. -/
def LRC (n : ℕ) : Prop :=
  ∀ (speeds : Fin (n - 1) → ℕ),
    (Function.Injective speeds) →          -- distinct speeds
    (∀ i, 0 < speeds i) →                 -- positive speeds
    (Nat.Coprime (Finset.univ.sup speeds) 1 → True) →  -- placeholder for gcd = 1
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / (n : ℝ)

/-- Simplified integer LRC: for n-1 distinct positive integer speeds with gcd 1,
    some time witnesses all runners being lonely. -/
def intLRC (n : ℕ) : Prop :=
  ∀ (speeds : Fin (n - 1) → ℕ),
    (StrictMono speeds) →
    (∀ i, 0 < speeds i) →
    Nat.Coprime (Finset.prod Finset.univ speeds) 1 →
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / (n : ℝ)

/-! ## §2.5  Induction scheme -/

/-- Strong induction hypothesis: LRC holds for all m < n. -/
def H (n : ℕ) : Prop := ∀ m, m < n → intLRC m
