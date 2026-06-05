import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.MetricSpace.HausdorffDistance

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
    have : Int.fract (-x) = 0 := by simp [Int.fract_neg, h]
    simp [h, this]
  · rw [Int.fract_neg h]
    ring_nf
    rw [min_comm]

end circDist

/-! ## §2.2  Good and bad sets (§2.3 of manuscript) -/

/-- `goodSet v n` is the set of times `t` at which runner with speed `v`
    is at distance ≥ `1/n` from the origin. -/
noncomputable def goodSet (v n : ℕ) : Set ℝ :=
  { t : ℝ | circDist ((v : ℝ) * t) ≥ (1 : ℝ) / (n : ℝ) }

/-- `badSet v n` is the complement of `goodSet v n`. -/
noncomputable def badSet (v n : ℕ) : Set ℝ := (goodSet v n)ᶜ

/-- The simultaneous good set for a finite indexed family of runners.
    This is `G_s` in the manuscript when `speeds` enumerates the slow runners. -/
noncomputable def jointGoodSet {k : ℕ} (speeds : Fin k → ℕ) (n : ℕ) : Set ℝ :=
  ⋂ i, goodSet (speeds i) n

/-! ## §2.3  Continuity, closedness, measurability -/

/-- `circDist x` equals the infimum-distance from `x` to the integer lattice `ℤ ⊆ ℝ`.

    Proof by `le_antisymm`:
    - Upper bound: `infDist ≤ dist x ⌊x⌋ = f` and `infDist ≤ dist x (⌊x⌋+1) = 1-f`.
    - Lower bound: for each `n : ℤ`, set `k = n - ⌊x⌋`; case split on k ≤ 0, k = 1, k ≥ 2. -/
theorem circDist_eq_infDist (x : ℝ) :
    circDist x = Metric.infDist x (Set.range (Int.cast : ℤ → ℝ)) := by
  have hf0 : 0 ≤ Int.fract x := Int.fract_nonneg x
  have hf1 : Int.fract x < 1 := Int.fract_lt_one x
  have hfl : (⌊x⌋ : ℝ) + Int.fract x = x := Int.floor_add_fract x
  have hmem_floor : (⌊x⌋ : ℝ) ∈ Set.range (Int.cast : ℤ → ℝ) := ⟨⌊x⌋, rfl⟩
  have hmem_next : ((⌊x⌋ + 1 : ℤ) : ℝ) ∈ Set.range (Int.cast : ℤ → ℝ) :=
    ⟨⌊x⌋ + 1, rfl⟩
  have hd_floor : dist x (⌊x⌋ : ℝ) = Int.fract x := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (Int.floor_le x))]
    linarith
  have hd_next : dist x ((⌊x⌋ + 1 : ℤ) : ℝ) = 1 - Int.fract x := by
    have hlt := Int.lt_floor_add_one x
    rw [Real.dist_eq,
        show ((⌊x⌋ + 1 : ℤ) : ℝ) = (⌊x⌋ : ℝ) + 1 from by push_cast; ring,
        abs_of_nonpos (by linarith)]
    linarith
  have h_lb : ∀ n : ℤ, circDist x ≤ dist x (n : ℝ) := by
    intro n
    unfold circDist
    have hrw : x - (n : ℝ) = Int.fract x - ((n - ⌊x⌋ : ℤ) : ℝ) := by
      push_cast; linarith
    rw [Real.dist_eq, hrw]
    set f := Int.fract x
    set k : ℤ := n - ⌊x⌋
    by_cases hk0 : k ≤ 0
    · have hk_r : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
      rw [abs_of_nonneg (by linarith)]
      linarith [min_le_left f (1 - f)]
    · push_neg at hk0
      by_cases hk2 : 2 ≤ k
      · have hk_r : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
        rw [abs_of_nonpos (by linarith)]
        have hmin12 : min f (1 - f) ≤ 1 / 2 := by
          by_cases h : f ≤ 1 / 2
          · linarith [min_le_left f (1 - f)]
          · push_neg at h; linarith [min_le_right f (1 - f)]
        linarith
      · push_neg at hk2
        have hk1 : k = 1 := by omega
        have hk_r : (k : ℝ) = 1 := by exact_mod_cast hk1
        rw [hk_r, abs_of_nonpos (by linarith)]
        linarith [min_le_right f (1 - f)]
  apply le_antisymm
  · have hne : (Set.range (Int.cast : ℤ → ℝ)).Nonempty := Set.range_nonempty _
    rw [Metric.le_infDist hne]
    rintro y ⟨n, rfl⟩
    exact h_lb n
  · unfold circDist
    apply le_min
    · calc Metric.infDist x (Set.range (Int.cast : ℤ → ℝ))
          ≤ dist x (⌊x⌋ : ℝ) := Metric.infDist_le_dist_of_mem hmem_floor
        _ = Int.fract x := hd_floor
    · calc Metric.infDist x (Set.range (Int.cast : ℤ → ℝ))
          ≤ dist x ((⌊x⌋ + 1 : ℤ) : ℝ) := Metric.infDist_le_dist_of_mem hmem_next
        _ = 1 - Int.fract x := hd_next

/-- `circDist` is continuous.

    Proof: `circDist x = Metric.infDist x (Set.range (Int.cast : ℤ → ℝ))` by
    `circDist_eq_infDist`, and `Metric.infDist · s` is continuous for any set `s`. -/
theorem circDist_continuous : Continuous circDist := by
  change Continuous (fun x => circDist x)
  simp_rw [circDist_eq_infDist]
  exact Metric.continuous_infDist_pt _

/-- `circDist` is 1-Lipschitz: `|circDist x - circDist y| ≤ |x - y|`.

    Proof: `circDist = infDist · ℤ` (by `circDist_eq_infDist`), and
    `infDist · s` is 1-Lipschitz for any set `s` (`Metric.lipschitz_infDist_pt`). -/
theorem circDist_lipschitz : LipschitzWith 1 circDist := by
  change LipschitzWith 1 (fun x => circDist x)
  simp_rw [circDist_eq_infDist]
  exact Metric.lipschitz_infDist_pt _

/-- `goodSet v n` is a closed set. Follows from continuity of `circDist`. -/
theorem goodSet_isClosed (v n : ℕ) : IsClosed (goodSet v n) := by
  unfold goodSet
  apply IsClosed.preimage
  · exact circDist_continuous.comp (continuous_const.mul continuous_id)
  · exact isClosed_Ici

/-- `jointGoodSet speeds n` is closed (finite intersection of closed sets). -/
theorem jointGoodSet_isClosed {k : ℕ} (speeds : Fin k → ℕ) (n : ℕ) :
    IsClosed (jointGoodSet speeds n) := by
  unfold jointGoodSet
  exact isClosed_iInter (fun i => goodSet_isClosed (speeds i) n)

/-- `goodSet v n` is measurable (every closed set is measurable). -/
theorem goodSet_measurable (v n : ℕ) : MeasurableSet (goodSet v n) :=
  (goodSet_isClosed v n).measurableSet

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
    some time witnesses all runners being lonely.

    The gcd = 1 condition (`Finset.gcd Finset.univ speeds = 1`) is the real
    normalisation from §2.2 of the manuscript. (The earlier formulation
    `Nat.Coprime (Finset.prod ...) 1` was vacuously true and let the
    DI-MOD case in §11 escape the necessary gcd hypothesis.) -/
def intLRC (n : ℕ) : Prop :=
  ∀ (speeds : Fin (n - 1) → ℕ),
    (StrictMono speeds) →
    (∀ i, 0 < speeds i) →
    Finset.gcd Finset.univ speeds = 1 →
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / (n : ℝ)

/-! ## §2.5  Induction scheme -/

/-- Strong induction hypothesis: LRC holds for all m < n. -/
def H (n : ℕ) : Prop := ∀ m, m < n → intLRC m
