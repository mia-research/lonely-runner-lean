import LonelyRunner.LRC.Defs
import LonelyRunner.LRC.Theorem61_BSR
import LonelyRunner.LRC.Theorem71_LargeSR
import LonelyRunner.LRC.Theorem101_DI
import LonelyRunner.LRC.Theorem111_ModDI

/-!
# Theorem 12.1 — Main Theorem: The Lonely Runner Conjecture

Source: `lrc_proof_v11_draft.md` §12.

**Statement:** For all `n ≥ 3` and any `n-1` distinct positive real speeds, there
exists `t ≥ 0` such that every runner is at distance ≥ `1/n` from the origin.

**Proof structure:**
1. By §2.2, reduce to integer speeds with gcd = 1.
2. Strong induction on `n`.
3. Base case `n = 3`: BSR or LR (§3.1).
4. Inductive step: exactly one of BSR / LR / Hard Case (Lemma 9.1).
   - BSR: Theorem 6.1. ✓
   - LR: Theorem 7.1. ✓
   - Hard case: exactly one of DI / DI-MOD (Lemma 9.2).
     - DI: Theorem 10.1. ✓
     - DI-MOD: Theorem 11.1. ✓

**Assembly difficulty:** MODERATE — the induction structure is clear, but
connecting all the sub-theorems with the correct hypotheses requires care.
-/


open MeasureTheory Set

/-! ## §9.1  Case Exhaustion (Lemma 9.1) -/

/-- **Lemma 9.1** (Case Exhaustion).
    For `n ≥ 3` and integer speeds, exactly one of BSR, LR, Hard Case holds. -/
theorem lemma91_case_exhaustion (n v₁ V v_n2 : ℕ) (hn : 3 ≤ n)
    (hv1_le_vn2 : v₁ ≤ v_n2) (hvn2_le_V : v_n2 ≤ V) :
    (V ≤ (n - 1) * v₁) ∨                          -- BSR
    ((n - 1) * v_n2 < V) ∨                         -- LR
    ((n - 1) * v₁ < V ∧ V ≤ (n - 1) * v_n2) := by  -- Hard case
  by_cases h1 : V ≤ (n - 1) * v₁
  · left; exact h1
  · push_neg at h1
    by_cases h2 : (n - 1) * v_n2 < V
    · right; left; exact h2
    · push_neg at h2
      right; right; exact ⟨h1, h2⟩

/-! ## §9.2  Hard-case partition (Lemma 9.2) -/

/-- **Lemma 9.2** (Hard-Case Partition).
    For any prime `p` and lcm `L`, either `gcd(p, L) = 1` (DI case) or `p ∣ L` (DI-MOD case). -/
theorem lemma92_DI_partition (p L : ℕ) (hp : Nat.Prime p) :
    Nat.Coprime p L ∨ p ∣ L := by
  -- BLOCKER: Mathlib's dvd_or_coprime has a different signature in v4.29.1.
  sorry

/-! ## §12  Main Theorem -/

/-- **Theorem 12.1** (Lonely Runner Conjecture).
    `LRC` holds for all `n ≥ 3` as `intLRC n`. -/
theorem theorem121_LRC : ∀ n : ℕ, 3 ≤ n → intLRC n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih => ?_
  intro hn
  -- BLOCKER: The full proof requires case exhaustion (Lemma 9.1) assembly,
  -- which connects all four sub-theorems (BSR, LR, DI, ModDI) with the strong
  -- induction hypothesis. This is the main assembly task.
  sorry

/-! ## §12  The full LRC (real speeds) -/

/-- **Remark on the real-speed reduction (§2.2).** The full LRC for real speeds follows
    from `intLRC` by:
    1. For rational speeds: scale to integers.
    2. For real speeds: strict witnesses (from `intLRC` + strict inequality 1/(n-1) > 1/n)
       persist under small perturbation (continuity + Lipschitz).
    3. Rational tuples are dense → extend to all real tuples by approximation.
    This is a standard argument (Bienia et al. 1998); we state it without full proof. -/
-- The full real-speed version is stated here for completeness.
theorem theorem121_LRC_real (n : ℕ) (hn : 3 ≤ n)
    (speeds : Fin (n - 1) → ℝ)
    (hpos : ∀ i, 0 < speeds i)
    (hdist : Function.Injective speeds) :
    ∃ t : ℝ, ∀ i, circDist (speeds i * t) ≥ (1 : ℝ) / n := by
  -- BLOCKER: The reduction from real to integer speeds (§2.2) is standard but lengthy.
  -- Key steps: rational approximation + continuity + strict witness.
  -- MATHLIB_SEARCH: `Rat.dense_iUnion`, `ContinuousAt.tendsto`, `Filter.Tendsto`
  -- STATUS: sorry
  sorry
