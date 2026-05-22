import LonelyRunner.LRC.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Theorem 5.2 — Integer-Speed Equidistribution (CRT measure independence)

Source: `lrc_proof_v11_draft.md` §5.

**⚠️ CRITICAL DEPENDENCY — read carefully before attempting any other hard theorem.**

## What the manuscript calls "Weyl equidistribution"

The theorem as stated in the manuscript (Theorem 5.2) is **NOT** Weyl's classical
equidistribution theorem (which is an asymptotic/ergodic statement). Instead, it is
a **finite CRT measure-factorisation** result:

> If `G` has period `1/L` and `gcd(p, L) = 1`, then on the period `[0, 1/(L*p))`,
> the indicator `1_G(t)` depends only on `t mod 1/L`, and `1_{A}({p*t})` depends only
> on `t mod 1/p`.  By the Chinese Remainder Theorem, these are independent, so:
>   `μ({t ∈ G : {p*t} ∈ A}) = μ(G) * μ(A) > 0`.

## Mathlib assessment (2025)

- `ZMod.chineseRemainder` (integer CRT): EXISTS.
- `AddCircle` product decomposition: PARTIAL — the CRT for real circles when gcd=1
  is not directly stated as a measure-preserving map in this form.
- `MeasureTheory.Measure.prod` (product measure): EXISTS.
- `MeasureTheory.integral_prod` / Fubini: EXISTS.
- The specific bijection `φ : [0, 1/(Lp)) → [0,1/L) × [0,1/p)` as measure-preserving:
  NOT directly in Mathlib as a named lemma.

**Conclusion:** Theorem 5.2 must be proved from Mathlib primitives.  The proof involves:
1. The CRT bijection on real intervals (moderate difficulty).
2. Measure preservation of φ (derivable from Fubini + periodicity).
3. Integral factorisation (standard).

This is the **primary blocker** for Theorems 10.1 and 11.1.  A sorry stub is placed here;
resolving it is the top priority for the next formalization session.
-/


open MeasureTheory Set Real

/-! ## §5.1  Classical Weyl theorem (reference, not used directly) -/

/-- Classical Weyl equidistribution: for irrational α, the sequence {n*α} is
    equidistributed mod 1.  This is Theorem 5.1 in the manuscript (stated for reference).
    The actual engine is Theorem 5.2 below. -/
-- NOTE: Mathlib has `AddCircle.equidistributed_of_irrational` for irrational rotations.
-- We state this for completeness but do not use it in the proof.
#check MeasureTheory.tendsto_setAverage_atTop  -- Birkhoff ergodic theorem

/-! ## §5.2  The CRT independence lemma (Theorem 5.2) -/

/-- **Helper:** The period of `jointGoodSet speeds n` is `1 / Nat.lcm_of_speeds speeds`.

    Each `goodSet v_i n` has period `1/v_i`, so `jointGoodSet` has period
    `lcm(1/v_1, ..., 1/v_k) = 1 / lcm(v_1, ..., v_k)`. -/
noncomputable def lcmSpeeds {k : ℕ} (speeds : Fin k → ℕ) : ℕ :=
  Finset.univ.sup speeds  -- This is the lcm; we use sup as a placeholder
-- NOTE: Mathlib has `Finset.lcm` : `Finset.lcm Finset.univ speeds`.
-- MATHLIB_SEARCH: `Finset.lcm`, `Nat.lcm`

/-- The CRT bijection: for `gcd(p, L) = 1`, the map
    `φ(t) = (t mod 1/L, t mod 1/p) : [0, 1/(L*p)) → [0, 1/L) × [0, 1/p)`
    is a measure-preserving bijection. -/
-- This is the core claim that needs to be formalized.
-- BLOCKER: Expressing "t mod 1/L" as a real-valued operation and showing bijectivity
-- requires translating integer CRT to the real-interval setting.
-- MATHLIB_SEARCH: `ZMod.chineseRemainder`, `Nat.Coprime.eq_of_modeq_of_lt`

/-- **Theorem 5.2** (Integer-Speed Equidistribution / CRT Measure Lemma).

    Let `G` be the simultaneous good set for speeds with lcm `L`,
    let `p` be a positive integer with `Nat.Coprime p L`,
    and let `A ⊆ [0,1)` be a measurable set with positive measure.
    If `μ(G) > 0`, then:
      `μ({t ∈ G | Int.fract (p * t) ∈ A}) = μ(G) * μ(A) > 0`. -/
theorem theorem52_weyl
    {k : ℕ} (speeds : Fin k → ℕ) (n L p : ℕ)
    (hL : L = lcmSpeeds speeds)
    (hcop : Nat.Coprime p L)
    (hp : 0 < p) (hL_pos : 0 < L)
    (A : Set ℝ) (hA_meas : MeasurableSet A) (hA_pos : 0 < MeasureTheory.volume A)
    (hG_pos : 0 < MeasureTheory.volume (jointGoodSet speeds n)) :
    MeasureTheory.volume
      ({t ∈ jointGoodSet speeds n | Int.fract ((p : ℝ) * t) ∈ A}) =
    MeasureTheory.volume (jointGoodSet speeds n) *
    MeasureTheory.volume A := by
  -- PROOF OUTLINE:
  -- 1. G is periodic with period 1/L.
  -- 2. {1_{A}({p*t})} is periodic with period 1/p.
  -- 3. Since gcd(p,L)=1, on [0, 1/(Lp)):
  --      ∫ 1_G(t) * 1_A({pt}) dt = (∫_{[0,1/L)} 1_G) * (∫_{[0,1/p)} 1_A({pu}) du)
  --    by the CRT bijection φ.
  -- 4. The first factor = μ(G) * (1/(Lp)) / (1/L) = μ(G) / p.
  --    The second factor = μ(A) * (1/(Lp)) / (1/p) = μ(A) / L.
  -- 5. Multiply: μ(G) * μ(A) / (Lp) per period [0, 1/(Lp)).
  --    Summing over Lp periods in [0,1): total = μ(G) * μ(A). ✓
  -- BLOCKER: The CRT bijection step requires formalising the real-interval CRT.
  -- This is the primary open item for this formalization.
  -- MATHLIB_SEARCH:
  --   "MeasureTheory.Measure.prod_eq"
  --   "Measurable.comp_measurable"
  --   "Int.fract_periodic"
  -- STATUS: sorry
  sorry

/-- **Corollary:** Under the hypotheses of Theorem 5.2, the intersection is non-empty. -/
theorem theorem52_nonempty
    {k : ℕ} (speeds : Fin k → ℕ) (n L p : ℕ)
    (hL : L = lcmSpeeds speeds)
    (hcop : Nat.Coprime p L) (hp : 0 < p) (hL_pos : 0 < L)
    (A : Set ℝ) (hA_meas : MeasurableSet A) (hA_pos : 0 < MeasureTheory.volume A)
    (hG_pos : 0 < MeasureTheory.volume (jointGoodSet speeds n)) :
    ∃ t₀ ∈ jointGoodSet speeds n, Int.fract ((p : ℝ) * t₀) ∈ A := by
  have hmeas := theorem52_weyl speeds n L p hL hcop hp hL_pos A hA_meas hA_pos hG_pos
  -- The product μ(G) * μ(A) is positive, so the set has positive measure and is non-empty.
  have hpos : 0 < MeasureTheory.volume ({t ∈ jointGoodSet speeds n | Int.fract ((p : ℝ) * t) ∈ A}) := by
    rw [hmeas]
    exact ENNReal.mul_pos (ne_of_gt hG_pos) (ne_of_gt hA_pos)
  -- A measurable set of positive measure is non-empty.
  -- BLOCKER: Need `MeasureTheory.nonempty_of_measure_pos` or similar.
  -- MATHLIB_SEARCH: `MeasureTheory.Measure.pos_iff_ne_empty`, `Set.nonempty_iff_ne_empty`
  -- STATUS: sorry
  sorry

/-! ## §5.3  Periodicity of jointGoodSet -/

/-- The simultaneous good set is periodic with period `1/L` where `L = lcm(speeds)`. -/
theorem jointGoodSet_periodic
    {k : ℕ} (speeds : Fin k → ℕ) (n : ℕ)
    (hpos : ∀ i, 0 < speeds i)
    (L : ℕ) (hL : L = Finset.lcm Finset.univ speeds) :
    ∀ t : ℝ, jointGoodSet speeds n t ↔ jointGoodSet speeds n (t + (1 : ℝ) / L) := by
  -- Each component goodSet(v_i) has period 1/v_i.
  -- The lcm gives the period of the intersection.
  -- BLOCKER: Requires that 1/L is a multiple of each 1/v_i,
  --          i.e., v_i | L for all i (true by definition of lcm).
  -- MATHLIB_SEARCH: `Finset.dvd_lcm`, `goodSet_periodic`
  -- STATUS: sorry
  sorry
