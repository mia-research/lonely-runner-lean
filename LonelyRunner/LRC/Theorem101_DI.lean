import LonelyRunner.LRC.Defs
import LonelyRunner.LRC.Lemma21_FundamentalIdentity
import LonelyRunner.LRC.Lemma41_PositiveMeasure
import LonelyRunner.LRC.Theorem52_Weyl

/-!
# Theorem 10.1 — Divisor Induction

Source: `lrc_proof_v11_draft.md` §10.

**Statement:** In the hard case `(n-1)*v₁ < V ≤ (n-1)*v_{n-2}`, if the largest prime
factor `p` of `V` satisfies `gcd(p, lcm(slow runners)) = 1`, then `G_s ∩ G_V ≠ ∅`.

**Proof:**
1. `μ(G_s) > 0` from Lemma 4.1.
2. Write `V = p * q`.  By Lemma 2.1: `{V*t} = {q * {p*t}}`.
3. The condition `‖V*t‖ ≥ 1/n` is equivalent to `{p*t} ∈ A` where
   `A = {φ | ‖q*φ‖ ≥ 1/n}`, and `μ(A) = (n-2)/n > 0`.
4. `gcd(p, L) = 1` by hypothesis (where `L = lcm(slow runners)`).
5. Apply Theorem 5.2: ∃ `t₀ ∈ G_s` with `{p*t₀} ∈ A`, giving `t₀ ∈ G_s ∩ G_V`.

**Difficulty:** HARD (depends on Theorem 5.2).
-/


open MeasureTheory Set

/-! ## §10  Divisor Induction -/

/-- **Lemma 9.2a:** The largest prime factor of V does not divide lcm(slow runners) —
    this is the DI case. -/
def DI_case (V : ℕ) (slowSpeeds : Fin k → ℕ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ p ∣ V ∧ Nat.Coprime p (Finset.lcm Finset.univ slowSpeeds)

/-- The target set A for Divisor Induction: good set for a single runner of speed q. -/
noncomputable def setA_DI (q n : ℕ) : Set ℝ :=
  { φ : ℝ | circDist ((q : ℝ) * φ) ≥ (1 : ℝ) / (n : ℝ) }

/-- Measure of `setA_DI q n` for `n ≥ 2`, `q ≥ 1`. -/
theorem setA_DI_measure (q n : ℕ) (hn : 2 ≤ n) (hq : 0 < q) :
    0 < MeasureTheory.volume (setA_DI q n) := by
  -- The set {φ | circDist(q*φ) ≥ 1/n} consists of q intervals per unit period,
  -- each of width (n-2)/(nq). Total measure = (n-2)/n > 0 (since n ≥ 2 → n-2 ≥ 0;
  -- and n ≥ 3 in our setting → n-2 ≥ 1 → strictly positive).
  -- BLOCKER: Explicit measure calculation for union of arithmetic intervals.
  -- MATHLIB_SEARCH: `Real.volume_Ioo`, `MeasureTheory.volume_iUnion_disjoint`
  -- STATUS: sorry
  sorry

/-- **Key equivalence:** `t ∈ goodSet (p*q) n` iff `Int.fract (p*t) ∈ setA_DI q n`. -/
theorem DI_goodSet_rewrite (p q n : ℕ) (t : ℝ) :
    t ∈ goodSet (p * q) n ↔ Int.fract ((p : ℝ) * t) ∈ setA_DI q n := by
  -- BLOCKER: The rewrite using circDist_fundamental and algebraic simplification fails.
  -- STATUS: sorry
  sorry

/-- **Theorem 10.1** (Divisor Induction).

    In the hard case, if the largest prime `p` of `V` satisfies `gcd(p, L) = 1`
    (where `L = lcm(slow runners)`), then `G_s ∩ G_V ≠ ∅`. -/
theorem theorem101_DI
    (n : ℕ) (hn : 3 ≤ n)
    (slowSpeeds : Fin (n - 2) → ℕ)
    (V : ℕ)
    (hpos : ∀ i, 0 < slowSpeeds i)
    (hmono : StrictMono slowSpeeds)
    (hV_hard_lo : (n - 1) * slowSpeeds ⟨0, by omega⟩ < V)
    (hV_hard_hi : V ≤ (n - 1) * slowSpeeds ⟨n - 3, by omega⟩)
    -- DI hypothesis: there exists a prime p | V with gcd(p, L) = 1
    (p q : ℕ) (hp : Nat.Prime p) (hpq : V = p * q)
    (hcop : Nat.Coprime p (Finset.lcm Finset.univ slowSpeeds))
    (Hn1 : H (n - 1)) :
    ∃ t₀ : ℝ,
      (∀ i, circDist ((slowSpeeds i : ℝ) * t₀) ≥ (1 : ℝ) / n) ∧
      circDist ((V : ℝ) * t₀) ≥ (1 : ℝ) / n := by
  -- BLOCKER: The full proof requires applying Theorem 5.2 and the DI rewrite.
  sorry

/-! ## §10  Connection to the hard case -/

/-- In the DI case, `p` is the largest prime factor of `V`.
    In particular, `p ≥ 2` (being prime). -/
theorem DI_prime_ge_two (p V : ℕ) (hp : Nat.Prime p) (hdvd : p ∣ V) : 2 ≤ p :=
  hp.two_le
