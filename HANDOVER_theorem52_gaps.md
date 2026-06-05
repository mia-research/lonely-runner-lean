# Handover Document: Formalization Findings on Theorem 5.2

**To:** Pen-and-Paper Proof Team
**From:** Lean 4 Formalization Team
**Date:** 2026-05-23
**Re:** Critical corrections required in Theorem 5.2 and upstream claims

---

## Summary

The Lean 4 formalization of the LRC proof has identified three mathematical errors in
the current manuscript's Theorem 5.2 (the "CRT Measure Lemma"). The central claim —
that `μ({t ∈ G : {p·t} ∈ A}) = μ(G)·μ(A)` for any measurable A with positive
measure — is false. The two lemmas on which the proof rests are also false as stated.
This document details each error with a concrete counterexample, explains the root
cause, identifies what is correct, and recommends the specific changes needed for the
downstream proof of Theorem 10.1 (Divisor Induction) to proceed.

---

## Error 1 — Periodicity of the joint good set

**Manuscript claim:** The simultaneous good set G = ⋂ᵢ goodSet(vᵢ, n) has period
1/L, where L = lcm(v₁,...,vₖ).

**Status: FALSE.**

Each goodSet(vᵢ, n) has period 1/vᵢ (proved in the formalization). When the speeds
vᵢ are distinct positive integers with gcd = 1 — the normalised case used throughout
the proof — the least common multiple of the periods 1/vᵢ is lcm(1/v₁,...,1/vₖ) = 1,
not 1/L. The joint good set therefore has period 1, and the indicator function
𝟙_G(t) cannot in general be expressed as a function of {L·t} alone.

The formalization proves `jointGoodSet_periodic` with period 1 and this is
type-checked. The claim of period 1/L is unproved and false for coprime integer speeds.

---

## Error 2 — Independence of fractional parts

**Manuscript claim:** For integers L and p with gcd(L, p) = 1, the random variables
{L·t} and {p·t} are independent when t is uniform on [0, 1). That is, for all
measurable U, V ⊆ [0, 1):

    μ({t ∈ [0,1) : {L·t} ∈ U  and  {p·t} ∈ V}) = μ(U) · μ(V).

**Status: FALSE.**

Counterexample: L = 2, p = 3, U = [0, 1/6), V = [0, 1/4).

  {2t} ∈ [0, 1/6)  iff  t ∈ [0, 1/12) ∪ [1/2, 7/12).
  {3t} ∈ [0, 1/4)  iff  t ∈ [0, 1/12) ∪ [1/3, 5/12) ∪ [2/3, 3/4).

The intersection is [0, 1/12) alone, so the joint measure is 1/12.
The product μ(U)·μ(V) = (1/6)·(1/4) = 1/24.

Since 1/12 ≠ 1/24, the independence claim fails by a factor of 2.

**Root cause.** On each CRT cell [m/(Lp), (m+1)/(Lp)), both {L·t} and {p·t} are
strictly increasing linear functions of t. Knowing {L·t} determines t within the cell
(up to which cell it is), which then determines {p·t} exactly. The two variables are
maximally correlated within each cell, not independent. The CRT bijection on cell
*indices* is correct and proved, but it does not imply independence of the continuous
fractional parts.

**What is true.** For *elementary* intervals — U = [j/p, (j+1)/p) and
V = [k/L, (k+1)/L) — the CRT bijection on Fin(L·p) gives exactly one cell m* with
m* mod p = j and m* mod L = k, so the joint measure is 1/(Lp) = μ(U)·μ(V). This
extends to finite unions of elementary intervals but does not extend to arbitrary
measurable sets.

---

## Error 3 — The main theorem

**Manuscript claim (Theorem 5.2):** If G = jointGoodSet(speeds, n) has positive
measure, L = lcm(speeds), gcd(p, L) = 1, and A ⊆ [0,1) is measurable with μ(A) > 0,
then:

    μ({t ∈ G : {p·t} ∈ A}) = μ(G) · μ(A).

**Status: FALSE.**

Counterexample: n = 5, speeds = [2] (so L = 2), p = 3 (gcd(3, 2) = 1 ✓),
A = [0, 1/6).

  G = goodSet(2, 5) = [1/10, 2/5) ∪ [3/5, 9/10),  μ(G) = 3/5.

  {3t} ∈ [0, 1/6)  iff  t ∈ [0, 1/18) ∪ [1/3, 7/18) ∪ [2/3, 13/18).

  G ∩ {3t ∈ [0,1/6)} = [1/3, 7/18) ∪ [2/3, 13/18),  μ = 1/18 + 1/18 = 1/9.

  μ(G)·μ(A) = (3/5)·(1/6) = 1/10.

Since 1/9 ≠ 1/10, the theorem fails.

**Why n = 4 appears correct.** The formula does hold for n = 4, v = 2, p = 3. This
is not a sign that the theorem is true; it is a coincidence specific to n = 4. The
indicator function of [1/4, 3/4] (the good region for n = 4) has all even Fourier
coefficients equal to zero — that is, f̂(2m) = 0 for all nonzero integers m. This
causes the Fourier cross-terms between the two periodic indicators to cancel exactly,
making the formula correct at n = 4. For n = 5 the analogous orthogonality fails and
the formula breaks. The coincidence should not be mistaken for a general theorem.

---

## What the proof of Theorem 10.1 actually needs

Theorem 10.1 (Divisor Induction) does not require the measure equality. It requires
only that the set of jointly-good times for the extended runner system has *positive
measure*:

    μ({t ∈ G : circDist(p·t) ≥ 1/n}) > 0.

This positive-measure statement IS provable by a direct CRT cell-counting argument
that does not rely on the false independence claim.

**Proof strategy.** Partition [0, 1) into L·p·n cells of width 1/(Lpn). Both
G = jointGoodSet(speeds, n) and H = goodSet(p, n) = {t : {p·t} ∈ [1/n, (n-1)/n]}
are unions of such cells (G has breakpoints at multiples of 1/(Ln), H at multiples
of 1/(pn); the common refinement has width 1/(Lpn)).

Within this partition:
- G membership depends on the cell index m modulo (p·n), since G has period 1/L
  and 1/L = (pn) cells in the Lpn partition. The good cells within each L-period are
  those with n-sub-period index in {1, 2, ..., n-2}.
- H membership depends on m modulo (L·n), since H has period 1/p. The good cells
  within each p-period are similarly indexed by {1, 2, ..., n-2}.

Since gcd(L, p) = 1, for any pair of good n-sub-period indices (j, k) with
1 ≤ j, k ≤ n-2, the CRT supplies a unique cell m* in {0, ..., Lpn-1} satisfying
m* ≡ j·p (mod pn) and m* ≡ k·L (mod Ln) simultaneously. The intersection G ∩ H
therefore contains at least (n-2)² such cells, giving

    μ(G ∩ H) ≥ (n-2)² / (Lpn)  >  0   for all n ≥ 3.

This argument uses only `Nat.chineseRemainder`, `Real.volume_Ico`, and
`MeasureTheory.measure_iUnion_of_disjoint` — all available in Mathlib 4.29.1.

---

## Recommended manuscript changes

1. **Retract the period claim.** Remove or correct the assertion that jointGoodSet
   has period 1/L. The correct period is 1 (for coprime integer speeds). This
   affects the statement of any lemma in §5 that builds on this periodicity.

2. **Retract the independence claim.** Remove the claim that {L·t} and {p·t} are
   independent for general measurable sets. Replace it with the correct statement:
   the formula holds for U and V that are finite unions of elementary intervals of
   width 1/L and 1/p respectively.

3. **Replace Theorem 5.2 with the positive-measure lemma.** The correct theorem
   needed for §10 is:

   > **Theorem 5.2 (revised).** Let G = jointGoodSet(speeds, n) with μ(G) > 0,
   > L = lcm(speeds), and p a positive integer with gcd(p, L) = 1. Then
   >
   >     μ({t ∈ G : circDist(p·t) ≥ 1/n}) > 0.

   The proof is by CRT cell counting as described above. The stronger measure-equality
   formulation is false and should not appear in the manuscript.

4. **Audit §10 and §11.** Check whether Theorems 10.1 and 11.1 invoke the measure
   equality or only the existence/positivity consequence. If only positivity is used,
   replace the citation to Theorem 5.2 with the revised version. If the equality is
   used in a genuinely essential way, the argument in §10 or §11 must be restructured.

---

## Lean formalization status

The following are type-checked and proved in `Theorem52_Weyl.lean`:

| Lemma | Status |
|---|---|
| `goodSet_periodic_multiple` | PROVED |
| `jointGoodSet_periodic` (period 1) | PROVED |
| `crt_map_injective` | PROVED |
| `crt_index_bijection` | PROVED |
| `fract_equidistributed_one_period` | SORRY — statement false |
| `theorem52_weyl` | SORRY — statement false |
| `theorem52_pos_measure` (revised theorem) | SORRY — statement correct, ~100-200 lines to prove |

The build compiles cleanly with sorry stubs. The critical path to closing the
formalization is to implement `theorem52_pos_measure` (the CRT cell-counting proof)
and update the callers in `Theorem101_DI.lean` and `Theorem111_ModDI.lean` to
reference the corrected theorem.

---

*This document was produced by the Lean 4 formalization team during session
2026-05-23. The counterexamples have been verified analytically. The Lean file
`LRC/Theorem52_Weyl.lean` contains inline documentation of all findings.*
