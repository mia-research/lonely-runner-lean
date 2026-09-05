# PREREG v2 — Route A: is the reduced-system last-fall degree coefficient-forced (extending first-fall), and does the elementary-symmetric reduction move it? (power-first)

**Supersedes** `PREREG_semaev_symmetric_reduction_lastfall_v1.md` after an `experiment-designer` audit
found 9 decidable defects — headline **A: Δ_coeff may have ZERO power by construction** (the membership
ideal ⟨r₀,r₁,r₂⟩ is identical across rungs; if last-fall is coefficient-forced on this support — as
first-fall provably is — Δ_coeff≡0 with no power to see a lever = the "null with no power" failure mode).
**Status:** FROZEN before any degree is read. Model scale. **Date:** 2026-08-31. **Harness:**
`semaev_symmetric_reduction_lastfall_v1.py` (updated; exact GF(p); `check_no_float` passes; reduction
correctness `P(σ_i(x))==S₄(x,τ)` already verified True).

## 0. The reframing forced by defect A (power-first)
The experiment is NOT "rank Semaev against a random spread" (that presumes the statistic can move). It is:
**(1) does the reduced-system last-fall degree move with the S₃-symmetric coefficients at all?** If NO
(zero variance + Ŝ inert vs the membership ideal), the last-fall is coefficient-FORCED — a strong,
clean extension of the first-fall result to the binding solving-degree invariant, and the coefficient
lever is dead at m=3 first AND last fall. If YES (it moves), THEN **(2) is Semaev at an extreme of the
spread** (secp-specific lever). Power is measured, not assumed, and reported before any lever claim.

## 1. Fixes folded in (all 9)
- **A (power, must):** three explicit power probes, reported before the decision — (i) **Ŝ-inertness:**
  last-fall of ⟨r₀,r₁,r₂⟩ ALONE vs ⟨Ŝ,r₀,r₁,r₂⟩ (does the coefficient-bearing generator move it?);
  (ii) **coefficient variance:** the spread of last-fall over K=12 symmetric-random Ŝ draws (does varying
  Ŝ's coefficients move it?); (iii) **constructed plant:** ⟨Ŝ·(e₁−κ), r_i⟩ (a symmetric perturbation
  that RAISES the degree of the Ŝ generator) MUST shift last-fall vs ⟨Ŝ,r_i⟩ — if it does not, the
  read-out is blind to last-fall changes → VOID. Δ_coeff is interpreted ONLY if probe (i) or (ii) shows
  motion; otherwise the outcome is "last-fall coefficient-FORCED" (probe-(iii) confirms read-out live).
- **B (distinct-triple object, must):** the divisibility encoding C|g (g squarefree) represents ONLY
  distinct-coordinate triples. The object is therefore fixed as **distinct-x decompositions**; the
  un-reduced system adds the distinctness saturation (record ∏_{i<j}(x_i−x_j) is a unit on the variety),
  and the cross-check is **un-reduced-distinct variety = 6 × reduced variety** (exact, integer).
- **C (freeze t, must):** τ is derived from a FROZEN seed (`Random(1234+p)`) and **recorded** per p in
  the output; the support of Ŝ is a function of τ and is thereby frozen.
- **D (ideal equality, not variety proxy, must):** verify ⟨Ŝ,r₀,r₁,r₂⟩ equals the true elimination
  ideal elim_x⟨S₄, g(x₁),g(x₂),g(x₃), e_i−σ_i⟩ by comparing **reduced Gröbner bases** (object-level), not
  just variety cardinality. Mismatch → VOID.
- **E/F (decision on integer order statistics, must):** let a=last-fall(Semaev-reduced), and
  [lo,hi]=[min,max] of the 12 symmetric-random last-falls. **SECP-SPECIFIC ⟺ a < lo; GENERIC ⟺ lo ≤ a ≤
  hi; ANTI ⟺ a > hi.** No medians, no half-integers. Exhaustive over every sign.
- **G (reduced-vs-unreduced is DESCRIPTIVE-ONLY, freeze):** the reduced variety is exactly 6× smaller,
  which confounds any last-fall difference with variety size — so this comparison is reported but is NOT
  a decision axis. Same Dmax=20 for reduced and un-reduced; a censored un-reduced value is reported ">20".
- **H (symmetric re-check, freeze):** whatever outcome the frozen rule (§2) returns — lever OR forced/null
  — gets the SAME independent re-check (a second p, a second frozen seed for the random rung). Triggered
  by the procedure, not by which outcome surprises. (Given the one-way suppression bias, the null is
  re-checked as hard as a positive.)
- **I (knobs frozen):** random rung = uniform NONZERO GF(p) coeffs, seed `9000+p+k`, k=0..11; V = the 6
  x-coords from the frozen τ-construction (recorded); require reduced variety size ≥ 2 (nonemptiness gate)
  before any statistic is read, else VOID; cross-p rule: an outcome must hold at BOTH p∈{307,2069} to be
  reported as that outcome — a split is reported as INCONCLUSIVE with both shown.

## 2. Decision rule (frozen, power-gated)
1. **Compute power probes (i),(ii),(iii).** If (iii) does not move last-fall → VOID (read-out blind).
2. **If (i) shows ⟨r_i⟩ last-fall == ⟨Ŝ,r_i⟩ last-fall AND (ii) variance == 0** → **LAST-FALL
   COEFFICIENT-FORCED**: the reduced solving-degree invariant is fixed by the support/membership, not the
   coefficients — extends the first-fall invariance to last-fall; the coefficient lever is dead at m=3.
   `[VERIFIED-scope]`. (Δ_coeff not interpreted — it is powerless here by measurement, not assumption.)
3. **Else (statistic has power):** apply E/F — SECP-SPECIFIC (a<lo, escalate, counter-prior target) /
   GENERIC (lo≤a≤hi) / ANTI (a>hi). Must agree at both primes or INCONCLUSIVE.
4. **Descriptive (all cases):** report reduced vs un-reduced last-fall + the 6× variety relation +
   whether the reduction made a censored un-reduced computation tractable (a computational, not
   degree-lever, statement).

## 3. Power ceiling (frozen)
m=3 only, model p. Settles the coefficient-lever question at m=3 (first + last fall) and characterizes the
symmetrization's computational effect; does NOT settle the asymptotic (m≥4 reduction is the next step IF a
lever appears). No grade above `[EMPIRICAL/VERIFIED-scope, model scale]`. Not a route-A closure.

## 4. Exactness / fence
Exact GF(p) integers throughout; PRNG/generation boundary untouched.
