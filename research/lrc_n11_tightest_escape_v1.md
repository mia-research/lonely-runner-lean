# Tightest Near-LRC-Failure: Findings and Interpretation

**Date:** 2026-03-22 (updated same session)
**Scope:** Complete-blocking configurations, n=11, EFN frame; minimising good fraction in W_0.
**Status:** Empirical Observation (computational; not analytically proved).
**Empirical floor (updated):** GF ≥ **0.12%** (500k grid, deep NM + perturbation search, Session 2026-03-22).

---

## Summary of Findings

| Configuration class | Min GF in W_0 | Notes |
|---|---|---|
| a_1 ∈ (0.10, 0.30) | 9.06% | Far from AP; many witnesses outside W_0 |
| a_1 ∈ (0.30, 0.50) | 5.78% | |
| a_1 ∈ (0.50, 0.70) | 4.70% | |
| a_1 ∈ (0.70, 0.85) | 3.74% | |
| a_1 ∈ (0.85, 0.95) | 2.08% | |
| a_1 ∈ (0.95, 1.00) | 1.46% | All 9 witnesses t_2,...,t_10 in W_0 |
| a_1 ∈ (0.97, 0.999) | 1.20% | |
| a_1 ∈ (0.99, 0.9999) | **0.82%** | Tightest seen; 1M samples |
| a_1 ∈ (0.995, 0.9999) | 1.24% | Subset; likely sampling variance |
| max\|δ_i\| ≤ 0.9, all a_1 | **~0.12%** | Deep NM minimum (Session 2026-03-22); sign pattern ++------ |
| max\|δ_i\| > 1 (degenerate) | 0% in W_0 | But LRC still holds via other windows |

---

## Route 2 Result

**Route 2 FAILS to close the analytic gap.**

The density argument shows:
$$\sum_{i=2}^{10} |B_i \cap W_0| = \frac{18}{11}|W_0|$$
Minimum pairwise overlap: $(7/22)|W_0|$. This forces the union to potentially cover all of $W_0$ — it only guarantees $|G| \geq 0$, not $|G| > 0$.

See `lrc_n11_route2_attempt_v1.md` for the full argument and where it breaks.

---

## Tightest Near-Failure Configuration

**Extremal config (approx, found by random search over 1M samples with a_1 ∈ (0.99, 0.9999)):**

```
a_1      = 0.9912    (delta_1 = -0.0088)
speeds   ≈ [0.9912, 2.807, 3.474, 4.390, 4.840, 5.471, 6.273, 7.705, 9.239, 10]
deltas   ≈ [-0.009, 0.807, 0.474, 0.390, -0.160, -0.529, -0.727, -0.295, 0.239]
max|δ|   = 0.807
Good fraction in W_0 (high-res 100k grid): 0.82%
```

**Key structural features:**
- Only 9 witnesses (t_2,...,t_10) lie in W_0 (t_1 just outside since a_1 < 1)
- Blocking assignments spread across runners 2–9 (no single runner dominates)
- Max simultaneous bad runners in W_0: at most 4 (stacking bound much below 9)
- Good times form a small connected interval in W_0 — not isolated points

---

## Degenerate Large-Perturbation Case

When max|δ_i| > 1 (e.g., δ_2 ≈ -1.96 giving speed a_2 ≈ 0.04), GF in W_0 = 0%.

**This is NOT a LRC counterexample.** Verification:
- Runner 2 (speed 0.04) has its lonely window at t ∈ [2.15, 21.5] — far outside W_0
- LRC holds at t ≈ 2.44 (all 10 runners lonely simultaneously)
- The W_0-based strategy simply fails when speeds deviate radically from AP values

**Implication:** The EFN/AP witness framework requires speeds to remain near-integer AP values. The natural domain for this approach is max|δ_i| ≤ some absolute constant (empirically, the interesting structure lives in max|δ_i| ≤ 0.9).

---

## Pattern: Min GF vs a_1

The minimum GF is a *decreasing function of a_1* (as a_1 → 1 from below):

$$\text{min GF} \approx c_0 + c_1 (1 - a_1)^{\alpha}$$

for some constants. Empirically, as a_1 → 1, the minimum GF approaches approximately 0.8%–1.2% (not 0).

**Conjecture (Empirical):** There exists an absolute constant $c > 0$ such that for every complete-blocking configuration with max|δ_i| ≤ 1 and a_1 ∈ (0, 1):
$$|G \cap W_0| \geq c \cdot |W_0|.$$

The empirical lower bound is $c \gtrsim 0.008$ (approximately 1% of W_0).

---

## Why the Good Fraction Is Bounded Away From Zero (Hypothesis)

The computation consistently shows GF > 0.8% for all tested complete-blocking configs (bounded δ). Several structural reasons may contribute:

**H1 — Speed integrality constraint.** All speeds are near-integer (a_i ≈ i). This forces the bad intervals of runners i and i+1 to nearly coincide at specific times (since i/(i+1) is close to a simple fraction). Near-coincidence creates forced overlaps that reduce the total union.

**H2 — No-missing-slot bijection.** The residues $r_i(m) = im \bmod 11$ form a bijection on {1,...,10} for each fixed m. This means: at any AP witness t_m, the runners' fractional positions are DISTINCT residues/11. No two runners can simultaneously be in their bad zones at the SAME AP witness (unless one is just barely bad, not deeply bad). This structural regularity prevents the bad sets from aligning perfectly to cover W_0.

**H3 — Runner 10 pinning.** Runner 10 has speed exactly 10 (δ_{10} = 0). Its bad intervals are fixed at positions k/10 and (k + 10/11)/10. These fixed bad intervals interact with the other runners' bad intervals in a structured way, preventing perfect coverage.

---

## Implications for Proof Strategy

| Route | Status | Reason |
|---|---|---|
| Route 1: Fourier/equidistribution | Only for irrational ratio (Prop E in paper) | Fails for commensurable speeds |
| Route 2: Explicit overlap bound | **FAILS** | Density argument gives ≥ 0 not > 0 |
| Route 3: Continuity + compactness | Promising | If min GF is bounded below by c > 0 on compact feasible set |
| Route 4: Structural argument via H1–H3 above | Unexplored | Requires deeper analysis of near-integer speed interactions |

**Route 3 remains the strongest candidate.** If the feasible set of complete-blocking configurations is compact (in appropriate topology), and GF is continuous and bounded below by c > 0 on this set, then we're done. The compactness question reduces to: is the complete-blocking condition closed and bounded?

The set CB = {δ ∈ ℝ^9 : config is complete-blocking, a_1 > 0} is not compact (unbounded for large |δ_i|). But restricted to max|δ_i| ≤ M for any M, it is compact. So Route 3 would need to handle the large-δ regime separately (where LRC holds by other means).

---

## Next Steps

1. **Route 3:** Establish compactness of CB ∩ {max|δ_i| ≤ 1} and prove GF is continuous on it.
2. **Structural analysis (H2):** Formalise the no-missing-slot argument — does it give a lower bound on GF?
3. **Runner 10 pinning (H3):** Analyse how the fixed-speed runner forces GF ≥ c for some c.
4. **Verify the 0.82% floor** with a targeted optimisation (Nelder-Mead from multiple starts near a_1 ∈ (0.99, 1.00)).
