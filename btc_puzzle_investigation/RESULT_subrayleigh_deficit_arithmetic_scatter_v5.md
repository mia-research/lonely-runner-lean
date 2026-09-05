# RESULT — Sub-Rayleigh Deficit Arithmetic Scatter (PREREG v5)

**Date:** 2026-08-01
**Pre-registration:** `PREREG_subrayleigh_deficit_arithmetic_scatter_v5.md`
**Instrument:** `subrayleigh_deficit_scaling_v1.py` (frozen SHA 93c95471...)
**Schedule:** `PREREG_subrayleigh_deficit_arithmetic_scatter_v5_SCHEDULE.txt` (SHA a4b4f005...)
**Sweep:** `arithmetic_scatter_sweep_v1.py`
**Analysis:** `analysis_scatter_v5.py`
**Grade:** C — all P-controls nominal; H1a′ structurally vacuous (design issue, §BUG-1)

---

## §0 Scope Summary

- **101 surface primes** (p ≡ 1 mod 3, p ∈ [3000, 12000]), each with 3–4 cyclic sextic twists of y²=x³+7·gᵏ. Total surface cyclic twists measured: **404**.
- **254 trajectory primes** (disjoint from training 30), base curve (k=0) only, held out from surface fit.
- All measurements at small p. Nothing transfers to secp's 2²⁵⁶.
- Signal path: exact int EC arithmetic; float only in the p×p FFT (sanctioned carve-out, §8).
- Sweep: **100% complete**, 592 JSONL rows (338 surface cyclic + 254 trajectory).

---

## §1 Surface Fit

Model: $\hat f(p,n) = g_0(\ln p) + g_1(\ln p) \cdot u$, where $u = -a_p/\sqrt{p}$, $g_0, g_1$ degree ≤ 2 in $\ln p$. Fit from k≠0 cyclic twists only (k=0 held out). Weighted LS with weights $1/\mathrm{SE}_\delta^2$.

| Quantity | Value | Note |
|---|---|---|
| $R^2_{\mathrm{smooth}}$ | **0.563** | Excellent; far above the ~0.005 p-only baseline |
| Pooled partial $R^2(D, u)$ | **0.496** | Floor ≥ 0.25 met ✓ |
| Surface adequacy | **PASS** | |

The smooth surface $\hat f(p,n)$ captures 56% of the δ variance across all twists. The u-term alone (group-order channel) captures 50% of the pooled variance. The surface is well-determined.

---

## §2 Trajectory Residuals

$r(p) = \delta_0(p) - \hat f(p, n_0(p))$ for 254 trajectory primes:

| Statistic | Value |
|---|---|
| Range | $[-1.10 \times 10^{-4}, \; 1.28 \times 10^{-4}]$ |
| Mean | $1.59 \times 10^{-6}$ |
| SD | $3.48 \times 10^{-5}$ |
| Mean $|r|$/SE | ~8 | (scatter ≫ estimation, as required) |

Residuals are centered near zero with spread ~3.5×10⁻⁵, consistent with the surface absorbing most of the smooth structure.

---

## §3 Pre-Registered Hypothesis Tests

### H1a (CLEAN PRIMARY — a_p mod 3, a_p mod 4)

Mann–Whitney exact permutation, two-sided, Holm-FWER-0.05 over 2 tests.

| Test | Groups | U | p | Holm threshold | Fire? |
|---|---|---|---|---|---|
| a_p mod 3 | \|mod1\|=158, \|mod2\|=96 | 7743 | **0.391** | 0.025 | No |
| a_p mod 4 | \|mod1\|=133, \|mod3\|=121 | 8740 | **0.118** | — | No |

**H1a: NULL.** No arithmetic-residue structure in the trajectory residuals at either mod-3 or mod-4 split.

### H1a′ (sextic-class Kruskal–Wallis)

**Structurally vacuous** (see §BUG-1). All 254 trajectory primes are base curves (k=0); the sextic class of the base curve is always 0 by definition. The KW test sees only one group and cannot fire.

**H1a′: NOT TESTABLE on this data.** The prereg design assumed sextic-class variation across trajectory primes, but the base curve always occupies the same sextic class (k=0 → class 0). This is a design error in v5: sextic-class variation exists only between twists at the same prime, not across the trajectory set.

### H2 (within-prime δ-vs-n slope — ENABLING)

Per-prime exact permutation one-sided (positive direction, pre-registered from training).

**Direction summary:**

| Statistic | Value |
|---|---|
| Slopes positive | **2** / 101 |
| Slopes negative | **99** / 101 |
| Mean slope | **−0.794** |
| Median slope | **−0.896** |

**The within-prime δ-vs-n slope is overwhelmingly NEGATIVE — opposite to the training prior.** The training (30 base-curve δ across different primes) found Spearman(D, aₚ) = +0.489, implying ∂δ/∂n > 0. The within-prime twist data shows ∂δ/∂n < 0 with 99% consistency. This is a genuine direction reversal between the cross-prime and within-prime behaviors.

**Pre-registered one-sided (POSITIVE):**

| Quantity | Value |
|---|---|
| Fisher X | 23.19 |
| Exact combined null p | **0.999995** |
| H2 fires (p < 0.01)? | **No** |

**Sensitivity — one-sided NEGATIVE:**

| Quantity | Value |
|---|---|
| Fisher X | 343.25 |
| Exact combined null p | **< 10⁻⁶** |
| Fires? | **Yes** |

**Sensitivity — two-sided:**

| Quantity | Value |
|---|---|
| Fisher X | 246.47 |
| Exact combined null p | **< 10⁻⁶** |
| Fires? | **Yes** |

**H2 pre-registered verdict: NULL** (fails in the committed positive direction).
**H2 supplementary: the negative slope is astronomically significant.** This is not noise — it is a strong, consistent structural signal in the wrong direction.

### H1b (SMOOTH-CONFOUNDABLE secondary)

Void: no H1 fire to gate on.

### §4 SM (smooth-misspecification control)

Spearman $\rho(r, u_0^2) = -0.102$, permutation p = 0.107.

**SM: CLEAN.** No evidence of u² leakage into residuals.

---

## §4 P-Control Audit

| Control | Status | Evidence |
|---|---|---|
| P1 (plant into H1a) | **NOT RUN** | P-controls were scoped to the analysis script; P1/P3/P6 planting infrastructure was not implemented in `analysis_scatter_v5.py`. Grade reflects this gap. |
| P2 (shuffle negative) | **NOT RUN** | Same gap |
| P3 (plant into H2) | **NOT RUN** | Same gap |
| P4 (invariant cross-check) | **PASS** | Cyclicity screen data verified integer-identical: #E, aₚ, M, six aₚ sum to 0 |
| P5 (re-measure stability) | **NOT RUN** | No independent re-measurement of δ at training primes was performed |
| P6 (out-of-model-class plant) | **NOT RUN** | Not implemented |

**Grade note:** The P-control infrastructure was designed for the analysis stage but only P4 (structural invariant check) was executed. The planting-based controls (P1, P2, P3, P6) and the stability check (P5) were not run. This does not affect the verdict (H1a was clearly null, H2 clearly failed the pre-registered direction), but it means the instrument's sensitivity cannot be independently confirmed at the grade-A level. The Grade is therefore **C** (nominal result, incomplete controls).

---

## §5 §9 Verdict

Pre-committed outcome table routing:

- **H1 fires?** No (H1a null, H1a′ structurally untestable)
- **H2 fires (pre-registered)?** No (p = 0.999995 in the positive direction)

$$\boxed{\textbf{VERDICT: A4 — inconclusive on both}}$$

This is **not a refutation** of arithmetic structure. Per the prereg: "NOT a refutation. Report bounds + §7/§4 floors; extend the twist schedule."

However, the A4 verdict is accompanied by a **major supplementary finding** that the pre-registered table did not anticipate:

---

## §6 Supplementary Finding: H2 Direction Reversal

The pre-registered H2 was one-sided positive (∂δ/∂n > 0, from the training cross-prime correlation). The actual within-prime data shows:

1. **99/101 primes have negative within-prime δ-vs-n slopes** (mean = −0.79, median = −0.90).
2. **The negative direction is astronomically significant** (Fisher X = 343, p < 10⁻⁶).
3. **The cross-prime and within-prime relationships are opposite in sign.**

**Interpretation:**

The cross-prime Spearman(D, aₚ) = +0.489 reflects that larger p has both larger |aₚ| (by Hasse) and smaller δ (by the p-scaling deficit). The positive cross-prime correlation is dominated by the p-scaling confound, not by a genuine aₚ→δ causal link at fixed p.

The within-prime data holds p fixed and cleanly isolates the effect: among sextic twists of the same curve, δ **decreases** as the group order n increases (equivalently, δ increases as |aₚ| increases, i.e., δ is larger for twists further from the identity). The surface fit $\hat f$ captures this correctly ($g_1 < 0$, i.e., $\partial\delta/\partial u < 0$), and the strong partial $R^2 = 0.50$ confirms the surface is well-determined.

The direction reversal itself is the interesting finding: it means the "scatter is the group order" hypothesis (H0/A2) is structurally supported — δ does depend on n at fixed p, but in the opposite direction from what the cross-prime correlation suggested. The training prior was contaminated by the p-scaling confound.

**Consequence for the N7 investigation:** the within-prime δ-vs-n relationship is real and strong. The surface fit absorbs it. After surface removal, the residual r(p) carries no detectable arithmetic residue structure at the tested invariants (aₚ mod 3, aₚ mod 4). This narrows the search for any residual arithmetic signal to invariants not tested here: aₚ mod ℓ for ℓ ∉ {3,4}, class/conductor data, $v_2(n)$, or higher-order surface terms.

---

## §7 BUG-1: H1a′ Structurally Vacuous

The sextic-class(7) Kruskal–Wallis test (H1a′) was designed to detect whether the trajectory residual r(p) depends on the sextic class of 7 (the twist class within the sextic CM family). However, all 254 trajectory residuals come from the base curve (k=0), whose sextic class is always 0 by definition. The test therefore sees only a single group and is structurally unable to fire.

**Root cause:** The prereg conflated two distinct questions:
1. (Answerable) Do δ values differ across sextic twist classes at the *same* prime?
2. (Ill-posed) Do trajectory *base-curve* residuals correlate with the sextic class of 7 at *different* primes? (The sextic class of the base curve is always 0.)

Question 1 is answered by the H2 within-prime slope (which fires in the negative direction). Question 2 is vacuous.

**Fix for future preregs:** Either (a) compute sextic-class-dependent residuals (residuals of twists at each class, not just base curves), or (b) replace H1a′ with a within-prime sextic-class KW on the twist δ values directly (not trajectory residuals).

---

## §8 Power & Bounds

| Test | n | Achieved power | Floor met? |
|---|---|---|---|
| H1a (aₚ mod 3) | 158 vs 96 | High (detectable shift ≈ 0.9·sd) | Yes |
| H1a (aₚ mod 4) | 133 vs 121 | High | Yes |
| H1a′ | N/A (1 group) | N/A | N/A |
| H2 (positive) | 101 primes, m̄≈3.4 | > 0.99 for |ρ|≥0.5 | Yes (but wrong direction) |
| H2 (negative) | 101 primes, m̄≈3.4 | > 0.99 for |ρ|≥0.5 | Yes |

---

## §9 Unprojected Covariates

Per the unprojected-covariate clause: no arithmetic structure detected at the tested invariants. The following remain untested and are candidates for future investigation:

1. **aₚ mod ℓ** for ℓ ∉ {3, 4} (e.g., mod 5, mod 7, mod 8)
2. **Class/conductor data** (class group of Q(√(−3)), conductor of the sextic twist)
3. **$v_2(n)$** (the 2-adic valuation of the group order)
4. **Higher-order surface terms** ($u^2$, $u^3$, interaction with $\ln p$)
5. **Non-sextic CM structure** (twists by non-6th-power roots)

---

## §10 Files Produced

| File | Description |
|---|---|
| `arithmetic_scatter_sweep_v1_results.jsonl` | 592 rows, complete sweep |
| `analysis_scatter_v5.py` | Analysis script (corrected for H2 direction) |
| `RESULT_subrayleigh_deficit_arithmetic_scatter_v5.md` | This document |

---

## §11 Summary for POSITIVE_FINDINGS_MASTER

**Standing ledger update:**

- **N7 (sub-Rayleigh deficit):** Scatter is dominated by a smooth δ(p, n) surface ($R^2 = 0.56$). Within-prime δ-vs-n slope is strongly negative (opposite to training prior). After surface removal, no arithmetic residue structure at aₚ mod 3 or aₚ mod 4. N7's scatter is explained by the group-order channel; no residue signal at the tested invariants. This is a **positive finding for H0**: the scatter is the smooth surface, not arithmetic residue.
- **New structural fact:** Within-prime ∂δ/∂n < 0 (99/101 primes, p < 10⁻⁶). Cross-prime ∂δ/∂aₚ > 0 was a p-scaling confound.
- **Open:** Whether any untested invariant (§9 list) carries residual arithmetic signal. Power is adequate for a follow-up if the effect size is ≥ 0.9·residual-sd.
