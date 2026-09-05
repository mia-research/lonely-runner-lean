# PREREG — Semaev per-prime yield excess vs Frobenius/Weil channel (P1)

**Date:** 2026-08-14 · **Status:** PRE-REGISTERED (no verdict) · **Object data:** EXISTING R1 only
**Source data:** `RESULT_semaev_cm_relation_yield_v4.md` §3 (T1(j0) per-prime, V=6,7,8) +
`_SCHEDULE_semaev_cm_relation_yield_v4.json` (curve (p,b)). No new Semaev runs.
**Gate:** this is itself the pre-registration artifact.

Hypothesis under test: the per-prime modulation of the CM Semaev relation-yield excess
`T1(j0)[p]` (mean over matched pairs of `logQ_CM − logQ_nonCM`, #E matched within pair) is a
Frobenius/Weil character-sum effect — its lower-order term is controlled by the curve's Frobenius
`π ∈ ℤ[ω]` (N(π)=p). If so, `T1(j0)[p]` should track a CM/Frobenius invariant computable from
`(p,b)` alone, and *not* be explained by #E (matched) or by p.

---

## 0. DECIDABILITY / CONFOUND LAYER (done pre-run; uses ONLY (p,b), never T1 or Q)

All 24 j0 cells in the frozen schedule are **A=0, B=1** — the j0 curve is `y²=x³+1` at *every*
prime (verified: schedule order == brute point-count of `y²=x³+1` for all 24 primes). Consequences,
per candidate invariant named in the hypothesis:

| Cand. | invariant | computable from (p,b) w/o T1,Q? | across-prime variance | Spearman vs #E(j0) | Spearman vs p | verdict |
|---|---|---|---|---|---|---|
| (i)  | sextic residue class of b = b^((p−1)/6) | yes | **b=1 ⇒ ≡1 for all p, ZERO variance** | undefined | undefined | **REJECT — degenerate** |
| (iv) | cubic residue class of b | yes | **b=1 ⇒ ≡1, ZERO variance** | undefined | undefined | **REJECT — degenerate** |
| (ii) | arg(π) mod 60° (oriented, Im>0 conv.) | yes | 24 distinct | **−0.221** | −0.359 | secondary (conj-DOF, #E-linked) |
| (iii)| J(χ₆,χ₆): **real part** 2·Re(J) ∈ ℤ | yes | 24 distinct | **+0.102** | +0.095 | **PRIMARY** |
|      | arg(J) mod 60° (oriented) | yes | 24 distinct | +0.359 | — | secondary (most #E-confounded) |
|      | folded angle min(arg π%60,60−·) | yes | 24 distinct | +0.120 | — | secondary (conj-free) |

Facts established in this layer (all exact / integer):
- `|J(χ₆,χ₆)| = √p` exactly (max deviation 6e−14) — normalization confirmed.
- **`2·Re(J(χ₆,χ₆)) ∈ ℤ`** exactly (Re(J) is a half-integer). Signal path is float-free.
- `2·Re(J)` is **generator-independent** (recomputed with a 2nd primitive root: max |diff| = 0)
  and **conjugation-invariant** (Re unaffected by χ₆↔χ̄₆) ⇒ **zero researcher DOF**.
- arg(π) mod 60° is **invariant across all six sextic twists of b** (multiplying b by a sextic
  nonresidue rotates π by 60°), so fixing b=1 loses *no* sextic-angle information; but the
  **oriented** angle carries a conjugation DOF (arg π vs arg π̄), which `Re(J)` does not.
- #E(j0) and p are near-collinear here (Spearman 0.914; #E≈p+1 in a narrow band), so controlling
  for #E ≈ controlling for p.

**Decidability verdict:** (i),(iv) are **not testable** (no variation) and are dropped. (iii)-real
part `W := 2·Re(J(χ₆,χ₆))` is exact, canonical, non-degenerate, and **the least #E/p-confounded**
candidate (+0.10 / +0.09, negligible) → it is the PRIMARY. (ii) and the angle variants are
demoted to SECONDARY (they realize the same Frobenius phase but with a conjugation DOF and/or
stronger #E linkage).

---

## 1. OBJECT

- **Target:** the per-prime scalar `T1pool[p] = mean over |V|∈{6,7,8} of T1(j0)[p,|V|]`, read from
  `RESULT_...v4.md` §3 (24 primes). This is a real, #E-matched-within-pair yield log-ratio.
- **Feature (primary):** `W[p] = 2·Re(J(χ₆,χ₆))` over F_p, an integer function of p alone (b=1).
- **Disjointness:** W is computed from p via a discrete-log/Jacobi-sum, with **no reference to
  T1, Q, decompositions, or #E**. Feature and target share no construction ⇒ not a tautology.
  (Contrast the r=v−w tautology in memory: here the feature never sees the target's ingredients.)
- **What W is NOT:** it is not #E and not a proxy for #E (confound +0.10). If the primary fires and
  survives #E/p control, the association is "beyond #E," as the hypothesis requires.

## 2. STATISTIC (exactly one)

- **Primary statistic:** two-sided **Spearman rank correlation** between `W[p]` and `T1pool[p]`
  over the n=24 primes, reported as the integer footrule `S = Σ_i d_i²`, `d_i = rank_W(i) −
  rank_T1(i)` (ranks 1..24; ties → average ranks, none expected).
- **Null distribution of S:** the exact permutation distribution of S under random relabeling of
  primes → invariant (Section 3).
- Why rank/Spearman and not a max-over-cells: a single pooled ordinal association aimed at the
  monotone `Re(J)` channel; no max over noisy cells (which would be upward-biased, low power).
- **Aim / subspace caveat:** the mechanism's leading real correction is taken ∝ `Re(J)` (the count
  is real ⇒ its leading Jacobi-sum correction is the real part; J, not Jᵏ, is the natural m=3
  sextic object). If the true correction lives in `Re(Jᵏ), k≥2`, or in the **oriented** phase
  (Im(J) / arg mod 60°), this primary has reduced power there — a primary null is scoped to the
  `k=1` linear-in-Re(J) channel and the secondaries (Section §2-sec) probe the orthogonal pieces.

**Secondary set** (report only; NEVER decides the verdict), Bonferroni α_sec = 0.05/4 = 0.0125:
S1 = arg(π) mod 60° (Im>0, frozen); S2 = folded angle min(argπ%60, 60−argπ%60);
S3 = arg(J(χ₆,χ₆)) mod 60° (flag: most #E-confounded, +0.36 — an S3-only hit is a #E-artifact
candidate); S4 = Im(J)/√p (oriented imaginary part). A secondary firing with the primary null is
an **EXPLORATORY lead requiring its own prereg**, not a verdict.

## 3. MATCHED CONTROL (the null)

- **Permutation:** hold the multiset `{T1pool[p]}` and the multiset `{W[p]}` fixed; permute the
  bijection primes→W (equivalently, shuffle W-labels across the 24 primes). Recompute S.
- **Preserves:** the full heterogeneity/marginal of T1pool (its per-prime spread), the full
  marginal of W **including its own +0.10 #E-confound and +0.09 p-confound** (these travel with
  the W values under relabeling), n=24, all rank structure.
- **Destroys:** only the specific `W[p]↔T1pool[p]` coupling — exactly the tested association.
- **Exact p-value (integer):** `N = 200000` relabelings, fixed seed `20260814`;
  `p_perm = (1 + #{perm : |ρ_perm| ≥ |ρ_obs|}) / (1 + N)` — an integer ratio; the comparison uses
  integer S (no float threshold decides). Two-sided.
- **Mandatory confound robustness (pre-committed):** partial-Spearman of (T1pool, W) controlling
  for **#E(j0) and p**. Because W's confounds are <0.11, this is expected ≈ raw; the rule in §6
  uses it to separate a clean Frobenius result (Outcome A) from a #E/p-driven one (Outcome B).
- **Diagnostic (uses T1, part of the run not the prereg layer):** report `Spearman(T1pool, #E)`
  — the hypothesis predicts this is weaker than the W-association ("beyond #E").

## 4. PLANTED CONTROL (positive; the test MUST fire)

- **Positive plant:** `W_synth[p] = rank(T1pool[p]) + η[p]`, η deterministic (seed 20260814),
  variance scaled so `Spearman(W_synth, T1pool) = 0.60 ± 0.03`. Run the identical pipeline.
  **Requirement:** `p_perm ≤ 0.05`. (Power at ρ=0.60 is ≈0.86 — see §5.) **If the plant does not
  fire, the null is uninformative — HALT, do not report a primary verdict** (Outcome D).
- **Negative calibration:** 1000 iid-random "invariants"; empirical fire-rate must be ≈0.05 (±0.01),
  confirming no inflation.

## 5. POWER

- n = 24. Exact permutation, α=0.05 two-sided ⇒ critical `|ρ_s| ≈ 0.405` (perm-exact, 200k draws).
- Power (Monte-Carlo, Gaussian-copula latent): ρ=0.40→0.46, 0.45→0.56, 0.50→0.67, **0.55→0.77,
  0.60→0.86**, 0.70→0.96. **MDE(80%) ≈ ρ_s = 0.56.** Significance boundary ρ_s≈0.41 (~50% power).
- **Consequence for reading a null:** the test cannot reliably detect `|ρ_s| ≲ 0.4`. A null is
  therefore SCOPED to "no monotone linear-in-Re(J) association of size ρ_s ≳ 0.56"; it is **not**
  "no Frobenius mechanism." A magnitude is a size, not an absence.

## 6. SCOPE · FALSIFICATION · PRE-COMMITMENT

**SCOPE (inherited by every number produced):** 24 primes p≡1 mod 3, p∈[523,823]; j0 curve
`y²=x³+1` (b=1, a **single** sextic twist — cross-twist sextic modulation is UNSAMPLED); m=3;
|V|∈{6,7,8}; T1(j0) from R1 (`RESULT_...v4.md` §3). Nothing extrapolates to secp / 2²⁵⁶.

**Pooling (item 4):** primary uses the single pooled per-prime statistic `T1pool = mean over
|V|∈{6,7,8}`, one Spearman test — NOT Stouffer across |V|, because the three |V| columns are
strongly correlated (nested factor bases, same curves) and Stouffer's independence assumption
would inflate significance. Per-|V| Spearman (3 tests, Bonferroni α=0.0167) is reported as a
sign-consistency diagnostic only.

**FALSIFICATION (written before the run):** primary `p_perm > 0.05` with the firing control fired
⇒ the hypothesis is falsified **at this scope and for the linear-Re(J) channel** — it is NOT a
closure of the Frobenius/Weil mechanism (see Outcome C).

**EXACTNESS:** primary signal path is integer-only: discrete-log table (int) → sextic counts (int)
→ `W=2·Re(J)` (int) → ranks (int) → `S=Σd²` (int) → permutation p-value (integer ratio). **Float
carve-out:** (a) the R1 T1 log-ratios (analytic-size, pre-computed, gated in v4) enter **only** as
the rank order of 24 primes — no key/target material, monotone-size use only; (b) secondary
invariants S1–S4 use trig/√p floats but rank only and never decide the verdict. Primary decision
path touches no float except the T1 pre-ranking.

**PRE-COMMITMENT TABLE (fill-in fixed before any computation):**

| # | Condition | Conclusion (pre-committed) |
|---|---|---|
| **A** | primary p≤0.05 · plant fired · partial(#E,p) keeps \|ρ\|≥0.405 | **SUPPORTED.** Per-prime T1(j0) modulation tracks the sextic-Jacobi phase Re(J), unconfounded by #E/p → consistent with a Frobenius/Weil character-sum mechanism. Association **form** is scale-free (W defined ∀p); detected **magnitude** is scoped to p∈[523,823], m=3, \|V\|∈{6,7,8}. **No secp/ECDLP claim.** |
| **B** | primary p≤0.05 · plant fired · partial(#E,p) drops \|ρ\|<0.405 | **CONFOUNDED.** Association is carried by #E/p, not a clean Frobenius channel. Report as scoped; open a follow-up isolating the #E-orthogonal component. |
| **C** | primary p>0.05 · plant fired | **NULL, SCOPED.** Not a monotone linear-in-Re(J) effect at MDE ρ_s≈0.56 within scope. **Not** a closure: untested subspaces = Re(Jᵏ) k≥2, oriented Im(J)/arg mod 60°, and (because b is fixed) the entire cross-twist sextic modulation. Secondaries (§2-sec) reported as exploratory leads. |
| **D** | plant did NOT fire | **UNINFORMATIVE.** Test lacks power at n=24; no primary verdict. Redesign (more primes / sharper statistic) before any claim. |

Only the **primary** (W = 2·Re(J(χ₆,χ₆))) decides A/B/C/D. Secondaries and the per-|V| breakdown
are diagnostic; a secondary hit under a primary null routes to a NEW prereg, never to a verdict here.
