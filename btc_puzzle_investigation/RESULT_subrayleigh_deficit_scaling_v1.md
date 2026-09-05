# RESULT — sub-Rayleigh deficit p-scaling: PERSISTENT (not finite-size), model range

**Date:** 2026-08-04. Executes `PREREG_subrayleigh_deficit_scaling_v1.md` (FROZEN, SHA-256
`93c954713d3a49444ee9e234a2a20b21fdec44cc5f0babb0bdce8a618894f293`, recorded pre-data).
Scripts: `subrayleigh_deficit_scaling_v1.py` (exact signal path), `analyze_scaling_v1.py` (frozen §9).
Deviations: `PREREG_subrayleigh_deficit_scaling_v1_DEVIATIONS.md` (D1 prereg numeral slip, no effect;
D2 planted-P3 prime-dependent; D3 smoke observed 3 primes).
This is the S2 re-test of `RETROSPECTIVE_FINDING_01_subrayleigh_demotion_v1.md`.

**Grade: `[EMPIRICAL — 30 primes, pre-registered, replication gate PASS]`** for the deficit's reality;
**level-1 PERSISTENT `[decided, robust]`**; **level-2 const-vs-1/log p `[ABSTAIN — a finding, not a
closure]`**. **Model scale only** (p ∈ [151, 12043], E: y²=x³+7); **no transfer to cryptographic p is
claimed or implied** (prereg §0, absolute).

---

## 1. The result (all 30 frozen primes, no post-hoc cell/subset selection)

| gate / statistic | value | frozen requirement | verdict |
|---|---|---|---|
| Replication (Stouffer Z) | **−71.80** | ≤ −5 | **PASS** |
| One-directional | **30/30 negative, 0 flips** | ≥27/30, ≤3 flips | **PASS** |
| Per-prime z range | −0.37 (p=211) → **−51.86** (p=12043) | grows with p | as prior |
| E1 exact Parseval `Σ|U|²=p²(n−1)` | relerr ≤ 8.5e-16 all 30 | ≤1e-6 | **PASS** |
| Pooled slope s_hat (weighted LS, ln D vs ln p) | **−0.0341**, σ_s=0.0307 | — | — |
| s_hat ± 2σ_s | **[−0.0954, +0.0273]** | vs s_loglog=−0.1412 | above ⇒ **PERSISTENT** |
| Model χ² (lower=better) | const **6106** < 1/log p 8327; power 5705 | — | const beats 1/log p |
| Curvature k2 | **+0.021 (z=+12.4)** | — | 1/log p signature ⇒ guard |

**Level-1 — PERSISTENT vs FADES: PERSISTENT, decisively.** The entire 2σ slope band [−0.095, +0.027]
is shallower than the 1/log p slope (−0.141) and nowhere near 1/√p (−0.5, excluded at ≫8σ) or 1/n. The
deficit **does not decay** across a 79× range in p. `U2 = +0.027 ≥ s_loglog` — FADES is falsified.

**Level-2 — const vs 1/log p: ABSTAIN.** The tree's literal leaf is CONST (L2=−0.095 > s_loglog;
k2 not negative; χ²_const ≤ χ²_loglog). **But** k2 is significantly *positive* (z=+12.4) — positive
curvature in ln D vs ln p is the algebraic signature of 1/log p, opposing the const slope-verdict; and
χ²_red = 204 shows neither smooth model captures the large prime-to-prime **arithmetic scatter**. Per the
prereg's **contradiction guard**, this downgrades to **UNRESOLVED_PERSISTENT**: persistence established
(decay no faster than 1/log p); the const-vs-1/log p refinement is not cleanly separated at this
schedule. *This abstention is a pre-committed finding, not a closure.*

## 2. What this establishes — and what it overturns

- **The sub-Rayleigh deficit is a real, persistent, model-range structural property** of the E+character
  system: 30/30 primes, Stouffer −71.8, one-directional, no decay. `mean|U|` for the arithmetic
  character weight is systematically below a matched Hermitian-symmetric null by ~0.1%, and that gap
  **does not shrink with p** across [151, 12043].
- **It is NOT a finite-size artifact.** This is the sharp contrast with N1/the ½-saturation
  (`n1_saturation_residual_v1`), which *was* finite-size (deficit ∝ p^−2/3, a max-statistic edge
  effect). The mean|U| deficit is the opposite: scale-flat. A finite-size explanation is **excluded** at
  the model range by the slope band excluding every decay law.
- **The demotion is confirmed wrong to that extent.** Master v4 dropped this object (Frontier #17,
  `RETROSPECTIVE_FINDING_01`). A dropped −13.99σ effect is now a dropped, *pre-registered,
  replication-gated, persistent* effect. **Signal recovered.**

## 3. Matched-null integrity (the wrong-null lesson honored)

The null carries the forced Hermitian symmetry g(n−d)=conj(g(d)) (prereg §3), the exact structure a
prior wrong-null omitted. E1 (exact integer Parseval) passed at every prime; the signal path (EC group
law, indices, coordinates) is exact Python int, with the sanctioned roots-of-unity float carve-out
(error ≤1e-12 ≪ deficit 1e-3, common-mode-cancelling — prereg §8). The instrument is accurate (M linear
in |U| ⇒ exact recovery of a planted δ); the planted-P3 |z|≥3-at-every-prime clause is prime-dependent
and met only where the effect's own |z|≥3 (D2 deviation).

## 4. Scope (binding on every number above)
E: y²=x³+7 only; the 30 frozen primes 151…12043; a₀=1; all p² frequencies, no exclusions; matched
Hermitian null, K(p)∈{300,200,100,50}. **"Persistent" = across the enumerable model range under the
fitted form — NEVER a statement about p ≈ 2²⁵⁶** (prereg §0). The mechanism is still open
(4th-moment and axis-locus refuted earlier; row-budget shadow active in `row_budget_lowtail_v3`).

## 5. Not run here (each its own prereg)
- Secondary X1 (subspace strata {b=0},{c=0},{b=c}) and X2 (all-character a₀∈{1..10}) — the sweep
  computed only the primary M over all (b,c). Named, not run.
- The mechanism (why the character's harmonics carry an ~8% near-zero excess) — open, active elsewhere.
