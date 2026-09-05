# RESULT — the sub-Rayleigh tail LOCALIZES to the y-only (b=0) axis (k≈1); x-axis and c=±b diagonal are Rayleigh. CORRECTS the pooled T1b.0.

**Date:** 2026-08-11. **`[PROVISIONAL characterization]`** (gate-free distributional-shape fit; the
broader Track-1 verdicts are gate-pending). **Corrects the pooled reading of
`RESULT_t1b0_tail_exponent_v1.md`** (its k≈1.4 was a geometry MIXTURE, not a curve-global exponent).
**Artifact:** `scratchpad/t1b_tail_split_v1.py`. Float carve-out: |U| magnitudes, integer args in the
sum, no key in the arg path, no matched-null verdict.

## What was measured
Tail exponent `k` in `P(|U(a,b,c)|/√n < ε) ~ ε^k`, `a≠0`, fit SEPARATELY per (b,c) geometry class
(pooled over the free index within each class). Rayleigh ⇒ k=2; real/1-D trace ⇒ k=1.

| p | axis c=0 (x-only) | axis b=0 (y-only) | diag c=±b | generic | random ref |
|---|---|---|---|---|---|
| 547 | 2.033 | **1.011** | 1.942 | 1.986 | 1.822 |
| 1303 | 2.070 | **0.951** | 1.940 | 1.912 | 2.004 |
| 2089 | 2.115 | **0.990** | 1.919 | 2.015 | 2.003 |

## Reading (localized find; mechanism a hypothesis; deficit untouched)
- **The sub-Rayleigh tail is entirely on the y-only (b=0) axis, k≈1** — a real, robust (3 curves),
  1-dimensional-type magnitude tail on `U(a,0,c)=Σ_d e_p(c·y_d)e_n(ad)`. **x-only axis and the c=±b
  diagonal are Rayleigh (k≈2)**; the random reference calibrates at ~1.9–2.0.
- **This CORRECTS T1b.0:** the pooled k≈1.4 averaged the y-axis (k≈1) with Rayleigh axes/diagonal — a
  mixture, not a global exponent. Do not cite k≈1.4 as a curve property.
- **Mechanism = a hypothesis to test, not a verdict.** The y-axis k≈1 is CONSISTENT with a forced
  1-D structure in the y-sum (y-coords come in `±` pairs; the record's `V(a)=Σχ₂(y)e_n(ad)` is purely
  imaginary at p≡3 mod4). Whether it is FULLY forced is decided by projecting out the forced skeleton
  and measuring the residual — not asserted here in either direction (not "just forced, no leak"; not
  "a leak").
- **The c=±b diagonal is Rayleigh in MAGNITUDE** — consistent with the free/forced lever (magnitude is
  the forced subspace on the diagonal). The diagonal's live probe is the PHASE test (T1a), not magnitude.
- **The −13.99σ deficit is NOT touched by this (CHECK 2).** It survived a shape-preserving null; its
  relation to the y-axis structure is the owed T1b.1, outcome not pre-judged.

## Next (owed)
- **Project out the forced y-structure** on the b=0 axis and re-fit the residual tail: fully forced
  (residual Rayleigh) vs residual structure (a lead). Gate-free characterization → then a pre-registered
  test if a residual survives.
- **T1a** (diagonal phase), **T1b.1** (deficit vs correct-shape null) — via the hardened
  `PREREG_cbpm_phase_deficit_v2` now in the gate.
- Scope: p=547/1303/2089, prime order; 6-point log-log fit (robust claim = the DIRECTION y-axis≈1 vs
  others≈2, not the third decimal).
