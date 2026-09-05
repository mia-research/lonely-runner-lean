# RESULT — pow7 population replication: WASH (the AND-gate demotion was correct)

**Date:** 2026-08-04. Executes `PREREG_cside_replication_v1.md` (FROZEN, SHA-256
`c53dced7b50bcb9a2fe8f2d844f9b7887aac985eb534fec5732b57ddff5e2be4`, recorded pre-data).
Scripts: `cside_replication_v1.py` (instrument imported byte-identical from
`cside_pooled_tilt_settlement_v1`). This is the S5 re-test of `RETROSPECTIVE_FINDINGS_LOG_v1.md`.

**Grade: `[EMPIRICAL — WASH, pre-registered, 30 fresh 80%-powered disjoint primes, Gate 0 PASS]`.**
**The pow7 population claim at the originally-claimed density is NOT reproduced.** Model scale only
(orbit level, p ~ 2×10⁴–4×10⁴); no crypto transfer; the channel is not closed (see §4).

---

## 1. Result (all 30 fresh primes, disjoint from the original 28)

| gate / statistic | value | frozen requirement | verdict |
|---|---|---|---|
| Gate 0a instrument-identity | sample_primes == original 36; gcd(7,n−1)=1 on all 28 | must match | **PASS** |
| Gate 0b firing control (g=1.5) | Z_pool = **−7.21** | < −5.0 | **FIRES** |
| Gate 0c negative control | mean Z_pool = **+0.034** | \|·\| < 0.25 | **NULL (unbiased)** |
| control family pow5/pow11/pow13 (2-sided cal p) | 0.181 / 0.313 / 0.488 | > 0.05 each | **stay null** |
| **pow7 primary: Z_pool^F30** | **−0.923** | expected −2.826 if real | far below |
| **pow7 p_fresh (1-sided neg, calibrated)** | **0.178** | REPLICATE <0.025 / WASH >0.159 | **WASH** |
| pow7 sign | 17/30 negative | — | weak, same sign |

**Frozen decision (§9): WASH.** `Z_pool^F30 = −0.923 > −1.0` and `p_fresh = 0.178 > 0.159`. The original
`Z_pool = −2.73` over 28 primes does **not** reproduce on a disjoint set powered at 80% for exactly that
density. It is consistent with the one-lucky-subsample the K=2 AND-gate flagged.

## 2. What this establishes — the audit hypothesis is REFUTED

The S5 suspicion was that the K=2 OOS **AND-gate** had structurally low power against a homogeneous
sub-detection effect (a real Z=−2.73 gives only ≈−1.9/fold, so a real effect would fail the AND-gate
~half the time), so its "not reproduced" might have been a suppression. **The properly-powered
population OOS settles it the other way:** at 80% power for the claimed density, the fresh pooled Z is
**−0.923, not ≈−2.8**. The effect is not there at the claimed density. **The AND-gate's demotion was
correct; pow7 was a subsample fluctuation, not a suppressed real signal.**

This is a calibration result for the retrospective itself: a suspected-suppressed lead, given the fair
fully-powered test the mandate calls for (false positives welcome), **washed**. S2 recovered (real);
S5 washed (correctly demoted). The audit produces both outcomes — it is not manufacturing recoveries.

## 3. Honest near-boundary scope (neither inflated nor over-closed)

`p_fresh = 0.178` sits just past the 0.159 WASH/ABSTAIN boundary, and the sign is weakly negative
(17/30). Per the prereg's own power analysis, this design was powered **only for the full claimed
density** (μ_z=−0.52); it has 29% power at half-density (μ_z=−0.26). So the honest statement is: **not
reproduced at the claimed density; any residual effect is ≤ ~1/3 of the claimed size, which this test
cannot separate from noise.** Resolving whether a much-thinner effect exists would owe M ≈ 118 fresh
primes (pre-registered as the ABSTAIN-zone debt) — but that is a *different, weaker* claim than the one
tested, and nothing here supports promoting it.

## 4. Scope / what is NOT closed
- Orbit level, p ~ 2×10⁴–4×10⁴, the pow7 index map, this instrument. **No crypto-p transfer.**
- The channel is **not** closed: the operationally-decisive form is the shortscalar arm at 2¹²⁸
  (`PREREG_incomplete_shortscalar_v2`), gate-blocked and untouched here (settlement §6). A sub-half-
  density orbit-level effect is untested (owes M≈118). "Not reproduced on this set" ≠ "inert at 2²⁵⁶".

## 5. Deviations
- **R = 2000** (settlement's byte-identical value), not the prereg's R=20000 — R sets only the per-prime
  null resolution, not the statistic or the pooled thresholds; 20000 would need 800 MB/map arrays.
  (`PREREG_cside_replication_v1` freezes R=20000; recorded as the one instrument-parameter deviation.)
- Fresh scan reached p=38431 (prereg estimated ~26000); qualifying density ran ~1/53 not ~1/40. All 30
  fresh primes are disjoint from the original 28 and Q-valid; M=30 and the design are unaffected.
