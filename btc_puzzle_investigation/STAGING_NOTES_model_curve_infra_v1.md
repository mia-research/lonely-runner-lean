# STAGING NOTES — shared model-curve infrastructure (v1)

**Date:** 2026-08-21. **Status:** infrastructure staged + self-tested; **no confirmatory
statistic computed** (gates still pending). Module: `model_curve_infra_v1.py`
(`--selftest`, `--schedule DIR`). No-float check: **`check_no_float.sh` OK.**

Serves the three model-curve preregs: A-joint (`PREREG_cm_jointset_excess_v1.md`),
C-center (`PREREG_monodromy_center_glv_ratio_v1.md`), D-mechanism
(`PREREG_omega_twisted_lefschetz_120deg_v1.md` — verdict HOLD, no run; see that file).

## What is staged (gate-safe: neutral primitives + public selection only)
- Exact int/GF(q) curve arithmetic (add, double, mul, neg, is_on, j-invariant), exact
  `point_count` (QR-sieve), generator finder.
- `chi3` cubic-residue index; `semaev_s3` third summation polynomial.
- Deterministic SELECTION: `select_j0_prime_order` (B-witness), `select_j1728_cofactor2`,
  `select_jgen` (ordinary, `j∉{0,1728}`, `|t²−4q|≥⌊√q⌋`, order-matchable); GLV `(β,λ)` with
  `[λ]G=(βx,y)` verified per arm.
- Self-test KATs (all pass): point_count vs brute force + Hasse; add associativity/inverse;
  j sentinels; chi3 multiplicativity (200 pairs); Semaev S3 60/60 true relations vanish,
  1/300 random triples (generic-nonzero); GLV `[λ]G=(βx,y)`, `β³=1`, `λ³=1`.

## Frozen schedules (`schedules_v1/`, SHA-256 sidecars)
- `schedule_A_joint_v1.json` — SHA `a03f7217…f087c9`. discovery q∈{541,547,571};
  confirmation {2029,2053,2089}; ladder {1033,4111,16417,65539}. (2089,547 etc. reuse the
  existing model-curve set.)
- `schedule_C_center_v1.json` — SHA `1c039933…131769`. Full 1-mod-12 band + the runnable
  `arm_available` subset (see Finding 1).

## Finding 1 — C-center's runnable set is a strict subset of its frozen band
All three arms (J0 cofactor-1 prime-order **and** J1728 cofactor-2 prime-part; JGEN always
exists) co-exist at only:
- **discovery: 6/10** — {37, 61, 73, 97, 181, 229}. (109, 241 lack the J1728 cof-2 arm;
  157, 193 lack a prime-order J0 twist — ~26% of primes have no prime-order j=0 sextic twist.)
- **confirmation: 12/25** — {349,397,421,433,457,541,577,661,673,757,853,877}.

Consequence for the C-center run: the verdict `Δ₃` pools over these primes, not the full band.
Pooled cell count is `Σ (N_J0−1)/6` minus filtered cells over ~18 primes — consistent with the
prereg §5 estimate (several hundred–low 10³), but the runner must key off `arm_available`, not
`band`. Not a prereg deviation (the prereg already says the runner filters by arm existence);
recorded so the pooled-`n` and the F-VOID cofactor logic are set against the right denominator.

## Finding 2 — the B-witness rule is biased toward ANOMALOUS (trace-1) curves
"Smallest `B` with prime order" preferentially selects curves with `N = q` (trace `t = 1`),
because `N = q` is automatically prime. Anomalous instances in the frozen schedules:
- **A-joint:** q=547 (N=547, t=1). [541,571 and all confirmation/ladder primes are non-anomalous.]
- **C-center discovery:** p=37 (N=37), p=61 (N=61). [confirmation set: none.]

**This matters for A-joint and must be handled before its run.** An anomalous curve admits
Smart's formal-group/`p`-adic-log attack: `d` is recoverable per-point in linear time. If the CM
arm is anomalous while the matched non-CM arm is not, the "joint synergy" on that arm is
dominated by a per-point anomalous leak, not by CM joint structure — a direct confound of the
CM-vs-non-CM contrast `Δ`. **Recommended runner refinement (feed to A-joint DEVIATIONS):** the
B-witness rule adds "`AND t ≠ 1` (exclude anomalous)"; equivalently match anomalousness across
arms. This drops q=547 from A-joint discovery (next non-anomalous j0 prime-order q>500 backfills).

For C-center the concern is weaker (the statistic is on the twisted sheaf `L_{χ₂(y)}⊗χ_a`
eigenvalues, not the curve's own trace), but p=37,61 anomalousness is logged in case the center
readout interacts with it; the runner should report `Δ₃` with and without the anomalous primes.

## Owed before any run (unchanged by staging)
- A-joint / C-center each: the second independent `experiment-designer` read named in their own
  "owed gates" before any Δ promotes; plus A-joint's `citation-verifier` on the S₃ definition and
  the KS floor used in its §5.
- Implementation runners (`cm_jointset_excess_v1.py`, the C-center runner) are NOT written; this
  module is their shared import layer only.
