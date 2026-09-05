# RESULT — the interval char-sum is indistinguishable from random points; Stage A's low-tail was the bootstrap artifact

**Date:** 2026-08-02. **Script:** `shortscalar_interval_vs_random_characterize_v1.py`
(background task `bq4af5tea`, exit 0, 1653s). **Log:** `interval_vs_random_char_v1.log`.
**Read against the pre-committed yardstick** `ANALYSIS_interval_charsum_generic_prediction_v1.md`
(written before the L=80000 row existed).

**Grade: `[EMPIRICAL — earned; located artifact + scoped bound]`.** This is the test I had SKIPPED,
whose absence the bias audit flagged. It **retracts** the pre-judged label *"generic/near-artifactual
property"* in `RESULT_shortscalar_sum_stageA_v1.md` §4 and `..._v2.md` §4 — replacing an unearned
prior with tested evidence.

---

## 1. The test (artifact-immune by design)
Real consecutive intervals `{[s]G}` vs. **real fresh random L-point sets** `{[r]G}` — both actual
point sets, **no bootstrap** (so no pool-imbalance artifact), differing only in scalar-consecutiveness.
Statistic E₂/E₃/E₆/D₆ = |Σχ|² (exact integer). Robust comparison: Mann-Whitney `P(int<rand)`.
**Power controls fired:** φ-closed `P(φ<rand)=1.000` (low), planted-5% `P=0.000` (high) — the
instrument provably distinguishes real differences, so a null here is not null-by-design.

## 2. The numbers (reported in full, including the misleading medians)
| L | N | readout | int-med | rand-med | ratio | P(int<rand) | z |
|---|---|---|---|---|---|---|---|
| 5000 | 40 | E3 | 2575 | 2479 | 1.04 | 0.488 | −0.2 |
| 20000 | 30 | E3 | 11284 | 15271 | 0.74 | 0.614 | +1.5 |
| 80000 | 20 | E3 | 76339 | 46567 | 1.64 | 0.482 | −0.2 |

The **median ratios wobble** (E3: 1.04 → 0.74 → 1.64; E2 swings 0.44 → 3.27) — heavy right tail at
N=20–40. The **rank statistic is flat at ≈0.5 across all three L with no trend** (E3 P = .488/.614/.482;
all readouts within [0.41, 0.61], |z|<1.5). No systematic direction, no growth.

## 3. Verdict — generic mixing confirmed, artifact located
- The "REAL structure" signature (ratio≪1 **consistent** + P→1 **growing** + z≳3) is **absent**.
- The test is well-powered (5% plant fired hard); Stage A's **5–25×** effect, if real, would be
  unmissable. It is not present against a real-random null.
- ⇒ **Stage A's 5–25× low-tail was the bootstrap-null inflation** (with-replacement draw baking the
  pool's finite-sample class imbalance into an `L²δ²` mean), **not** real interval structure and
  **not** equidistribution. The interval character sum is **pseudorandom** — the standard generic
  prediction, now empirically confirmed rather than hand-waved.

## 4. Scope (Rule 5 — earned bound, not a blanket closure)
- **Earned:** the specific Stage A anomaly (a 500–2500% E₃ gap) is a null artifact. Intervals =
  real-random at L ∈ {5000, 20000, 80000}.
- **Bound, not closed:** the test resolves coherent effects ≳5% (plant threshold). A residual
  sub-≈5% interval effect is **untested** and remains open; there is no trend suggesting one emerges
  at larger L, but this is not a proof of "no structure."
- **Finer probe available (R3):** lag-`d` autocorrelation of the orbit's χ-sequence
  (`PLAN_interval_charsum_realbranch_characterization_v1.md`) would confirm the mixing *mechanism*
  (A(d)≈0) or expose short-range structure the histogram misses — and ties to the group-law
  difference (C2). Not required for §3's verdict; a mechanism confirmation.

## 5. Bias-audit closure
Two things the audit flagged are now discharged with evidence, not prose:
1. The "generic/near-artifactual" label was an **unearned prior**; the earned result is §3.
2. My "equidistribution ⇒ intervals more cancelled" reasoning was **backwards** — for a character
   (non-smooth) readout, generic equidistribution predicts **random-like** behavior, which is what the
   data show (`ANALYSIS_...generic_prediction_v1`). The dismissal reflex was doubly wrong in mechanism
   and is corrected.

## 6. Files
`shortscalar_interval_vs_random_characterize_v1.py`, `interval_vs_random_char_v1.log`,
`ANALYSIS_interval_charsum_generic_prediction_v1.md` (pre-committed yardstick),
`PLAN_interval_charsum_realbranch_characterization_v1.md` (R3 shelved-but-available).
Supersedes the "generic/near-artifactual" phrasing in `RESULT_shortscalar_sum_stageA_v1/v2.md`.
