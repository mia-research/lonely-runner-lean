# Predictions — Pre-Registered Before Experiments Run
# Date: 2026-03-21
# Source dataset: results_v1.csv (9163 configs, seeds 42/99/137/271/314/577/1000/2718/3141)
# All experiments below use ONLY seeds not in the source dataset.

---

## P1 — Overall L=0 rate: 23–26%
**Basis:** Observed 24.65% in source. Number-theoretic independence estimate gives 16.4%–38.9%
depending on p1 distribution. Observed > estimate (non-uniform residues). Predict replication
within ±2% of 24.65%.
**Falsification:** rate outside [22%, 27%] on fresh 5000-config dataset.

## P2 — L=0 rate by p1 (fresh data, n≥500 each)
| p1 | Predicted rate |
|---|---|
| 1 | 40–46% |
| 2 | 26–30% |
| 3 | 23–27% |
| 4 | 20–25% |
| 5 | 19–24% |
**Basis:** p1=1 condition is "no speed divisible by 11" — clean number-theoretic.
**Falsification:** any row outside predicted band.

## P3 — Zero configs with min containment margin < 54% of |W₀|
**Basis:** Observed minimum is exactly 54.5455% = 6/11, achieved only by pacemaker (1,3,...,10,11).
This config is deterministic — it always gives 54.5% regardless of sampling. No random config
has ever beaten it. The mechanism (Theorem 10.12 forces witness to slot j*=5) means no random
config can produce a tighter margin.
**Falsification:** any config with min_containment_pct_W0 < 54.0%.

## P4 — Max L = 20, never exceeded
**Basis:** Observed across 9163 configs. L=20 is determined by the pacemaker miss-2 config
(deterministic). No random config has come close (max random L=14).
**Falsification:** any config with L > 20.

## P5 — Lemma 10.C never violated: max_advance / (2/(11*p2)) < 1.0
**Basis:** Observed max ratio = 0.9982 across 9163 configs. Zero violations.
**Falsification:** any ratio > 1.0001 (allowing floating point tolerance).

## P6 — Witnesses in first 5% of W₀: 94–97%
**Basis:** Observed 95.9% in source. Expect slight variation with different seeds.
**Falsification:** rate outside [92%, 99%].

## P7 — Carry-free advance rate: 50–60%
**Basis:** Observed 54.6% zero-carry configs (including L=0) and 55% carry-free advances.
**Falsification:** carry-free advance rate outside [48%, 62%].

## P8 — L ≥ 15 only when p2/p1 ≤ 3.0
**Basis:** Hard ceiling observed: all L≥15 have p2/p1=3.0 exactly (pacemaker).
**Prediction:** This should hold exactly on any dataset — it follows from the structure of
the pacemaker grid (p2=3*p1 with p10=11*p1 is the only path to L≥15).
**Falsification:** any config with L≥15 and p2/p1 > 3.0.

## P9 — Pacemaker ratio-11 configs: L is determined by missing speed m
**Basis:** From the source, L for pacemaker (p1=1, p10=11, missing m) is:
m=2→L=20, m=3→L=13, m=4→L=9, m=5→L=7, m=6→L=5, m=7→L=4, m=8→L=3, m=9→L=2, m=10→L=1.
**Prediction:** These L values are DETERMINISTIC — every instance of these 9 configs will
give exactly the same L (different p1 values just scale the problem).
**Falsification:** any pacemaker config (p10=11*p1, missing speed m) giving different L.

## P10 — L decreases as pacemaker order increases (ratio = 11k, k≥2)
**Basis:** Observed max L by pacemaker order: k=1→20, k=2→12, k=3→6, k=4→5, k=5→5.
**Prediction:** Pattern is approximately L_max(k) ≈ 20/k (or similar decreasing function).
For k=6 (ratio=66): predict max L ≤ 4. For k=7 (ratio=77): max L ≤ 4. For k=10: max L ≤ 3.
**Falsification:** max L for k=6 exceeds 5.

## P11 — Type-W carry fraction increases with ratio
**Basis:** Observed 31.9% W-fraction at ratio 10–20, rising to 38–39% at ratio 100+.
**Prediction:** This gradient holds on fresh data. Configs at ratio 500+ will have
W-fraction ≥ 36%.
**Falsification:** W-fraction at ratio 500+ below 33% on fresh data.

## P12 — p2/p1 is uncorrelated with L (Pearson |r| < 0.05)
**Basis:** Observed r(p10/p1, L) = -0.005, r(p2/p1, L) = 0.024. Neither simple ratio
predicts L.
**Prediction:** Both correlations remain near zero on fresh data.
**Falsification:** |r| > 0.10 for either predictor.

## P13 — L=0 rate is stable across ratio bins (all within ±3% of each other)
**Basis:** Observed range 23.9%–26.6% across all ratio bins. Essentially flat.
**Prediction:** On fresh data, no ratio bin deviates more than 3 percentage points
from the overall L=0 rate.
**Falsification:** any ratio bin with L=0 rate outside [overall_rate ± 3%].
