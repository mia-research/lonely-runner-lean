# G4B-COMP-CAP: Lower Band Universality Test

**Date:** 2026-03-05
**n=6, L_MAX=360, MAX_E=12**

---

## Core Claim

> For every obstruction run in B_div: safe_before (fibers in B_div before the run) ≥ n.
> This implies run_len ≤ B_div − (safe_before) ≤ B_div − n. □

---

## Dataset
- Tuples processed: 93150
- CB violations: **0**
- Total obstruction runs: 56160
- Runs with has_unit=True: 44160
- Runs with has_unit=False (no unit runner): 12000
- Tuples with no unit runner: 17130  (CB ok: 17130)

---

## Q1. Is safe_before >= n for ALL runs? (Lower band >= n claim)

- Runs with safe_before < n (lower band failures): **7320 / 56160**
✗ 7320 runs have safe_before < n. Lower band argument incomplete.
These runs require additional analysis.

## Q2. For unit-runner tuples: safe_before >= min_period?

- Unit-runner runs: 44160
- Runs with safe_before >= min_period: **23520 / 44160**
✗ 20640 unit-runner runs have safe_before < min_period.
The min_period lower bound needs refinement.

## Q3. No-unit-runner tuples: are all B_div fibers safe?

- No-unit-runner runs: 12000
Non-zero runs exist. lb_size distribution: {0: 1440, 2: 480, 3: 1440, 5: 1440, 6: 2520, 7: 240, 9: 240, 11: 1440, 13: 240, 14: 120, 16: 600, 21: 240, 25: 240, 26: 960, 40: 120, 51: 240}
lb_size values: [0, 2, 3, 5, 6, 7, 9, 11, 13, 14, 16, 21, 25, 26, 40, 51]

## Q4. Termination type census

| Type | Count | Pct |
|------|-------|-----|
| z0_or_other | 52560 | 93.6% |
| at_B_div_end | 3600 | 6.4% |

## Q5. Safe-before distribution

| safe_before | count |
|-------------|-------|
| 0 | 3840 |
| 2 | 960 |
| 3 | 1320 |
| 4 | 240 |
| 5 | 960 |
| 6 | 4080 |
| 7 | 360 |
| 8 | 1320 |
| 9 | 360 |
| 10 | 600 |
| 11 | 1800 |
| 12 | 1560 |
| 13 | 240 |
| 14 | 840 |
| 15 | 1080 |
| 16 | 600 |
| 17 | 1320 |
| 18 | 120 |
| 19 | 480 |
| 20 | 480 |
| 21 | 1080 |
| 23 | 1320 |
| 25 | 240 |
| 26 | 2880 |
| 27 | 240 |
| 29 | 1560 |
| 31 | 240 |
| 32 | 960 |
| 34 | 240 |
| 35 | 240 |
| 36 | 1800 |
| 37 | 720 |
| 39 | 600 |
| 40 | 240 |
| 41 | 480 |
| 43 | 120 |
| 45 | 1200 |
| 46 | 1080 |
| 47 | 240 |
| 49 | 240 |
| 51 | 360 |
| 52 | 120 |
| 54 | 120 |
| 56 | 480 |
| 57 | 120 |
| 61 | 240 |
| 62 | 720 |
| 64 | 480 |
| 65 | 960 |
| 66 | 360 |
| 67 | 360 |
| 71 | 720 |
| 72 | 120 |
| 75 | 360 |
| 76 | 480 |
| 77 | 1800 |
| 78 | 240 |
| 83 | 240 |
| 85 | 120 |
| 86 | 120 |
| 87 | 120 |
| 91 | 240 |
| 92 | 840 |
| 99 | 120 |
| 100 | 480 |
| 101 | 120 |
| 104 | 120 |
| 106 | 720 |
| 107 | 600 |
| 112 | 120 |
| 113 | 120 |
| 116 | 600 |
| 117 | 480 |
| 119 | 120 |
| 121 | 120 |
| 122 | 120 |
| 125 | 120 |
| 127 | 120 |
| 133 | 120 |
| 141 | 240 |
| 144 | 600 |
| 152 | 480 |
| 156 | 480 |
| 164 | 240 |
| 166 | 120 |
| 167 | 120 |
| 173 | 240 |
| 177 | 120 |
| 181 | 240 |
| 182 | 120 |
| 186 | 360 |
| 193 | 240 |
| 211 | 120 |
| 232 | 240 |

---

## Analytic Conclusion

### G4B-COMP-CAP Proof Status

CB violations: 0. Lower band failures: 7320.
G4B-COMP-CAP NOT yet fully proved — investigate failures above.

