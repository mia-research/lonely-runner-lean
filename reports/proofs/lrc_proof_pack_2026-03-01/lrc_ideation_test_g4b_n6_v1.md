# Test 2: Adjacent-Pair Rotation Anatomy — n=6 G4B-COMP-CAP

**Date:** 2026-03-04  
**n=6, L_MAX=360, MAX_E=12**

---

## Parameters
- Tuples enumerated: 93150
- CB violations: **0**
- Total obstruction runs: 56160
- Long runs (len > n−1 = 5): 40200

---

## Q1. Do long runs always terminate at z=0?

- Long runs terminating at **z0_event**: 37920 / 40200
- Long runs terminating at **at_B_div_end**: 2280 / 40200

**Answer Q1:** 94.3% of long runs terminate at z=0.
✗ 2280 long runs terminate at at_B_div_end (boundary truncation). These need separate analysis.

## Q2. Termination type census

| Type | Count | Pct |
|------|-------|-----|
| z0_event | 52560 | 93.6% |
| at_B_div_end | 3600 | 6.4% |

## Q3. gcd(e_terminating, n) pattern at z=0 events

| gcd(e,n) | Count | Pct |
|----------|-------|-----|
| 3 | 22080 | 42.0% |
| 2 | 19560 | 37.2% |
| 1 | 10920 | 20.8% |

**Observation:** z=0 events require (e·b) mod L = 0, i.e., b = m·L/e.
For gcd(e,n) = 1 (unit e): Safe by Lemma S2 (z=0 → delta > 0).
For gcd(e,n) > 1 (non-unit e): z=0 does NOT guarantee safety (may still obstruct).

## Q4. at_B_div_end run analysis

- Total at_B_div_end runs: 3600
- Position breakdown: upper=3120, middle=480, lower=0
- Next z=0 within min_period of B_div end: 3600 / 3600
- Next z=0 exactly 1 step after B_div end: 0 / 3600
- next_z0_dist: min=2, max=30, mean=9.80

**Answer Q4:** at_B_div_end runs are runs cut off by the upper boundary of B_div.
The next z=0 event falls just outside B_div. This is a BOUNDARY ARTIFACT,
not a distinct termination mechanism. These runs are bounded by the top band.

## Q5. Gcd-structured bound: run_len ≤ n · lcm(gcd(e,n) for e∈E_non)

- Runs violating gcd_struct_bound: **15720**
✗ 15720 violations. Hypothesis refuted — need a different bound.

## Top 10 Longest Obstruction Runs

| E | L | B | run_len | gcd_bound | term_type | term_gcd | next_z0_dist | pos |
|---|---|---|---------|-----------|-----------|----------|--------------|-----|
| 1 4 5 6 9 | 180 | 121 | 89 | 36 | z0_event | 2 | 0 | lower |
| 1 4 5 6 9 | 180 | 121 | 89 | 36 | z0_event | 2 | 0 | lower |
| 1 4 5 6 9 | 180 | 121 | 89 | 36 | z0_event | 2 | 0 | lower |
| 1 4 5 6 9 | 180 | 121 | 89 | 36 | z0_event | 2 | 0 | lower |
| 1 4 5 6 9 | 180 | 121 | 89 | 36 | z0_event | 2 | 0 | lower |
| 1 4 5 6 9 | 180 | 121 | 89 | 36 | z0_event | 2 | 0 | lower |
| 1 4 5 6 9 | 180 | 121 | 89 | 36 | z0_event | 2 | 0 | lower |
| 1 4 5 6 9 | 180 | 121 | 89 | 36 | z0_event | 2 | 0 | lower |
| 1 4 5 6 9 | 180 | 121 | 89 | 36 | z0_event | 2 | 0 | lower |
| 1 5 6 8 9 | 360 | 241 | 89 | 36 | z0_event | 2 | 0 | middle |

---

## Analytic Conclusions for G4B-COMP-CAP

From this anatomy, the proof of G4B-COMP-CAP for n=6 should proceed as:

1. **z=0 runs**: Every run terminated by a z=0 event (gcd(e,n)=1 runner) satisfies
   run_len ≤ L/e − 1 = min_period − 1 (by Lemma S2 separation theorem).

2. **at_B_div_end runs**: These are truncated by the upper boundary of B_div.
   The top-band safety (T3(c)) guarantees a safe fiber at b_hi − ε, so the
   at_B_div_end run starts within distance max(L/e) of b_hi, bounding its length.

3. **Combined bound**: max_obstr_run ≤ max(min_per − 1, top_band_dist) < B_div − n
   when B_div = (n−2)/(n) · L (the minimum gap formula).

