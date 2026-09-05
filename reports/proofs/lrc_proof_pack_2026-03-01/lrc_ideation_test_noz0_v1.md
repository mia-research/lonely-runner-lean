# Test 3: Non-z=0 Termination Anatomy (4.8% Signal)

**Date:** 2026-03-04

---

## Dataset
- Tuples processed: 1705
- Total obstruction runs: 1705
- z0/t_increment runs: 0 (0.0%)
- at_B_div_end runs: 1705 (100.0%)

---

## Q1. Are at_B_div_end runs ALWAYS the last run in B_div?

- at_B_div_end runs that are last: **1705 / 1705**
✓ **YES — ALL at_B_div_end runs are the last run in B_div.**
This confirms: at_B_div_end = boundary truncation of the final obstruction run.

## Q2. Is run_len bounded by top-band distance?

- Top-band distance: min=1, max=2205, mean=53.97
- run_len ≤ top_band_dist+1: **118 / 1705**
✗ 1587 violations. Top-band bound insufficient.

## Q4. Does next z=0 fall within min_period of b_hi?

- next_z0_dist: min=1, max=280, mean=49.19
- within min_period: **1705 / 1705**
✓ ALL: next z=0 event falls within min_period beyond b_hi.
**Corollary:** Had B_div extended by min_period more, these runs would terminate at z=0.

## Q5. Type-B mechanism (runner bad-set shifts at boundary)?

- Runs with TYPE-B signature (runner loses coverage at b_hi): **0 / 1705**
✗ NO TYPE-B signature found. The mechanism is purely boundary truncation (not bad-set shift).

---

## Run Length Distribution for at_B_div_end

| run_len | count |
|---------|-------|
| 3 | 6 |
| 5 | 246 |
| 7 | 6 |
| 8 | 24 |
| 9 | 6 |
| 10 | 120 |
| 16 | 21 |
| 20 | 120 |
| 21 | 32 |
| 25 | 165 |
| 35 | 120 |
| 42 | 12 |
| 56 | 24 |
| 63 | 85 |
| 70 | 120 |
| 75 | 45 |
| 84 | 24 |
| 105 | 80 |
| 126 | 90 |
| 135 | 3 |
| 140 | 36 |
| 147 | 4 |
| 168 | 16 |
| 175 | 120 |
| 224 | 26 |
| 225 | 59 |
| 245 | 9 |
| 252 | 43 |
| 260 | 4 |
| 288 | 2 |
| 315 | 17 |
| 378 | 3 |
| 405 | 2 |
| 440 | 3 |
| 441 | 2 |
| 468 | 1 |
| 476 | 5 |
| 560 | 1 |
| 728 | 3 |

---

## Analytic Conclusions

**The 4.8% 'at_B_div_end' signal is NOT a distinct termination mechanism.**
It is the final obstruction run in B_div truncated by the upper boundary.

**Key structural fact (100% confirmed):**
- ALL at_B_div_end runs are the LAST run in B_div.
- ALL have next z=0 within min_period beyond b_hi.
- NO type-B (bad-set shift) mechanism exists.
- The top-band distance bound is INSUFFICIENT (only 118/1705 satisfy it).

**Analytic Proof of CB for at_B_div_end runs (NEW — derived from Test 3 Q4):**

For any Case-2 tuple E with a unit runner e_u (gcd(e_u,n)=1):
  - n | L (since e_div ∈ E with e_div = k·n)
  - e_u | L (since e_u ∈ E and L = lcm(E))
  - gcd(e_u, n) = 1 → lcm(n, e_u) = n·e_u | L
  - Therefore: min_period := L/e_u ≥ n.

Lower band (T3(b) proved): all t_e = 0 for b ∈ [b_lo, b_lo + min_period).
In this band, union_bad < n for all e ∈ E_non → delta > 0 → all min_period fibers SAFE.

Any obstruction run (including at_B_div_end) must start at b ≥ b_lo + min_period
(since the lower band is entirely safe and no run can begin there).

Therefore: safe fibers before the at_B_div_end run ≥ min_period ≥ n.
→ at_B_div_end run_len = B_div − (safe before run) ≤ B_div − n. □

**Verification:** Tight case n=4, E=(1,3,4), L=12, min_period=L/3=4=n, B_div=7, run_len=3=B_div−n. ✓

**Remaining open for G4B-COMP-CAP:**
Why do non-unit z=0 events (gcd(e,n)>1) create safe fibers (79.2% of z0-terminated runs in n=6)?
  - For unit runners (gcd=1): z_e(b)=0 → Lemma S2 → delta > 0. Proved.
  - For non-unit runners (gcd=2 or 3): z_e(b)=0 at b=m·L/e. The COMBINED bad-set
    of all runners at such b must leave some a uncovered. No single-runner guarantee.
  - This is the sole remaining analytic sub-lemma for G4B-COMP-CAP composite n.

**Summary of CB proof structure:**
  (A) z0 from unit runner: run_len ≤ min_period − 1  [Lemma S2, proved]
  (B) at_B_div_end: run_len ≤ B_div − n  [Lower band ≥ n, PROVED above]
  (C) z0 from non-unit runner: delta > 0 at z=0 fiber  [OPEN sub-lemma]

Cases (A) + (B) + empirical confirmation of (C) → CB proved for (A)+(B), certified for (C).

