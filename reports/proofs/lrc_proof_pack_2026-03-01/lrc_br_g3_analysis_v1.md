# LRC BR G3 Window Analysis — MZ Witnesses

**Date:** 2026-03-06  
**Script:** `lrc_br_g3_analysis_v1.py`  
**Scope:** Escape regime MZ witnesses (τ=0 + τ=n-1 at r** ∈ S₀, both large).

---

## §4.2 Error and Correction

**Handoff §4.2 claim (WRONG):**
> "For n ≥ 5, the small-runner window threat is ruled out when e_U > n."

**Correct analysis:**  
For small runner f_s (e < n) with τ(f_s, r**) = n-2, the blocking condition is:

    window(f_s, r**) < cap(r**)  ⟺  e_U < f_s · (n−1)

This CAN hold even when e_U > n, whenever f_s ≥ 2 and e_U is small (near n+1).

**Empirical §4.2 violations found: 177**  
(e_U > n, yet small runner f_s blocks the MZ window)

### §4.2 Violation Examples

| n | e_non | r** | e_L | e_U | f_s | τ(f_s) | window | cap | Condition |
|---|---|---|---|---|---|---|---|---|---|
| 5 | (1, 3, 8, 9) | 1 | 9 | 8 | 3 | 3 | 48 | 63 | e_U=8 < f_s*(n-1)=3*(n-1)=12 |
| 5 | (1, 4, 7, 11) | 2 | 7 | 11 | 4 | 3 | 77 | 252 | e_U=11 < f_s*(n-1)=4*(n-1)=16 |
| 5 | (1, 4, 9, 14) | 2 | 14 | 9 | 4 | 3 | 63 | 168 | e_U=9 < f_s*(n-1)=4*(n-1)=16 |
| 5 | (1, 4, 11, 14) | 2 | 14 | 11 | 4 | 3 | 77 | 252 | e_U=11 < f_s*(n-1)=4*(n-1)=16 |
| 5 | (1, 4, 11, 16) | 2 | 16 | 11 | 4 | 3 | 44 | 144 | e_U=11 < f_s*(n-1)=4*(n-1)=16 |
| 7 | (1, 2, 3, 5, 12, 19) | 1 | 19 | 12 | 5 | 5 | 456 | 855 | e_U=12 < f_s*(n-1)=5*(n-1)=30 |
| 7 | (1, 2, 3, 5, 18, 19) | 1 | 19 | 18 | 5 | 5 | 684 | 950 | e_U=18 < f_s*(n-1)=5*(n-1)=30 |
| 7 | (1, 2, 3, 5, 19, 24) | 1 | 19 | 24 | 5 | 5 | 912 | 1045 | e_U=24 < f_s*(n-1)=5*(n-1)=30 |

---

## MZ Witness Summary

- **Total MZ witnesses analyzed:** 2412
- **Valid (budget OK + no blockers):** 823
- **Blocked (any blocker or budget fail):** 1589
  - With alternative valid k≤2 witness: 1539
    - Alternative types: k1=1137, LL=161, MZ=210, UU=31
  - **No alternative found (ALERT):** 50 (expect 0)

### Blocker Breakdown

- Runner-1 blocks: 0 (expect 0)
- Small runner (f < n) blocks: 178
  - Of which §4.2 violations (e_U > n): 177
- Large runner (f > n) blocks: 2290

## Analytic Lemma Verification

| Lemma | Expected | Result | Status |
|---|---|---|---|
| Runner-1 never blocks MZ | 0 | 0 | ✓ HOLDS |
| Blocked MZ always has alternative k≤2 | 0 without alt | 50 | ✗ FAILS |
| §4.2 claim (small-runner ruled out by e_U>n) | — | 177 violations | ✗ FALSE (expected, see correction) |

## τ Distribution of Co-Covering Runners at MZ Witnesses

| τ value | Count | Fraction |
|---|---|---|
| 1 | 1702 | 0.092 |
| 2 | 1654 | 0.089 |
| 3 | 1594 | 0.086 |
| 4 | 1893 | 0.102 |
| 5 | 2051 | 0.111 |
| 6 | 1892 | 0.102 |
| 7 | 1876 | 0.101 |
| 8 | 1899 | 0.103 |
| 9 | 1874 | 0.101 |
| 10 | 1061 | 0.057 |
| 11 | 1012 | 0.055 |

## Per-n Breakdown

| n | Tuples | MZ witnesses | Valid | Blocked | §4.2 viols |
|---|---|---|---|---|---|
| 5 | 290 | 204 | 127 | 77 | 5 |
| 7 | 300 | 101 | 70 | 31 | 3 |
| 11 | 300 | 943 | 289 | 654 | 84 |
| 13 | 300 | 1164 | 337 | 827 | 85 |

## Blocked MZ Examples (with Alternative Witness Found)

### n=5, e_non=(1, 2, 6, 8), r**=3
- MZ pair: e_L=8 (τ=0), e_U=6 (τ=n-1)
- cap=36.0, budget=34.5, budget_ok=False
- **Alternative witness:** r=1, type=k1, excl=[8], cap=21

### n=5, e_non=(1, 3, 8, 9), r**=1
- MZ pair: e_L=9 (τ=0), e_U=8 (τ=n-1)
- cap=63.0, budget=106.5, budget_ok=True
- Small runner blocker: f_s=3, τ=3, window=48, cap=63
  → §4.2 VIOLATION: e_U=8 > n=5 but e_U < f_s*(n-1)=3*4=12
- **Alternative witness:** r=2, type=k1, excl=[9], cap=48

### n=5, e_non=(1, 4, 7, 11), r**=2
- MZ pair: e_L=7 (τ=0), e_U=11 (τ=n-1)
- cap=252.0, budget=460.5, budget_ok=True
- Small runner blocker: f_s=4, τ=3, window=77, cap=252
  → §4.2 VIOLATION: e_U=11 > n=5 but e_U < f_s*(n-1)=4*4=16
- **Alternative witness:** r=3, type=k1, excl=[11], cap=112

### n=5, e_non=(1, 4, 11, 14), r**=2
- MZ pair: e_L=14 (τ=0), e_U=11 (τ=n-1)
- cap=252.0, budget=460.5, budget_ok=True
- Small runner blocker: f_s=4, τ=3, window=77, cap=252
  → §4.2 VIOLATION: e_U=11 > n=5 but e_U < f_s*(n-1)=4*4=16
- **Alternative witness:** r=3, type=MZ, excl=[11, 14], cap=132

### n=5, e_non=(1, 4, 11, 16), r**=2
- MZ pair: e_L=16 (τ=0), e_U=11 (τ=n-1)
- cap=144.0, budget=262.5, budget_ok=True
- Small runner blocker: f_s=4, τ=3, window=44, cap=144
  → §4.2 VIOLATION: e_U=11 > n=5 but e_U < f_s*(n-1)=4*4=16
- **Alternative witness:** r=3, type=k1, excl=[11], cap=64

### n=5, e_non=(1, 6, 7, 8), r**=3
- MZ pair: e_L=8 (τ=0), e_U=6 (τ=n-1)
- cap=252.0, budget=250.5, budget_ok=False
- Large runner blocker: f_L=7, τ=2, window=192, cap=252
- **Alternative witness:** r=2, type=k1, excl=[7], cap=72

### n=5, e_non=(1, 6, 8, 9), r**=3
- MZ pair: e_L=8 (τ=0), e_U=6 (τ=n-1)
- cap=108.0, budget=106.5, budget_ok=False
- Large runner blocker: f_L=9, τ=3, window=8, cap=108
- **Alternative witness:** r=1, type=MZ, excl=[8, 9], cap=63

### n=5, e_non=(1, 6, 8, 14), r**=3
- MZ pair: e_L=8 (τ=0), e_U=6 (τ=n-1)
- cap=252.0, budget=250.5, budget_ok=False
- **Alternative witness:** r=2, type=k1, excl=[14], cap=12

---

## Verdict

✗ ALERT: 50 blocked MZ witnesses have NO alternative. G3 route is incomplete.
