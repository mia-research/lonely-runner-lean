# LRC BR σ-Diagnostic Summary

**Date:** 2026-03-06  
**Script:** `lrc_br_sigma_diagnostic_v1.py`  
**Framework:** σ(e) = q·s⁻¹ mod n; escape/T1/T2 classification

---

## Structural Invariants (should always hold)

| Invariant | Violations | Status |
|---|---|---|
| \|A_small\| = k_S − 1 (a_high injectivity) | 0 | ✓ HOLDS |
| \|S₀\| = k_L (sharp count, full LRC) | 0 | ✓ HOLDS |

## Classification Counts

- **Total Case-B tuples:** 1190
- **Escape (E):** 1133 (95%)
  - k=1 via Key Lemma: 982
  - k=2 LL rescue: 96
  - k=2 MZ rescue: 55
  - **No rescue found (ALERT):** 0 (expect 0)
- **Non-escape T1 (k_L≥k_S):** 19 (1%)
  - LL coincidence (info only, LL∈A_small→k=3): 12
  - No LL (k_L=k_S all distinct σ): 7
  - ψ bijection holds: 19
  - **ψ bijection fails (ALERT):** 0 (expect 0)
  - ≥1 valid UZ k=1 candidate: 14
  - All UZ k=1 invalid (early-time?): 5
- **Non-escape T2 (k_L<k_S):** 38 (3%)
  - ψ bijection holds: 38
  - **ψ bijection fails (ALERT):** 0 (expect 0)
  - ≥1 valid UZ k=1 candidate: 24
  - All UZ k=1 invalid (early-time?): 14
- **Unclassified:** 0 (expect 0)

## Analytic Lemma Verification

| Lemma | Expected | Violations | Status |
|---|---|---|---|
| Runner-1 Non-Blocking | 0 | 0 | ✓ HOLDS |
| Escape → k=1 or LL/MZ rescue | 0 unrescued | 0 | ✓ HOLDS |
| Non-escape → ψ: E_L → S₀ bijection (T1+T2) | 0 failures | 0 | ✓ HOLDS |
| T1 LL coincidence (informational; LL∈A_small→k=3) | — | 7 no LL | (pigeonhole fails at k_L=k_S) |
| T2 → ψ bijection | 0 failures | 0 | ✓ HOLDS |

## ⚠ T1 Tuples Without LL (INVESTIGATE)

- n=5, e_non=(1, 2, 6, 16), σ-vals={6: 1, 16: 3}
- n=5, e_non=(1, 2, 12, 14), σ-vals={12: 1, 14: 3}
- n=5, e_non=(1, 3, 8, 18), σ-vals={8: 2, 18: 1}
- n=5, e_non=(1, 3, 11, 12), σ-vals={11: 2, 12: 1}
- n=5, e_non=(1, 4, 6, 9), σ-vals={6: 1, 9: 4}
- n=5, e_non=(1, 4, 17, 18), σ-vals={17: 4, 18: 1}
- n=7, e_non=(1, 2, 3, 8, 10, 18), σ-vals={8: 1, 10: 5, 18: 4}

## T2 Case Sample Detail

### n=5, e_non=(1, 2, 3, 4)
- k_L=0, k_S=4, A_small=[1, 2, 3], S₀=[]
- σ-values of large runners: {}
- ψ bijection: True

### n=5, e_non=(1, 2, 3, 8)
- k_L=1, k_S=3, A_small=[2, 3], S₀=[1]
- σ-values of large runners: {8: 2}
- ψ bijection: True
  - r=1, e_L=8: cap=21, budget=34.5, budget_ok=True, runner1_blocks=False, blockers=[3], valid=False

### n=5, e_non=(1, 2, 3, 12)
- k_L=1, k_S=3, A_small=[2, 3], S₀=[1]
- σ-values of large runners: {12: 1}
- ψ bijection: True
  - r=1, e_L=12: cap=8, budget=16.5, budget_ok=True, runner1_blocks=False, blockers=[], valid=True

### n=5, e_non=(1, 2, 3, 16)
- k_L=1, k_S=3, A_small=[2, 3], S₀=[1]
- σ-values of large runners: {16: 3}
- ψ bijection: True
  - r=1, e_L=16: cap=27, budget=70.5, budget_ok=True, runner1_blocks=False, blockers=[], valid=True

### n=5, e_non=(1, 2, 4, 6)
- k_L=1, k_S=3, A_small=[1, 2], S₀=[3]
- σ-values of large runners: {6: 1}
- ψ bijection: True
  - r=3, e_L=6: cap=18, budget=16.5, budget_ok=False, runner1_blocks=False, blockers=[], valid=False

## Per-n Counts

| n | Total Case-B |
|---|---|
| 5 | 290 |
| 7 | 300 |
| 11 | 300 |
| 13 | 300 |

