# LRC BR Witness Classifier Summary

**Date:** 2026-03-06
**Script:** `lrc_br_witness_classifier_v1.py`
**Branch hypothesis:** Every Case-B tuple (prime n, 1∈E_non) has a valid
low-multiplicity witness r* with |Excl(r*)| ≤ 2.

## Decision Gate

> If any Case-B tuple has NO valid k≤2 witness (interior residue, budget ok,
> all co-covering runners maintain window): the k≤2 hypothesis is falsified
> and the G4BI roadmap pivot activates.

## Definitions

- **k**: excl_multiplicity = |{e ∈ E_non : r ∉ safe_set(e, b_lo)}|
- **cap**: max arr(e, r) over excl_set
- **budget_ok**: cap ≤ (n−2)(L−n)/(2n)
- **blocker**: co-covering runner e with window_from_blo(e,r) < cap
- **valid**: budget_ok AND no blockers
- **strip**: full forbidden tau strip {n−c_e,...,n−2} (size c_e−1 ≥ 1)
- **c_e formula**: c_e = ceil((e·A_zone(e*) + e*·s_e) / (n·e*))

## n = 7

- Checked: 2000
- Case-B tuples: 283
- Tuples with valid k=1 witness: 277
- Tuples needing k=2 (no valid k=1, has valid k≤2): 6
- Tuples with valid k=3 only (k≤2 insufficient): 0
- **Tuples with NO valid k≤3 witness: 0**

## Overall Summary

- Total Case-B tuples analyzed: 283
- Tuples with valid k=1 witness: 277
- Tuples needing k=2 (no k=1, has k≤2): 6
- Tuples with valid k=3 only (k≤2 fails): 0
- **Tuples with NO valid k≤3 witness: 0**

### HYPOTHESIS STATUS: k≤2 HOLDS

All Case-B tuples in this sweep have a valid k≤2 witness.
The low-multiplicity-2 branch hypothesis is supported.
Proceed to Phase 1 (cascade diagnostic) and Phase 3 (proof routes).

