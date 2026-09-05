# Gap-1 GIL / Two-Class Probe Summary
**Date:** 2026-03-03
**Scope:** residual rows where `Xi_tr>0` from `lrc_gap1_delta_tr_mtot3_rows_v1.csv`.

## Inputs
- rows: `lrc_gap1_delta_tr_mtot3_rows_v1.csv`
- checks: `lrc_case2_d3_batch_checks_n7n11_v2.csv`
- checks: `lrc_case2_d3_batch_checks_n13_boundary_v1.csv`
- checks: `lrc_case2_d3_batch_checks_n17_boundary_v1.csv`
- checks: `lrc_case2_d3_batch_checks_n19_boundary_v1.csv`

## Residual-row checks
- residual rows analyzed: `92`
- GIL lower-band match count: `92/92`
- strong gap-diversity (`distinct_gaps >= n-2`) rows: `0/92`
- strong gap-diversity failures: `92`
- rows with `x0_non_danger >= phi(n)`: `92/92`
- rows with `Bsafe_non_danger >= phi(n)`: `91/92`

## Template-level low-band residue law
- residual templates scanned: `91`
- templates with exactly one bad-low residue class: `22`
- templates with exactly two bad-low residue classes: `69`
- two-class templates with complementary classes: `69/69`
- two-class templates matching predicted `M mod n in {+c,-c}` law: `69/69`

## By n (residual rows)
| n | rows | avg_distinct_gaps | min_distinct_gaps | avg_dangerous_frac | max_dangerous_frac |
|--:|----:|------------------:|------------------:|-------------------:|-------------------:|
| 7 | 8 | 1.75 | 1 | 0.3137 | 0.9971 |
| 11 | 11 | 2.27 | 1 | 0.2126 | 0.4995 |
| 13 | 16 | 2.38 | 1 | 0.1716 | 0.4843 |
| 17 | 26 | 2.88 | 1 | 0.1247 | 0.4333 |
| 19 | 31 | 3.00 | 1 | 0.1172 | 0.3642 |

## Bsafe Non-Danger Outliers
- n=7, fixed=(2,3,4,6), M=17, L0=84: `Bsafe_non_danger=3 < phi=6`, but `x0_non_danger=10 >= phi=6` (and `x0_non_danger <= x0=1686`).

## Artifacts
- rows: `lrc_gap1_gil_two_class_probe_rows_v1.csv`
- templates: `lrc_gap1_gil_two_class_probe_templates_v1.csv`
- summary: `lrc_gap1_gil_two_class_probe_summary_v1.md`
