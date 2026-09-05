# Gap-1 Reduced Delta_tr (m_tot<=3) Support Validation
**Date:** 2026-03-03

## Scope
Prime-window support check over existing certified check artifacts.
This is a consistency artifact only (not a proof dependency).

## Inputs
- `lrc_case2_d3_batch_checks_n7n11_v2.csv`
- `lrc_case2_d3_batch_checks_n13_boundary_v1.csv`
- `lrc_case2_d3_batch_checks_n17_boundary_v1.csv`
- `lrc_case2_d3_batch_checks_n19_boundary_v1.csv`

## Global results
- rows processed (prime n only): `36847`
- `Delta_tr^sh >= 0` failures: `0`
- criterion equivalence mismatches (`G1.K.4` vs `B_safe>=n-1`): `0` (algebraic consistency check on computed quantities)
- rows with `Xi_tr = 0`: `36755`
- rows with `Xi_tr > 0`: `92`
- max observed `Xi_tr`: `18`
- input-row certifier failures (`ok=0`): `0`
- input-row theorem failures (`x0 < phi_n`): `0`

## By n
| n | rows | Delta_nonneg_fail | criterion_mismatch | Xi_tr=0 |
|--:|----:|------------------:|-------------------:|--------:|
| 7 | 300 | 0 | 0 | 292 |
| 11 | 2115 | 0 | 0 | 2104 |
| 13 | 4096 | 0 | 0 | 4080 |
| 17 | 11959 | 0 | 0 | 11933 |
| 19 | 18377 | 0 | 0 | 18346 |

## Artifacts
- rows: `lrc_gap1_delta_tr_mtot3_rows_v1.csv`
- summary: `lrc_gap1_delta_tr_mtot3_validation_v1.md`
