# Unified Metric Harness (000044 vs 000056)

- Source 000044: `/Users/trentpalelei/Downloads/lrc_efficiency_runtime_validation.csv`
- Source 000056: `/Users/trentpalelei/Downloads/lrc_validation_large_1759239075705.csv`
- Shared-key harness CSV: `/tmp/lrc_unified_metric_harness_shared_grid.csv`

## Shared Grid Definition
- Key = `(family, n, seed)` intersection across both datasets
- Shared rows: **8**
- Families: `['arithmetic']`
- n values: `[5, 7, 8, 10, 11, 12, 13, 15]`
- seed values: `[0]`

## Family Summary (shared grid)
| family | rows | phase_count_match true | unique_phases_match true | unique_phases_match false | unique_phases N/A | phase-vs-unique disagreements |
|---|---:|---:|---:|---:|---:|---:|
| arithmetic | 8 | 0 | 8 | 0 | 0 | 8 |

## Key Findings
- Arithmetic shared rows: phase_count_match=0/8, unique_phases_match=8/8 measured.
- Arithmetic phase-vs-unique disagreement count on measured rows: 8/8.

## Example Disagreement Rows
| family | n | seed | detected_phases_44 | phi_44 | unique_phases_56 | phi_56 |
|---|---:|---:|---:|---:|---:|---:|
| arithmetic | 5 | 0 | 1 | 4 | 4 | 4 |
| arithmetic | 7 | 0 | 2 | 6 | 6 | 6 |
| arithmetic | 8 | 0 | 2 | 4 | 4 | 4 |
| arithmetic | 10 | 0 | 2 | 4 | 4 | 4 |
| arithmetic | 11 | 0 | 5 | 10 | 10 | 10 |
| arithmetic | 12 | 0 | 2 | 4 | 4 | 4 |
| arithmetic | 13 | 0 | 5 | 12 | 12 | 12 |
| arithmetic | 15 | 0 | 3 | 8 | 8 | 8 |