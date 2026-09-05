# Unified Metric Harness (Family-n Grid)

- 000044 source: `/Users/trentpalelei/Downloads/lrc_efficiency_runtime_validation.csv`
- 000056 source: `/Users/trentpalelei/Downloads/lrc_validation_large_1759239075705.csv`
- Output CSV: `/tmp/lrc_unified_metric_harness_family_n_grid.csv`

## Shared Grid
- Shared `(family,n)` cells: **16**
- Families in shared grid: `['arithmetic', 'geometric']`
- n values in shared grid: `[5, 7, 8, 10, 11, 12, 13, 15]`

## Cell Summary
| family | n | phase_rate_44 | unique_rate_56 (measured) | unique measured rows | unique N/A rows | interpretation |
|---|---:|---:|---:|---:|---:|---|
| arithmetic | 5 | 0.000000 | 1.000000 | 5000 | 0 | rates_disagree |
| arithmetic | 7 | 0.000000 | 1.000000 | 5000 | 0 | rates_disagree |
| arithmetic | 8 | 0.000000 | 1.000000 | 5000 | 0 | rates_disagree |
| arithmetic | 10 | 0.000000 | 1.000000 | 5000 | 0 | rates_disagree |
| arithmetic | 11 | 0.000000 | 1.000000 | 5000 | 0 | rates_disagree |
| arithmetic | 12 | 0.000000 | 1.000000 | 5000 | 0 | rates_disagree |
| arithmetic | 13 | 0.000000 | 1.000000 | 5000 | 0 | rates_disagree |
| arithmetic | 15 | 0.000000 | 1.000000 | 5000 | 0 | rates_disagree |
| geometric | 5 | 1.000000 |  | 0 | 5000 | unique_not_measured_in_56 |
| geometric | 7 | 1.000000 |  | 0 | 5000 | unique_not_measured_in_56 |
| geometric | 8 | 1.000000 |  | 0 | 5000 | unique_not_measured_in_56 |
| geometric | 10 | 1.000000 |  | 0 | 5000 | unique_not_measured_in_56 |
| geometric | 11 | 1.000000 |  | 0 | 5000 | unique_not_measured_in_56 |
| geometric | 12 | 1.000000 |  | 0 | 5000 | unique_not_measured_in_56 |
| geometric | 13 | 1.000000 |  | 0 | 5000 | unique_not_measured_in_56 |
| geometric | 15 | 1.000000 |  | 0 | 5000 | unique_not_measured_in_56 |

## Family-Level Summary on Shared n Values
| family | rows44 | phase_true_44 | phase_rate_44 | rows56 | unique_measured_56 | unique_true_56 | unique_rate_56 | unique_na_56 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| arithmetic | 48 | 0 | 0.000000 | 40000 | 40000 | 40000 | 1.000000 | 0 |
| geometric | 48 | 48 | 1.000000 | 40000 | 0 | 0 |  | 40000 |