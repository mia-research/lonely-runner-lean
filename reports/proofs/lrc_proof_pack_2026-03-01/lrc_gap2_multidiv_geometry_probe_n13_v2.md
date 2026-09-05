# Gap-2 Multi-Divisible Geometry Probe (n=13, v2)

Status: progress artifact for Gap 2. This is not a global closure claim.

## What changed

`lrc_case2_multidiv_band_geometry_v2.py` replaces the old per-`b` `B_div` scan with an exact interval method:

- For each divisible speed `e = n f`, define
  `S_f = {x in [0,1): frac(f x) in [1/n, (n-1)/n]}`.
- Each `S_f` is a finite union of rational closed intervals.
- Compute `S = intersect_f S_f` exactly (fraction arithmetic).
- For `L = lcm(E_fixed U {M} U E_div)`, convert each `x`-interval `[lo,hi]` to integer fiber interval
  `b in [ceil(L lo), floor(L hi)]`.

This yields exact `B_div` components without scanning all `b in [0,L-1]`.

## Exact parity checks

Validated against scan-based `v1` outputs:

1. `n=13, E_div=(13,26), M={11,17,19}` with `--validate-scan`: exact component match.
2. `n=13, E_div=(13,26,39), admissible M<=80` with `--validate-scan`: exact component match.
3. CSV parity checks (`diff -u`): no differences in both summary and components outputs.

## Runtime comparison (same workload)

Workload: `n=13, E_div=(13,26,39), fixed={1..9}, admissible M<=80`.

- `v1` scan method: `real 3.14s`
- `v2` interval method: `real 0.03s`

Speedup is about 100x on this probe.

## Geometry findings reused from v1/v2-equal outputs

Across admissible `M<=80` for fixed `E_fixed={1..9}` and `L0=32760`:

- `E_div=(13,26)`: components `=2`, `B_div_count = 25200*M + 2`.
- `E_div=(13,39)`: components `=3`, `B_div_count = 24360*M + 3`.
- `E_div=(26,39)`: components `=4`, `B_div_count = 24360*M + 4`.
- `E_div=(13,26,39)`: components `=4`, `B_div_count = 21840*M + 4`.

Component endpoints are affine in `M` with exact formulas in the `components_*_m80_probe.csv` artifacts.

## Gap-2 relevance

This gives the non-bruteforce `B_div` geometry layer needed for component-wise band construction:

- represent `B_div` as finite interval components,
- intersect each component with low/high frozen bands,
- feed resulting component bands into TM/D.1'/D.2' counting.

Remaining theoretical step: prove the component-wise two-band lower bound in full generality.
