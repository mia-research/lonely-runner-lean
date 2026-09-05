# Gap 1 TM2 Obstruction Scan (Support, Non-Canonical)
**Date:** 2026-03-03

## Purpose

Record diagnostic evidence for the obstruction class `O_tm2(F,M)` introduced in `v11` §17.15.

This note is support evidence only and not a proof dependency.

## Kernel

Used boundary/event-cell kernel from:
- `lrc_case2_d3_batch_certify_boundary_v1.py`

For each check-row `(n, fixed, M)`:
1. Build canonical `I_tot = I_lo union I_hi`.
2. Build fixed-signature event cells.
3. For each cell, compute fixed mask and `r(C)=|R_fix(C)|`.
4. Obstruction mass contribution is full cell length when `r(C)!=2`.

## Windows scanned

- `lrc_case2_d3_batch_checks_n7n11_v2.csv`
- `lrc_case2_d3_batch_checks_n8n9n10_v1.csv`
- `lrc_case2_d3_batch_checks_n13_boundary_v1.csv`
- `lrc_case2_d3_batch_checks_n17_boundary_v1.csv`
- `lrc_case2_d3_batch_checks_n19_boundary_v1.csv`

Total rows scanned: `39,946`.

## Results

| n | rows | rows with obstruction mass > 0 | obstruction mass sum | I_tot mass sum |
|---:|---:|---:|---:|---:|
| 7  | 300   | 0    | 0        | 148,272 |
| 8  | 581   | 369  | 412,647  | 615,591 |
| 9  | 989   | 432  | 1,470,412| 2,686,513 |
| 10 | 1,529 | 1,307| 4,900,773| 5,345,593 |
| 11 | 2,115 | 0    | 0        | 74,892,881 |
| 13 | 4,096 | 0    | 0        | 1,605,339,486 |
| 17 | 11,959| 0    | 0        | 196,542,097,765 |
| 19 | 18,377| 0    | 0        | 5,528,990,481,507 |

Aggregate:
- rows: `39,946`
- rows with obstruction: `2,108`
- all obstruction rows were in composite windows (`n=8,9,10`).

## Additional low-prime diagnostic

Small-prime finite-window spot scan (templates at `n=5,7`, `M<=120`, admissible `gcd(M,nL0)=1`):
- `n=5`: obstruction rows `0 / 272`
- `n=7`: obstruction rows `0 / 454`

## Interpretation for Gap 1

For prime one-divisible all-distinct windows currently tested (`n=5,7,11,13,17,19`),
observed obstruction mass is zero. This supports the chosen theorem route in
`lrc_g1h_stocktake_decision_memo_v1.md` to prove `O_tm2(F,M)=empty` analytically in prime scope.
