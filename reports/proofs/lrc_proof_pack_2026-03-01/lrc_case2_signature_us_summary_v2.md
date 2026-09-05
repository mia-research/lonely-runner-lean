# Case-2 Signature U_s Checker (v2, upgraded)

Closed-form classwise candidates:
- `U_s^cap`: capacity (`sum_e (1+delta_e)gcd(e,n) >= n`).
- `U_s^solv`: solvable branch capacity (`sum_e s_e(sig) >= n`).
- `U_s^b3`: `UB3>=n`, where `UB3=V1-V2+V3`.
- `U_s^b5`: `UB5>=n`, where `UB5=V1-V2+V3-V4+V5`.
- `U_s^bN`: dynamic odd Bonferroni bound: `UB_k>=n` with `k=max odd <= n-1`.
- `U_s^hyb5`: `cap & solv & b5`.
- `U_s^hybN`: `cap & solv & bN`.
- `U_s^cov`: exact baseline (`cover_s=n`).

Tuple-level forcing check:
- `sum_s U_s F_s <= n(B_div-(n-1))`.

## Exhaustive (Case-2 grids)
| n | case2 tuples | x0>=phi | cap | solv | b3 | b5 | bN | hyb5 | hybN | cov |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 3 | 48 | 48/48 | 48/48 | 48/48 | 48/48 | 48/48 | 48/48 | 48/48 | 48/48 | 48/48 |
| 4 | 330 | 330/330 | 297/330 | 303/330 | 330/330 | 330/330 | 330/330 | 330/330 | 330/330 | 330/330 |
| 5 | 1104 | 1104/1104 | 956/1104 | 956/1104 | 1104/1104 | 1104/1104 | 1104/1104 | 1104/1104 | 1104/1104 | 1104/1104 |
| 6 | 15150 | 15150/15150 | 12565/15150 | 13295/15150 | 14970/15150 | 15150/15150 | 15150/15150 | 15150/15150 | 15150/15150 | 15150/15150 |

## Random Stress (higher n)
| n | k_n | samples | x0>=phi | bN forcing |
|---:|---:|---:|---:|---:|
| 7 | 5 | 300 | 300/300 | 300/300 |
| 8 | 7 | 200 | 200/200 | 200/200 |
| 9 | 7 | 140 | 140/140 | 140/140 |
| 10 | 9 | 90 | 90/90 | 90/90 |

Artifacts:
- rows: `/tmp/lrc_case2_signature_us_rows_v2.csv`
- summary: `/tmp/lrc_case2_signature_us_summary_v2.md`
