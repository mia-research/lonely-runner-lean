# C2-main(C) Random Stress (v1)

Condition tested:
- `I_bad - P_bad + T_bad <= n(B_div-(n-1))`

| n | checked | target | max_e | L_cap | violations |
|---:|---:|---:|---:|---:|---:|
| 8 | 12000 | 12000 | 32 | 2500 | 0 |
| 9 | 8000 | 8000 | 36 | 2500 | 0 |
| 10 | 6000 | 6000 | 40 | 2500 | 0 |
| 11 | 219 | 3000 | 44 | 2500 | 0 |
| 12 | 175 | 2000 | 48 | 2500 | 0 |

## First violation per n
- n=8: none
- n=9: none
- n=10: none
- n=11: none
- n=12: none

Artifacts:
- rows: `/tmp/lrc_case2_c2mainC_stress_rows_v1.csv`
- summary: `/tmp/lrc_case2_c2mainC_stress_summary_v1.md`
