# C2.3/C2.4 Inequality Check (v2)

Bad-fiber moments:
- `C_bad = #{b in B_div : A_b=0}`
- `I_bad = sum_{bad b} sum_a q_a(b)`
- `P_bad = sum_{bad b} sum_a C(q_a(b),2)`
- `T_bad = sum_{bad b} sum_a C(q_a(b),3)`

C2.3 tested inequalities:
- `n C_bad <= I_bad`
- `n C_bad <= I_bad - (2/m)P_bad` (m=|E_non|)
- `n C_bad <= I_bad - P_bad + T_bad`

C2-main sufficiency candidates tested:
- (A) `I_bad <= n(B_div-(n-1))`
- (B) `I_bad - (2/m)P_bad <= n(B_div-(n-1))`
- (C) `I_bad - P_bad + T_bad <= n(B_div-(n-1))`

| n | case2 tuples | x0>=phi | C2.3(I) | C2.3(I,P) | C2.3(I,P,T) | C2-main(A) | C2-main(B) | C2-main(C) | min bad-fiber I_b |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 3 | 48 | 48/48 | 48/48 | 48/48 | 48/48 | 48/48 | 48/48 | 48/48 | None |
| 4 | 330 | 330/330 | 330/330 | 330/330 | 330/330 | 330/330 | 330/330 | 330/330 | 4 |
| 5 | 1104 | 1104/1104 | 1104/1104 | 1104/1104 | 1104/1104 | 1056/1104 | 1104/1104 | 1104/1104 | 5 |
| 6 | 15150 | 15150/15150 | 15150/15150 | 15150/15150 | 15150/15150 | 14910/15150 | 15150/15150 | 15150/15150 | 6 |
| 7 | 70992 | 70992/70992 | 70992/70992 | 70992/70992 | 70992/70992 | 68112/70992 | 70272/70992 | 70992/70992 | 7 |

## Min margins for C2-main candidates
- n=3: min margins A=0, B=0.0, C=0
- n=4: min margins A=0, B=0.0, C=0
- n=5: min margins A=-6, B=0.0, C=0
- n=6: min margins A=-92, B=0.0, C=0
- n=7: min margins A=-437, B=-63.0, C=0

## Example failures of C2-main(C)
- n=3: none
- n=4: none
- n=5: none
- n=6: none
- n=7: none

Artifacts:
- rows: `/tmp/lrc_case2_c23_c24_rows_v2.csv`
- summary: `/tmp/lrc_case2_c23_c24_summary_v2.md`
