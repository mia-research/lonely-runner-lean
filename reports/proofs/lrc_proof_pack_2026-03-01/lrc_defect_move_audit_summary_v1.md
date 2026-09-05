# Defect-Move Inequality Audit (v1)

Primitive move tested:
- `H_p`: suffix hole insertion (`e_p..e_m += 1`) on strict sorted tuple `E`.

Inequality tested:
- `f(H_p(E)) <= f(E)` where `f(E)=|U D_e|/N` is forbidden density.

| n | sampled tuples | move tests | nonincrease OK | nonincrease FAIL | OK rate |
|---:|---:|---:|---:|---:|---:|
| 5 | 120 | 480 | 251 | 229 | 0.5229 |
| 6 | 120 | 600 | 281 | 319 | 0.4683 |
| 7 | 120 | 720 | 412 | 308 | 0.5722 |
| 8 | 120 | 840 | 458 | 382 | 0.5452 |

Conclusion:
- This naive monotonic inequality is not universally true on sampled exact checks.
- Defect-monotonic proof must use a stronger/structured potential than raw `f` per single move.

Artifacts:
- rows: `/tmp/lrc_defect_move_audit_rows_v1.csv`
- summary: `/tmp/lrc_defect_move_audit_summary_v1.md`
