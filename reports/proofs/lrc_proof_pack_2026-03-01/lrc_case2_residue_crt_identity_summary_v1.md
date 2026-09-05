# Case-2 Residue/CRT Identity Checker (v1)

Validated identities:
- per-speed bad-a set = union of <=2 linear congruence classes mod n
- fiber moments I_b,P_b,T_b from set-system match direct counting
- pair/triple intersections from branch CRT counts match direct intersections

## Exhaustive blocks
| n | tuples checked | status |
|---:|---:|---:|
| 3 | 48 | OK |
| 4 | 330 | OK |
| 5 | 1104 | OK |

## Random higher-n blocks
| n | sampled tuples | max_e | sample_b_limit | status |
|---:|---:|---:|---:|---:|
| 6 | 4000 | 8 | 40 | OK |
| 7 | 3000 | 7 | 40 | OK |
| 8 | 2000 | 10 | 40 | OK |

Artifacts:
- rows: `/tmp/lrc_case2_residue_crt_identity_rows_v1.csv`
- summary: `/tmp/lrc_case2_residue_crt_identity_summary_v1.md`
