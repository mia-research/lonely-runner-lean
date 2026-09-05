# Triple-Overlap + Inclusion Checker (v1)

Formulas used:
- `|D_e| = 2L - e`
- Pair overlap: exact CRT residue formula
- Triple overlap: exact CRT-lift formula
  `|D_a∩D_b∩D_c| = g * #{x mod M : x in all three dangerous residue systems}`
  where `g=gcd(a,b,c)`, `M=nL/g`.

LP bounds:
- `lp_min_x0_S1S2`: min possible safe-point count from moments (N,S1,S2)
- `lp_min_x0_S1S2S3`: min possible safe-point count from moments (N,S1,S2,S3)
- If lower bound > 0, then `|U D_e| < N` is proven for that tuple by those moments.

| n | max_e | gcd1 tuples | proven (S1,S2) | proven (S1,S2,S3) | rate S1,S2 | rate S1,S2,S3 |
|---:|---:|---:|---:|---:|---:|---:|
| 3 | 12 | 91 | 91 | 91 | 1.0000 | 1.0000 |
| 4 | 9 | 637 | 589 | 637 | 0.9246 | 1.0000 |
| 5 | 7 | 2303 | 1463 | 2231 | 0.6353 | 0.9687 |
| 6 | 5 | 3091 | 1471 | 2731 | 0.4759 | 0.8835 |
| 7 | 4 | 4031 | 3761 | 4031 | 0.9330 | 1.0000 |
| 8 | 4 | 16255 | 15625 | 16255 | 0.9612 | 1.0000 |

Artifacts:
- table: `/tmp/lrc_triple_overlap_inclusion_table_v1.csv`
- summary: `/tmp/lrc_triple_overlap_inclusion_summary_v1.md`
