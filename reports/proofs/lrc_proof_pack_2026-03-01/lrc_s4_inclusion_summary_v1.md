# S4 Inclusion Checker (v1)

Exact moments used: S1, S2, S3, S4 (all verified against brute profiles).

| n | max_e | gcd1 tuples | proven S1,S2 | proven S1,S2,S3 | proven S1,S2,S3,S4 | rate S2 | rate S3 | rate S4 | unresolved S3 | unresolved S4 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 3 | 12 | 91 | 91 | 91 | 91 | 1.0000 | 1.0000 | 1.0000 | 0 | 0 |
| 4 | 9 | 637 | 589 | 637 | 637 | 0.9246 | 1.0000 | 1.0000 | 0 | 0 |
| 5 | 7 | 2303 | 1463 | 2231 | 2303 | 0.6353 | 0.9687 | 1.0000 | 72 | 0 |
| 6 | 5 | 3091 | 1471 | 2731 | 3091 | 0.4759 | 0.8835 | 1.0000 | 360 | 0 |
| 7 | 4 | 4031 | 3761 | 4031 | 4031 | 0.9330 | 1.0000 | 1.0000 | 0 | 0 |
| 8 | 4 | 16255 | 15625 | 16255 | 16255 | 0.9612 | 1.0000 | 1.0000 | 0 | 0 |

Artifacts:
- table: `/tmp/lrc_s4_inclusion_table_v1.csv`
- unresolved families (`n=5,6`, S4 unresolved): `/tmp/lrc_s4_unresolved_families_v1.csv`
- summary: `/tmp/lrc_s4_inclusion_summary_v1.md`
