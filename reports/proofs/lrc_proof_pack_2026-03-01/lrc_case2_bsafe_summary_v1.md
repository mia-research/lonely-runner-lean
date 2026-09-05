# Lemma E Case-2 B_safe Scan (v1)

Definitions:
- `B_div = {b : b passes all divisible-speed constraints}`
- `B_safe = {b in B_div : exists a with k=aL+b safe for non-divisible constraints}`
- `x0 = sum_{b in B_div} |A_b|`, so `x0 >= |B_safe|`.

| n | phi(n) | case2 tuples | min B_div | min B_safe | min x0 | viol(B_safe>=n-1) | viol(B_safe>=phi) | viol(x0>=phi) |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 3 | 2 | 48 | 2 | 2 | 2 | 0 | 0 | 0 |
| 4 | 2 | 330 | 3 | 3 | 4 | 0 | 0 | 0 |
| 5 | 4 | 1104 | 4 | 4 | 8 | 0 | 0 | 0 |
| 6 | 2 | 15150 | 5 | 5 | 10 | 0 | 0 | 0 |
| 7 | 6 | 70992 | 6 | 6 | 30 | 0 | 0 | 0 |

## Min-B_safe examples
- n=3: (1, 3) (L=3, B_div=2, B_safe=2, x0=2), (3, 1) (L=3, B_div=2, B_safe=2, x0=2)
- n=4: (1, 1, 4) (L=4, B_div=3, B_safe=3, x0=6), (1, 2, 4) (L=4, B_div=3, B_safe=3, x0=4), (1, 4, 1) (L=4, B_div=3, B_safe=3, x0=6), (1, 4, 2) (L=4, B_div=3, B_safe=3, x0=4), (1, 4, 4) (L=4, B_div=3, B_safe=3, x0=6), (2, 1, 4) (L=4, B_div=3, B_safe=3, x0=4), (2, 4, 1) (L=4, B_div=3, B_safe=3, x0=4), (4, 1, 1) (L=4, B_div=3, B_safe=3, x0=6)
- n=5: (1, 1, 1, 5) (L=5, B_div=4, B_safe=4, x0=12), (1, 1, 5, 1) (L=5, B_div=4, B_safe=4, x0=12), (1, 1, 5, 5) (L=5, B_div=4, B_safe=4, x0=12), (1, 5, 1, 1) (L=5, B_div=4, B_safe=4, x0=12), (1, 5, 1, 5) (L=5, B_div=4, B_safe=4, x0=12), (1, 5, 5, 1) (L=5, B_div=4, B_safe=4, x0=12), (1, 5, 5, 5) (L=5, B_div=4, B_safe=4, x0=12), (5, 1, 1, 1) (L=5, B_div=4, B_safe=4, x0=12)
- n=6: (1, 1, 1, 1, 6) (L=6, B_div=5, B_safe=5, x0=20), (1, 1, 1, 2, 6) (L=6, B_div=5, B_safe=5, x0=16), (1, 1, 1, 3, 6) (L=6, B_div=5, B_safe=5, x0=16), (1, 1, 1, 6, 1) (L=6, B_div=5, B_safe=5, x0=20), (1, 1, 1, 6, 2) (L=6, B_div=5, B_safe=5, x0=16), (1, 1, 1, 6, 3) (L=6, B_div=5, B_safe=5, x0=16), (1, 1, 1, 6, 6) (L=6, B_div=5, B_safe=5, x0=20), (1, 1, 2, 1, 6) (L=6, B_div=5, B_safe=5, x0=16)
- n=7: (1, 1, 1, 1, 1, 7) (L=7, B_div=6, B_safe=6, x0=30), (1, 1, 1, 1, 7, 1) (L=7, B_div=6, B_safe=6, x0=30), (1, 1, 1, 1, 7, 7) (L=7, B_div=6, B_safe=6, x0=30), (1, 1, 1, 7, 1, 1) (L=7, B_div=6, B_safe=6, x0=30), (1, 1, 1, 7, 1, 7) (L=7, B_div=6, B_safe=6, x0=30), (1, 1, 1, 7, 7, 1) (L=7, B_div=6, B_safe=6, x0=30), (1, 1, 1, 7, 7, 7) (L=7, B_div=6, B_safe=6, x0=30), (1, 1, 7, 1, 1, 1) (L=7, B_div=6, B_safe=6, x0=30)

## Min-x0 examples
- n=3: (1, 3) (L=3, B_div=2, B_safe=2, x0=2), (3, 1) (L=3, B_div=2, B_safe=2, x0=2)
- n=4: (1, 2, 4) (L=4, B_div=3, B_safe=3, x0=4), (1, 3, 4) (L=12, B_div=7, B_safe=4, x0=4), (1, 4, 2) (L=4, B_div=3, B_safe=3, x0=4), (1, 4, 3) (L=12, B_div=7, B_safe=4, x0=4), (2, 1, 4) (L=4, B_div=3, B_safe=3, x0=4), (2, 4, 1) (L=4, B_div=3, B_safe=3, x0=4), (3, 1, 4) (L=12, B_div=7, B_safe=4, x0=4), (3, 4, 1) (L=12, B_div=7, B_safe=4, x0=4)
- n=5: (1, 3, 4, 5) (L=60, B_div=37, B_safe=8, x0=8), (1, 3, 5, 4) (L=60, B_div=37, B_safe=8, x0=8), (1, 4, 3, 5) (L=60, B_div=37, B_safe=8, x0=8), (1, 4, 5, 3) (L=60, B_div=37, B_safe=8, x0=8), (1, 5, 3, 4) (L=60, B_div=37, B_safe=8, x0=8), (1, 5, 4, 3) (L=60, B_div=37, B_safe=8, x0=8), (3, 1, 4, 5) (L=60, B_div=37, B_safe=8, x0=8), (3, 1, 5, 4) (L=60, B_div=37, B_safe=8, x0=8)
- n=6: (1, 2, 3, 4, 6) (L=12, B_div=9, B_safe=9, x0=10), (1, 2, 3, 6, 4) (L=12, B_div=9, B_safe=9, x0=10), (1, 2, 4, 3, 6) (L=12, B_div=9, B_safe=9, x0=10), (1, 2, 4, 6, 3) (L=12, B_div=9, B_safe=9, x0=10), (1, 2, 6, 3, 4) (L=12, B_div=9, B_safe=9, x0=10), (1, 2, 6, 4, 3) (L=12, B_div=9, B_safe=9, x0=10), (1, 3, 2, 4, 6) (L=12, B_div=9, B_safe=9, x0=10), (1, 3, 2, 6, 4) (L=12, B_div=9, B_safe=9, x0=10)
- n=7: (1, 1, 1, 1, 1, 7) (L=7, B_div=6, B_safe=6, x0=30), (1, 1, 1, 1, 7, 1) (L=7, B_div=6, B_safe=6, x0=30), (1, 1, 1, 1, 7, 7) (L=7, B_div=6, B_safe=6, x0=30), (1, 1, 1, 7, 1, 1) (L=7, B_div=6, B_safe=6, x0=30), (1, 1, 1, 7, 1, 7) (L=7, B_div=6, B_safe=6, x0=30), (1, 1, 1, 7, 7, 1) (L=7, B_div=6, B_safe=6, x0=30), (1, 1, 1, 7, 7, 7) (L=7, B_div=6, B_safe=6, x0=30), (1, 1, 7, 1, 1, 1) (L=7, B_div=6, B_safe=6, x0=30)

Artifacts:
- rows: `/Users/trentpalelei/Desktop/Math Ex/reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_bsafe_rows_v1.csv`
- summary: `/Users/trentpalelei/Desktop/Math Ex/reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_bsafe_summary_v1.md`
