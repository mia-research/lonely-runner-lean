# Lemma E Case-2 Factorization Scan (v1)

Decomposition used per tuple:
- `x0 = sum_{b in B_div} |A_b|`
- `B_div`: b-values surviving all divisible-speed constraints
- `A_b`: number of a in {0,...,n-1} surviving all non-divisible constraints at k=aL+b

| n | phi(n) | case2 tuples | min x0 | min x0/phi | min |B_div| | min max_b |A_b| |
|---:|---:|---:|---:|---:|---:|---:|
| 3 | 2 | 48 | 2 | 1.000 | 2 | 1 |
| 4 | 2 | 330 | 4 | 2.000 | 3 | 1 |
| 5 | 4 | 1104 | 8 | 2.000 | 4 | 1 |

## Min-x0 examples
- n=3: (1,3), (3,1)
- n=4: (1,2,4), (1,3,4), (1,4,2), (1,4,3), (2,1,4), (2,4,1), (3,1,4), (3,4,1)
- n=5: (1,3,4,5), (1,3,5,4), (1,4,3,5), (1,4,5,3), (1,5,3,4), (1,5,4,3), (3,1,4,5), (3,1,5,4)

## Min-|B_div| examples
- n=3: (1,3), (3,1)
- n=4: (1,1,4), (1,2,4), (1,4,1), (1,4,2), (1,4,4), (2,1,4), (2,4,1), (4,1,1)
- n=5: (1,1,1,5), (1,1,5,1), (1,1,5,5), (1,5,1,1), (1,5,1,5), (1,5,5,1), (1,5,5,5), (5,1,1,1)

Artifacts:
- rows: `/Users/trentpalelei/Desktop/Math Ex/reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_factorization_rows_v1.csv`
- summary: `/Users/trentpalelei/Desktop/Math Ex/reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_factorization_summary_v1.md`
