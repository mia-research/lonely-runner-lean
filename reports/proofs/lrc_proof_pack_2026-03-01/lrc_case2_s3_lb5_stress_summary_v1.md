# S3 LB5 Stress (v1)

Checks candidate structural lower bound:
- `LB5(E) = sum_s N_s * max(0, n-UB5_s) >= n-1`.

| n | kept tuples | violations LB5<n-1 | min LB5 | min x0 |
|---:|---:|---:|---:|---:|
| 13 | 160 | 1 | 6 | 856 |
- first violation n=13: `E=(2, 1, 1, 1, 1, 8, 13, 2, 1, 7, 1, 8)`, `L=728`, `B_div=617`, `x0=4112`, `LB5=6`
| 14 | 140 | 0 | 168 | 452 |
| 15 | 120 | 1 | 0 | 440 |
- first violation n=15: `E=(2, 15, 1, 1, 12, 1, 2, 2, 2, 15, 3, 2, 15, 10)`, `L=60`, `B_div=53`, `x0=440`, `LB5=0`
