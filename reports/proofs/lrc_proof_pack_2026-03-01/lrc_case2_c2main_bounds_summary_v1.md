# Lemma E Case-2 Explicit Lower-Bound Checker (v1)

Bounds used:
- `|B_div| >= max(lb_union1, lb_anchor)`
- `lb_union1 = max(0, sum_i |S_i| - (s-1)L)` where `S_i` is exact single-divisible safe set
- `lb_anchor = |{j in {1..n-1}: forall i, n !| (f_i j)}|` for anchors `b=jL/n`
- Uniform fiber bound: `|A_b| >= max(0, n - 2*sum_{e in E_non} gcd(e,n))`
- Product bound: `x0 >= lb_Bdiv * lb_Ab_uniform`
- Stronger explicit per-fiber bound: `x0 >= sum_{b in B_div} max(0, n - sum_e bad_e(b))`

| n | phi(n) | case2 tuples | proved by product | proved by per-fiber | proved by anchor-subset | min x0 exact | min lb_x0 product | min lb_x0 per-fiber | min |B_div| exact | min lb_Bdiv |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 3 | 2 | 48 | 48/48 | 48/48 | 32/48 | 2 | 2 | 2 | 2 | 2 |
| 4 | 2 | 330 | 60/330 | 318/330 | 312/330 | 4 | 0 | 0 | 3 | 3 |
| 5 | 4 | 1104 | 240/1104 | 388/1104 | 888/1104 | 8 | 0 | 0 | 4 | 4 |
| 6 | 2 | 15150 | 105/15150 | 11265/15150 | 15150/15150 | 10 | 0 | 0 | 5 | 5 |
| 7 | 6 | 70992 | 4896/70992 | 8544/70992 | 66312/70992 | 30 | 0 | 0 | 6 | 6 |

## Example failures of product bound
- n=3: none
- n=4: (1, 1, 4) (lb_Bdiv=3, lb_Ab=0, lb_x0=0, x0=6); (1, 1, 8) (lb_Bdiv=6, lb_Ab=0, lb_x0=0, x0=12); (1, 2, 4) (lb_Bdiv=3, lb_Ab=0, lb_x0=0, x0=4); (1, 2, 8) (lb_Bdiv=6, lb_Ab=0, lb_x0=0, x0=6); (1, 3, 4) (lb_Bdiv=7, lb_Ab=0, lb_x0=0, x0=4); (1, 3, 8) (lb_Bdiv=14, lb_Ab=0, lb_x0=0, x0=12)
- n=5: (1, 1, 1, 5) (lb_Bdiv=4, lb_Ab=0, lb_x0=0, x0=12); (1, 1, 2, 5) (lb_Bdiv=7, lb_Ab=0, lb_x0=0, x0=14); (1, 1, 3, 5) (lb_Bdiv=10, lb_Ab=0, lb_x0=0, x0=16); (1, 1, 4, 5) (lb_Bdiv=13, lb_Ab=0, lb_x0=0, x0=18); (1, 1, 5, 1) (lb_Bdiv=4, lb_Ab=0, lb_x0=0, x0=12); (1, 1, 5, 2) (lb_Bdiv=7, lb_Ab=0, lb_x0=0, x0=14)
- n=6: (1, 1, 1, 1, 6) (lb_Bdiv=5, lb_Ab=0, lb_x0=0, x0=20); (1, 1, 1, 2, 6) (lb_Bdiv=5, lb_Ab=0, lb_x0=0, x0=16); (1, 1, 1, 3, 6) (lb_Bdiv=5, lb_Ab=0, lb_x0=0, x0=16); (1, 1, 1, 4, 6) (lb_Bdiv=9, lb_Ab=0, lb_x0=0, x0=24); (1, 1, 1, 5, 6) (lb_Bdiv=21, lb_Ab=0, lb_x0=0, x0=48); (1, 1, 1, 6, 1) (lb_Bdiv=5, lb_Ab=0, lb_x0=0, x0=20)
- n=7: (1, 1, 1, 1, 1, 7) (lb_Bdiv=6, lb_Ab=0, lb_x0=0, x0=30); (1, 1, 1, 1, 2, 7) (lb_Bdiv=11, lb_Ab=0, lb_x0=0, x0=44); (1, 1, 1, 1, 3, 7) (lb_Bdiv=16, lb_Ab=0, lb_x0=0, x0=58); (1, 1, 1, 1, 4, 7) (lb_Bdiv=21, lb_Ab=0, lb_x0=0, x0=72); (1, 1, 1, 1, 5, 7) (lb_Bdiv=26, lb_Ab=0, lb_x0=0, x0=86); (1, 1, 1, 1, 6, 7) (lb_Bdiv=31, lb_Ab=0, lb_x0=0, x0=100)

## Example failures of per-fiber bound
- n=3: none
- n=4: (1, 1, 4) (lb_x0_fiber=0, x0=6); (1, 1, 8) (lb_x0_fiber=0, x0=12); (1, 2, 8) (lb_x0_fiber=0, x0=6); (1, 4, 1) (lb_x0_fiber=0, x0=6); (1, 8, 1) (lb_x0_fiber=0, x0=12); (1, 8, 2) (lb_x0_fiber=0, x0=6)
- n=5: (1, 1, 1, 5) (lb_x0_fiber=0, x0=12); (1, 1, 2, 5) (lb_x0_fiber=0, x0=14); (1, 1, 3, 5) (lb_x0_fiber=0, x0=16); (1, 1, 4, 5) (lb_x0_fiber=0, x0=18); (1, 1, 5, 1) (lb_x0_fiber=0, x0=12); (1, 1, 5, 2) (lb_x0_fiber=0, x0=14)
- n=6: (1, 1, 1, 1, 6) (lb_x0_fiber=0, x0=20); (1, 1, 1, 2, 6) (lb_x0_fiber=0, x0=16); (1, 1, 1, 3, 6) (lb_x0_fiber=0, x0=16); (1, 1, 1, 4, 6) (lb_x0_fiber=0, x0=24); (1, 1, 1, 5, 6) (lb_x0_fiber=0, x0=48); (1, 1, 1, 6, 1) (lb_x0_fiber=0, x0=20)
- n=7: (1, 1, 1, 1, 1, 7) (lb_x0_fiber=0, x0=30); (1, 1, 1, 1, 2, 7) (lb_x0_fiber=0, x0=44); (1, 1, 1, 1, 3, 7) (lb_x0_fiber=0, x0=58); (1, 1, 1, 1, 4, 7) (lb_x0_fiber=0, x0=72); (1, 1, 1, 1, 5, 7) (lb_x0_fiber=0, x0=86); (1, 1, 1, 1, 6, 7) (lb_x0_fiber=0, x0=100)

Artifacts:
- rows: `/tmp/lrc_case2_c2main_bounds_rows_v1.csv`
- summary: `/tmp/lrc_case2_c2main_bounds_summary_v1.md`
