# Case-2 Aggregate Deficit Scan (v1)

Target tested:
- Strong form: `x0 >= n-1` (implies `x0 >= phi(n)`).
- Also records `safe_anchor` and `lower_band_safe` to stress-test sub-arguments.

## Exhaustive Block (n=3..7)

| n | phi(n) | tuples | min x0 | min B_safe | min safe anchors | min lower-band-safe | viol(x0>=n-1) | viol(x0>=phi) |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 3 | 2 | 48 | 2 | 2 | 0 | 0 | 0 | 0 |

- n=3 min-x0 example: `E=(1, 3)`, `L=3`, `x0=2`, `B_safe=2`
- n=3 min-anchor example: `E=(1, 9)`, `safe_anchor=0`, `x0=6`
- n=3 min-lower-band-safe example: `E=(3, 4)`, `lower_band_safe=0`, `x0=6`

| 4 | 2 | 330 | 4 | 3 | 0 | 0 | 0 | 0 |

- n=4 min-x0 example: `E=(1, 2, 4)`, `L=4`, `x0=4`, `B_safe=3`
- n=4 min-anchor example: `E=(1, 7, 8)`, `safe_anchor=0`, `x0=16`
- n=4 min-lower-band-safe example: `E=(1, 4, 5)`, `lower_band_safe=0`, `x0=8`

| 5 | 4 | 1104 | 8 | 4 | 2 | 0 | 0 | 0 |

- n=5 min-x0 example: `E=(1, 3, 4, 5)`, `L=60`, `x0=8`, `B_safe=8`
- n=5 min-anchor example: `E=(1, 2, 3, 5)`, `safe_anchor=2`, `x0=10`
- n=5 min-lower-band-safe example: `E=(1, 1, 5, 6)`, `lower_band_safe=0`, `x0=30`

| 6 | 2 | 15150 | 10 | 5 | 1 | 0 | 0 | 0 |

- n=6 min-x0 example: `E=(1, 2, 3, 4, 6)`, `L=12`, `x0=10`, `B_safe=9`
- n=6 min-anchor example: `E=(2, 5, 6, 7, 8)`, `safe_anchor=1`, `x0=212`
- n=6 min-lower-band-safe example: `E=(1, 1, 1, 6, 7)`, `lower_band_safe=0`, `x0=72`

| 7 | 6 | 70992 | 30 | 6 | 2 | 1 | 0 | 0 |

- n=7 min-x0 example: `E=(1, 1, 1, 1, 1, 7)`, `L=7`, `x0=30`, `B_safe=6`
- n=7 min-anchor example: `E=(1, 1, 3, 4, 5, 7)`, `safe_anchor=2`, `x0=142`
- n=7 min-lower-band-safe example: `E=(1, 1, 1, 1, 6, 7)`, `lower_band_safe=1`, `x0=100`

## Random Stress (n=8..12, L capped)

- L cap in this pass: `3000`

| n | kept tuples | min x0 | min B_safe | min safe anchors | viol(x0>=n-1) | viol(x0>=phi) |
|---:|---:|---:|---:|---:|---:|---:|
| 8 | 220 | 52 | 19 | 3 | 0 | 0 |
| 9 | 220 | 154 | 57 | 4 | 0 | 0 |
| 10 | 200 | 164 | 33 | 4 | 0 | 0 |
| 11 | 180 | 550 | 109 | 10 | 0 | 0 |
| 12 | 150 | 122 | 21 | 7 | 0 | 0 |

## Key Diagnostic Conclusion

- In tested data, `x0 >= n-1` had zero violations.
- Anchor-only route is insufficient (`safe_anchor` can be below `phi(n)`, including 0).
- Lower-band-only route is insufficient (`lower_band_safe` can be 0).
- Therefore the remaining theorem step must use global feasible-pattern/coverage structure, not a single local band or anchor subset.
