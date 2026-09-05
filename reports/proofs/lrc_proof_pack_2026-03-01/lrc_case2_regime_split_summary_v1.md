# Case-2 Regime Split Scan (v1)

Regimes:
- Anchor regime: `L=n`
- Slack regime: `L>n`

## Canonical family `(1,...,1,n)`
| n | tuple | L | B_div | C_bad | B_safe | x0 | phi(n) |
|---:|---|---:|---:|---:|---:|---:|---:|
| 3 | `(1, 3)` | 3 | 2 | 0 | 2 | 2 | 2 |
| 4 | `(1, 1, 4)` | 4 | 3 | 0 | 3 | 6 | 2 |
| 5 | `(1, 1, 1, 5)` | 5 | 4 | 0 | 4 | 12 | 4 |
| 6 | `(1, 1, 1, 1, 6)` | 6 | 5 | 0 | 5 | 20 | 2 |
| 7 | `(1, 1, 1, 1, 1, 7)` | 7 | 6 | 0 | 6 | 30 | 6 |

## Exhaustive bounded Case-2 grids
| n | tuples | min B_safe overall | min B_safe (L=n) | min B_safe (L>n) | tight count (B_safe=n-1) | tight with L=n | tight profile mismatches |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 3 | 48 | 2 | 2 | 3 | 2 | 2 | 0 |
| 4 | 330 | 3 | 3 | 4 | 12 | 12 | 0 |
| 5 | 1104 | 4 | 4 | 7 | 14 | 14 | 0 |
| 6 | 15150 | 5 | 5 | 9 | 720 | 720 | 0 |
| 7 | 70992 | 6 | 6 | 11 | 62 | 62 | 0 |

## Non-canonical high-C_bad example
For `n=5`, `E=(1, 3, 4, 5)`: `L=60`, `B_div=37`, `C_bad=29`, `B_safe=8`, `x0=8`, `phi(5)=4`.

## Random stress for anchor regime L=n (higher n)
| n | tested tuples (L=n) | violations of (B_div=n-1, C_bad=0, B_safe=n-1) |
|---:|---:|---:|
| 8 | 298 | 0 |
| 9 | 342 | 0 |
| 10 | 349 | 0 |
| 11 | 349 | 0 |
| 12 | 348 | 0 |
| 14 | 350 | 0 |
| 15 | 350 | 0 |
| 16 | 336 | 0 |
| 18 | 350 | 0 |
| 20 | 350 | 0 |
