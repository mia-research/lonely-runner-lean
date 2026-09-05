# C2-main(C) Universal Check: Counterexample

## Explicit counterexample
- `n=12`, `E=(12, 10, 5, 4, 7, 3, 6, 1, 8, 3, 11)`
- `phi(n)=4`, `x0=9386` (so `x0 >= phi` holds)
- `|B_div|=7701`, `C_bad=3919`, `B_safe=3782`
- `I_bad=85652`, `P_bad=78354`, `T_bad=91764`
- `lhs = I_bad-P_bad+T_bad = 99062`
- `rhs = n(|B_div|-(n-1)) = 92280`
- `C2-main(C)`: `lhs <= rhs` is **False**

Conclusion: C2-main(C) is **not universally true**.

## Small random incidence scan (Case-2 tuples)
| n | max_e | samples | violations of C2-main(C) |
|---:|---:|---:|---:|
| 10 | 12 | 120 | 0 |
| 11 | 12 | 100 | 0 |
| 12 | 12 | 100 | 0 |
| 13 | 14 | 80 | 0 |

Interpretation: bounded-grid success at small n does not extend as a universal theorem for C2-main(C).
