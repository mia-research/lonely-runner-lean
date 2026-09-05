# Extremal-Multiplicity Progress on Lemma 8.1 (v1)

## Goal
Prove `x_0>0` universally from multiplicity constraints.

## What was attempted
### 1) Direct S4 scalar lower bound
From

`x_0 = N - S1 + S2 - S3 + S4 - sum_{q>=5} C(q-1,4)x_q`

and `C(q-1,4) <= ((m-4)/m) C(q,4)` (`m=n-1`), we get

`x_0 >= N - S1 + S2 - S3 + (4/m) S4`.

This bound works on earlier small grids, but is **not universal**.
Counterexample found in random higher-`n` sampling:
- `n=12`, tuple `(1,4,1,3,5,1,3,1,1,1,1)`, `L=60`
- bound value negative (`-385.45...`), while LP lower bound remains positive.

Conclusion: one-coefficient S4 scalar bound is too weak for `n=all`.

### 2) Full S4 LP extremal method
Using exact moments `(N,S1,S2,S3,S4)`, solve LP over histogram `x_q` to minimize `x_0`.
This is the strongest extremal argument from moments up to order 4.

Empirical status (exact moments, exact LP):
- Existing exhaustive grids (`n=3..8`): 100% proven under S4.
- Additional exhaustive checks:
  - `n=9`, `max_e=3`: `6559/6559` proven, min LP lb = `8`.
  - `n=10`, `max_e=3`: `19681/19681` proven, min LP lb = `9`.
  - `n=11`, `max_e=3`: `59047/59047` proven, min LP lb = `10`.
  - `n=12`, `max_e=2`: `2047/2047` proven, min LP lb = `11`.
  - `n=13`, `max_e=2`: `4095/4095` proven, min LP lb = `12`.
- Additional random checks:
  - `n=9..18`, 20 random tuples each (`e<=5`): `200/200` proven.

Observed pattern:
- Worst LP lower bound in exhaustive families above is attained at all-ones tuple and equals `n-1`.

## Updated proof strategy suggestion
The most promising global route is now:

1. **Promote a new universal lemma candidate**:
   `LP_S4(n,e_1,...,e_{n-1}) > 0` for all gcd-1 tuples.
2. Prove this by constructing an explicit dual feasible polynomial certificate (degree 4 in factorial basis) adapted to `m=n-1` and the exact moment identities of dangerous sets.
3. Use this to imply `x_0>0`, hence Lemma 8.1 and rational `n=all`.

This replaces the weaker scalar inequality route.
