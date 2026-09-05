# n=7 B_div Gap Structure (v1)

## Bounded exhaustive regime (from `lrc_case2_regime_split_rows_v1.csv`)
Constraint: `|E|=n-1`, Case-2 tuples, bounded grid used in scan (`max_e=7`).

- tuple count: `70992`
- distinct `B_div` values: `[6, 11, 16, 21, 26, 31, 51, 61, 76, 101, 151, 301]`
- anchor value `n-1=6`; next value `11`; skipped `[7, 8, 9, 10]`
- missing count in full interval [6,301]: `284`

### Structural description in this bounded grid
All divisible speeds are necessarily `7` (since `max_e=7`), so `E_div` profile is only `f=1`.
For `L=7m`, observed formula is exactly:
- `B_div = 5m + 1 = 5L/7 + 1`.
This yields values `{6,11,16,21,26,31,51,61,76,101,151,301}` for the observed `m` set.

## Extended profile sampling (max_e=14, L<=420)
Allowing divisible speeds `7` and `14` produces three affine families in `m=L/14`:

| f-profile | observed law | sample values |
|---|---|---|
| `(1,)` | `B_div = 10m + 1` | m=4: 41, m=6: 61, m=9: 91, m=10: 101, m=12: 121, m=15: 151 |
| `(2,)` | `B_div = 10m + 2` | m=3: 32, m=5: 52, m=6: 62, m=9: 92, m=10: 102, m=12: 122 |
| `(1, 2)` | `B_div = 8m + 2` | m=2: 18, m=3: 26, m=4: 34, m=9: 74, m=10: 82, m=15: 122 |

Verification in the random sample: all tested tuples in these families matched the stated formulas exactly.

## Interpretation
The `B_div` gaps are arithmetic-lattice effects from divisible-speed residue maps, not random holes.
For `n=7`, the first gap is structural: no values in `{7,8,9,10}` under the bounded (`max_e=7`) grid; with `14` allowed, value `10` appears via mixed `(1,2)` profile while `7,8,9` remain absent in sampled data.
