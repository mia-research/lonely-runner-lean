# n=5,6 Structural Lemma Note (v1)

## What S3 left unresolved
- `n=5`: 72 tuples unresolved by moments up to S3
- `n=6`: 360 tuples unresolved by moments up to S3

Top unresolved S3 prototype families (sorted tuples):
- `n=6`, tuple=(1, 2, 3, 4, 5), multiplicity=120
- `n=6`, tuple=(1, 1, 3, 4, 5), multiplicity=60
- `n=6`, tuple=(1, 3, 3, 4, 5), multiplicity=60
- `n=6`, tuple=(1, 3, 4, 4, 5), multiplicity=60
- `n=6`, tuple=(1, 3, 4, 5, 5), multiplicity=60
- `n=5`, tuple=(1, 3, 4, 5), multiplicity=24
- `n=5`, tuple=(1, 3, 4, 7), multiplicity=24
- `n=5`, tuple=(1, 4, 5, 6), multiplicity=24

## Structural closure with S4
### n=5 (m=4 dangerous sets): exact identity
For multiplicity histogram `x_r` on `r=0..4`:
- `safe = x_0 = N - S1 + S2 - S3 + S4`
Checked on all n=5 rows: `violations = 0`.
- verified rows: 2303

### n=6 (m=5 dangerous sets): lower-bound identity
With `x_5` the all-five-dangerous count:
- `safe = N - S1 + S2 - S3 + S4 - x_5`
And from `S4 = x_4 + 5 x_5`, we get `x_5 <= floor(S4/5)`.
Hence universal lower bound:
- `safe >= N - S1 + S2 - S3 + S4 - floor(S4/5)`
Across all n=6 rows, this lower bound was strictly positive in every case (min=1).
- bound failures (<=0): 0
Worst-case examples (lb minimal):
- tuple `1 2 3 4 5`: safe=2, S4=121, lb=1
- tuple `1 2 3 5 4`: safe=2, S4=121, lb=1
- tuple `1 2 4 3 5`: safe=2, S4=121, lb=1
- tuple `1 2 4 5 3`: safe=2, S4=121, lb=1
- tuple `1 2 5 3 4`: safe=2, S4=121, lb=1
- tuple `1 2 5 4 3`: safe=2, S4=121, lb=1
- tuple `1 3 2 4 5`: safe=2, S4=121, lb=1
- tuple `1 3 2 5 4`: safe=2, S4=121, lb=1
- tuple `1 3 4 2 5`: safe=2, S4=121, lb=1
- tuple `1 3 4 5 2`: safe=2, S4=121, lb=1

## S4 unresolved status
- unresolved tuples under S4 for n=5,6: 0
