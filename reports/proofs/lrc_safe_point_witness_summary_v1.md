# Safe-Point Witness Survey (v1)

**Question:** For each gcd-1 tuple E, do the A_n witnesses
k = j*L with gcd(j,n)=1 remain safe (not in any D_e)?

If ALL tuples have all phi(n) witnesses surviving:
  → Lemma E proved: x_0(E) >= phi(n) for all gcd-1 E  (uniform witnesses).

## Per-n Results

| n | phi(n) | max_e | gcd-1 tuples | all survive | partial | none | % all survive |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 3 | 2 | 12 | 91 | 43 | 0 | 48 | 47.3% |
| 4 | 2 | 9 | 637 | 307 | 0 | 330 | 48.2% |
| 5 | 4 | 7 | 2303 | 1199 | 0 | 1104 | 52.1% |
| 6 | 2 | 5 | 3091 | 3091 | 0 | 0 | 100.0% |

## Global Verdict

**RESULT: 1482 tuples have at least one A_n witness that is NOT safe.**

The k=j*L witnesses do NOT universally generalize.
See failures CSV for details; look for twisted witnesses or alternative routes.
