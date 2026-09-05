# G4.OPEN Case-B Interval Lemmas (v1)
**Date:** 2026-03-07  
**Purpose:** package the salvageable interval facts from the attempted `G4.OT` draft as auxiliary lemmas for the fixed-side `Miss(r)` program.

## 0) Scope and use
Work in the near-complete one-div Case-B / Case-iiib framework:
- composite `n >= 10`,
- `E_fix = {1,...,n-1} \ {a,b}`,
- `|E_fix| = n-3`,
- `I_div = [1/n, (n-1)/n]`,
- `Cov_e(r) = union_{t: r in bad_set(e,t,n)} ([t/e,(t+1)/e) intersect I_div)`.

This note does **not** claim Case-B closure.
It only isolates two fixed-side interval lemmas for the residue `r=1`.

## 1) Unit coverability threshold for `r=1`

### Lemma CI.1 (coverability threshold)
Let `e` be a unit runner (`gcd(e,n)=1`).
Then residue `1` lies in `bad_set(e,t,n)` for some floor value `t in {0,...,e-1}` if and only if

`e >= ceil(n/2)`.

Equivalently:
- if `e < ceil(n/2)`, then `Cov_e(1) = emptyset`,
- if `e >= ceil(n/2)`, then `Cov_e(1) != emptyset`.

### Proof
For unit `e`,

`bad_set(e,t,n) = { (-t)e^{-1}, (-(t+1))e^{-1} } (mod n)`.

So `1 in bad_set(e,t,n)` iff

`t == -e (mod n)` or `t == -e-1 (mod n)`.

Because `0 <= t <= e-1 < n`, these congruences can only occur as:
- `t = n-e`,
- `t = n-e-1`.

The first is admissible iff `n-e <= e-1`, i.e.

`e >= (n+1)/2`.

The second is admissible iff `n-e-1 <= e-1`, i.e.

`e >= n/2`.

Together this is exactly

`e >= ceil(n/2)`.

If `e < ceil(n/2)`, neither candidate `t` is available, so `Cov_e(1)=emptyset`. ∎

### Corollary CI.1a (active set for `r=1`)
Define

`E_large(1) := { e in E_fix : gcd(e,n)=1 and e >= ceil(n/2) }`.

Interpretation:
- all unit runners below `ceil(n/2)` are inert for `r=1`,
- among unit runners, only the large unit runners can contribute to fixed-side coverage of `r=1`,
- any non-unit contribution to `Cov(1)` must be handled separately in the full Case-B theorem.

## 2) Contiguous interval structure

### Lemma CI.2 (contiguous `alpha` interval on `[0,1]`)
Let `e` be a unit runner with `e >= ceil(n/2)`.
Then the full `alpha`-coverage set of residue `1` on `[0,1]` is exactly

`Cov_e^{full}(1) = [ (n-e-1)/e, (n-e+1)/e )`.

In particular, `Cov_e^{full}(1)` is a single contiguous interval of length `2/e`.

### Proof
By Lemma CI.1, the only floor values that can cover residue `1` are

`t_1 = n-e-1`,
`t_2 = n-e`.

These are adjacent integers, so the corresponding floor intervals are

`[(n-e-1)/e, (n-e)/e)`

and

`[(n-e)/e, (n-e+1)/e)`.

Their union is the stated interval, of length `2/e`. ∎

### Corollary CI.2a (restriction to `I_div`)
Inside the Case-B working interval `I_div`,

`Cov_e(1) = Cov_e^{full}(1) intersect I_div`.

Hence `Cov_e(1)` is still a single contiguous interval, with endpoints drawn from

`{ (n-e-1)/e, (n-e+1)/e, 1/n, (n-1)/n }`.

So all coverage components for residue `1` contributed by active unit runners remain interval-shaped after restriction to `I_div`.

## 3) Program use
These lemmas are support facts for the existence-only Case-B target:

`exists r with Miss(r) != empty`.

What they provide:
- a clean active/inert split for the test residue `r=1`,
- exact interval structure for the unit-runner coverage pieces of `Cov_e(1)`.

What they do **not** provide:
- they do not prove `Miss(1) != empty`,
- they do not control non-unit contributions,
- they do not close `SL1-O1`.

So they should be used as auxiliary input to the fixed-side `Miss(r)` program, not as a closure theorem.

## 4) Status
`PROVED` as auxiliary interval lemmas; Case-B existence remains `OPEN`.
