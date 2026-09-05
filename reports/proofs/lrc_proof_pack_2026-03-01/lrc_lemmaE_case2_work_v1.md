# Lemma E — Case 2 Work Note (v1)

## Scope
Case 2 means:

- normalized integer tuple `E=(e_1,...,e_{n-1})`, `gcd(E)=1`
- at least one component is divisible by `n`:
  `exists r: e_r ≡ 0 (mod n)`.

Goal (corrected): prove

`x_0(E) >= phi(n)`.

## Correction to prior claim
The stronger claim `x_0(E) > phi(n)` is **not universally true**:
- counterexample at `n=3`: `E=(1,3)` has `x_0=2=phi(3)`.

So the mathematically defensible Case-2 target is `>=`, not strict `>`.

## Exact facts already established
### Fact A (Case-1 witnesses)
If no `e_r` is divisible by `n`, then AP witnesses `k=jL` (`gcd(j,n)=1`) are safe.

### Fact B (Witness failure trigger)
If some `e_r` is divisible by `n`, then every AP witness `k=jL` fails that constraint:

`e_r * jL ≡ 0 (mod nL)`.

Hence Case 2 needs a different witness family.

## Useful decomposition for Case 2
Write every lattice point as

`k = aL + b`, with `a in {0,...,n-1}`, `b in {0,...,L-1}`.

For a multiple-of-`n` speed `e=nf`:

`e*k mod nL = n f b mod nL`,

so this constraint is independent of `a`.

### Lemma C2.1 (a-invariance of divisible constraints)
Divisible-speed constraints only filter `b`, not `a`.

Proof: immediate from `n f (aL) = a f (nL) ≡ 0 (mod nL)`.

This gives a structural split:
1. choose `b` surviving all divisible constraints,
2. then solve non-divisible constraints over `a`.

## Empirical checkpoint (bounded exhaustive grids)
From exact checks on current bounded grids:
- `n=3`: case-2 minimum `x_0 = 2 = phi(3)`
- `n=4`: case-2 minimum `x_0 = 4 > phi(4)=2`
- `n=5`: case-2 minimum `x_0 = 8 > phi(5)=4`
- grids for `n>=6` used earlier had `max_e<n`, so no case-2 tuples there.

## Proof route for Case 2 (next)
### Target lemma C2-main
For every case-2 tuple `E`, `x_0(E) >= phi(n)`.

### Proposed route
1. Define `B_div` = set of `b` surviving all divisible-speed constraints.
2. For each `b in B_div`, define `A_b` = set of `a` such that `k=aL+b` survives all non-divisible constraints.
3. Prove a uniform lower bound on total survivors:
   `sum_{b in B_div} |A_b| >= phi(n)`.

The key technical step is controlling `A_b` via residue action of non-divisible `e_r mod n` on `a`.

## Why this is enough
Lemma E only needs AP-core extremality in safe-count form:

`x_0(E) >= x_0(A_n) = phi(n)`.

Case 1 already gives this via AP witnesses.
Case 2 closes Lemma E once C2-main is proved.
