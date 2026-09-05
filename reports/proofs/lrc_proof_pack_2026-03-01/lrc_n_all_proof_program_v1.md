# LRC `n=all` Proof Program (v1)

## Target theorem
For every `n >= 3`, every distinct speed set, and every runner `i`, there exists `t` such that runner `i` is isolated at threshold `1/n`.

## Normalized rational form
Fix runner `i` as stationary. For rational/resonant case, reduce to integers:
- relative speeds `e_1,...,e_m` with `m=n-1`, `gcd(e_j)=1`
- `L=lcm(e_j)`, `N=nL`, lattice points `k in Z_N`, `s_k=k/N`
- dangerous sets `D_e subset Z_N`.

Need: `|U_e D_e| < N`.

## Exact combinatorial identity (all n)
Let `x_r` = number of lattice points covered by exactly `r` dangerous sets (`r=0..m`).
Define moment sums:
- `S_k = sum_{|I|=k} |cap_{e in I} D_e| = sum_{r=k}^m C(r,k) x_r`.

Then exactly:

`x_0 = N + sum_{k=1}^m (-1)^k S_k`.

So proving positivity reduces to proving this alternating sum is `>0`.

## What is already established
- Exact formulas/algorithms for `S1,S2,S3,S4` (validated by brute force).
- Exhaustive bounded scans (`n=3..8` grids used in artifacts) show no counterexample.
- With S4 moments, LP forcing proves all scanned tuples (`100%` in those grids).
- Structural closures:
  - `n=5`: exact `x0 = N-S1+S2-S3+S4`.
  - `n=6`: `x0 = N-S1+S2-S3+S4-x5`, and bound via `S4=x4+5x5` gives strict positivity on all scanned tuples.

## Continuum note (rational ↔ irrational)
“irrationals lie between rationals” is not by itself a proof step.
To transfer by continuity, one needs robust witnesses (`gap > 1/n` with margin), not only boundary-equality witnesses.
So the rigorous route is:
1. irrational/full-rank theorem (measure-positive safe set via equidistribution), and
2. rational/resonant theorem (finite lattice inequality above).

## Single remaining universal lemma
Prove for all `n` and all gcd-1 integer tuples:

`N + sum_{k=1}^m (-1)^k S_k > 0`.

Equivalent: dangerous sets never cover all `N` lattice points.

This is now a finite arithmetic-combinatorics statement on residue systems.

## Immediate proof plan
1. Derive closed-form/good bounds for `S_k` at general `k` using CRT-lift representation.
2. Prove alternating-sum positivity directly (or by sharp bounds on top multiplicities `x_{m-1},x_m`).
3. Package as rational theorem; combine with irrational theorem for full `n=all` statement.
