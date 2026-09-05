# C2-main Closure Plan (v1)

## Objective
Close Case 2 by proving:

`x0(E) >= phi(n)` for all gcd-1 tuples `E` with some `e_r ≡ 0 (mod n)`.

## Fixed decomposition
With `k=aL+b`, `L=lcm(E)`, `N=nL`, `E=E_div ⊔ E_non`:

`x0(E) = sum_{b in B_div} |A_b|`,

where `B_div` is determined only by `E_div`, and `A_b` by `E_non` on the fiber over `b`.

## What is already explicit/proved
1. `|B_div|` machinery is explicit:
   - exact single-divisible counts,
   - Bonferroni-1 lower bound,
   - anchor criterion (`b=jL/n`).
2. Uniform `|A_b|` lower bound exists, but is too weak globally.
3. Empirical invariant in current exhaustive scans: `|B_safe| >= n-1` (no violations in tested Case-2 grids).

## Remaining universal inequality (equivalent forms)
Any one of the following would close Case 2:
1. `|B_safe| >= n-1`.
2. `sum_{b in B_div} |A_b| >= phi(n)`.
3. `sum_{b in B_div} 1_{|A_b|>0} >= n-1`.

## Proof program (next hard step)
### Lemma C2.3 (bad-fiber incidence lower threshold)
For each fiber `b`, define bad-coverage profile on `a in {0,...,n-1}` from `E_non`.
Derive a necessary inequality for complete coverage (`A_b=0`) in terms of residue-pattern counts of non-divisible speeds.

Target output: an explicit per-fiber obstruction inequality that forbids `A_b=0` on at least `n-1` admissible fibers.

### Lemma C2.4 (residue-pattern counting over `B_div`)
Count how often each obstruction pattern can occur over admissible `b` values, using the periodic structure induced by `E_div`.

Target output: upper bound on number of bad fibers `|B_div \ B_safe|` that implies `|B_safe|>=n-1`.

### Theorem C2-main
Combine C2.3 + C2.4:

`|B_safe|>=n-1`  =>  `x0(E)>=|B_safe|>=n-1>=phi(n)`.

## Equality clause (must be kept)
`n=3`, tuples `(1,3)` and `(3,1)` give equality: `x0=phi(3)=2`.
So final theorem statement must remain non-strict (`>=`).

