# G1.G.2 Analytic Blockers (Current)
**Date:** 2026-03-03

## Objective context

Remaining open target is the bounded-strip uniform claim `(G1.G.2)` from `v11` §17.12.

## Blocker A: Anchor-sum shortcut fails

Tested claim (candidate):

`sum_{j=0}^{n-1} delta(b_j) >= n-1`, with anchors `b_j = jL/n`.

Counterexample found:

- `n=8`
- fixed template speeds `(1,2,3,4,5)`
- free speed `M=7`
- computed anchor sum: `sum_j delta(b_j)=6 < n-1=7`.

Conclusion: anchor-sum by itself cannot close `(G1.G.2)`.

## Blocker B: Lower+top guaranteed-safe-only shortcut fails

Tested claim (candidate):

`|I_lo|+|I_hi| >= n-1` always (using only guaranteed-safe canonical bands).

Counterexample found:

- `n=7`
- fixed speeds `(1,2,3,6)`
- free speed `M=1`
- guaranteed-safe count: `|I_lo|+|I_hi|=3 < n-1=6`.

Conclusion: lower+top guaranteed-safe fibers alone are insufficient for full closure.

## Implication

A valid proof of `(G1.G.2)` must use additional global structure beyond:

1. anchor-only mass, and
2. canonical guaranteed-safe bands alone.

This is consistent with prior scope guardrails and keeps Gap 1 open at genuine analytic
 de-enumeration difficulty.
