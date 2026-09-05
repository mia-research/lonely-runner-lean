# Odd Period-3 Scope Lock

## Goal

The current odd-cycle theorem path is **not** trying to prove a full odd-cycle
classification in one jump.

The sharp remaining claim is narrower:

> every odd period-3 attractor is affine-`delta`.

Everything else should now be treated as supporting machinery for that claim,
not as a competing research direction.

## What “affine-`delta`” means

An odd period-3 attractor is affine-`delta` if its three phases can be written
as

- `R0_delta(u,v,w,x,y) = [u,v,w,x,y,y,x,w,v,u+delta]`
- `R1_delta(u,v,w,x,y) = [u,y,v,x,w,w,x,v,y,u+delta]`
- `R2_delta(u,v,w,x,y) = [u,w,y,x,v,v,x,y,w,u+delta]`

for some positive odd `delta`.

So the global theorem debt has two parts:

1. **symmetry/completeness**
   show every odd period-3 attractor has pairwise symmetry
   `c1=c8, c2=c7, c3=c6, c4=c5`
   and a constant odd defect `delta = c9-c0`
2. **level structure**
   show the resulting affine-`delta` levels are exactly the ones already
   appearing in the internal grammar

The second part is already mostly under control:

- reduced sector gives `delta=1`
- boundary-thread entrance gives explicit access to `delta=3`
- the exact lift `delta -> delta+2` gives all positive odd `delta`

So the real unresolved theorem debt is now the first part:

> prove global odd period-3 pairwise symmetry.

## What is already solved and should not distract us

- fixed-point `d=all` base-10 side
- reduced odd period-3 affine cone
- boundary-thread entrance into `delta=3`
- exact affine lift across odd `delta`

These are no longer the open problem.

## What a good next move looks like

A useful next step must do one of:

1. produce a new invariant that forces pairwise symmetry on odd period-3
   attractors, or
2. audit the full odd period-3 universe at low/moderate dimensions to test
   whether any counterexample to affine-`delta` exists

A step that only adds another affine family or another shell count without
tightening one of those two points is drift.

## Current audit checkpoint

The global sample audit now covers the second item in a disciplined way:

- across `5000` random full odd count states at each of
  `d=19,21,23,25,27,29,31,33,39,45,55`,
  every sampled period-3 attractor was affine-`delta`

and the observed `delta` levels were exactly:

- only `delta=1` up through `d=33`
- `delta=1,3` by `d=39,45`
- `delta=1,3,5` by `d=55`

So the next non-drifting move is now clearly the first item:

> produce a symbolic invariant that forces pairwise symmetry on odd period-3
> attractors.

## New bridge

The phase-sum bridge now makes the shape of that next proof step clearer.

For every currently verified affine odd period-3 cycle, the phase-sum vector

- `S = C0 + C1 + C2`

is itself a fixed point, and in fact lands on the symmetric fixed-point
branch:

- `S = [3u,M,M,3x,M,M,3x,M,M,3u+3delta]`.

So the clean theorem path is now:

1. force global odd period-3 attractors into affine-`delta`
2. then use the fixed-point shadow `S` as the structural anchor

That is much better than trying to prove the global odd cycle grammar
independently from scratch.

## New reduction

There is now a sharper theorem-facing reduction:

> if an odd period-3 attractor satisfies
> 1. phase-sum fixedpoint, and
> 2. phasewise asymmetry constancy,
> then pairwise symmetry is forced.

The reason is simple but strong:

- the phase-sum shadow `S=C0+C1+C2` is then a fixed point whose inner
  asymmetry is divisible by `3`
- but the fixed-point theorem allows only two inner asymmetry types:
  - zero
  - the classical `6174` type `(1,-1,-1,1)`
- the classical type is not divisible by `3`

So the fixed-point shadow cannot be classical, and the inner complementary-pair
asymmetries of the cycle must vanish.

That means the real unresolved theorem debt is now even narrower:

1. prove phase-sum fixedpoint globally on odd period-3 attractors
2. prove phasewise asymmetry constancy globally on odd period-3 attractors

Once those land, pairwise symmetry follows automatically, and the affine-`delta`
normal form is no longer just an empirical fit.

## Stronger asymmetry profile

The newest asymmetry-profile audit sharpens the second item again.

Across all currently exposed odd period-3 sectors, the observed asymmetry is
not merely constant. It is exactly

- `A(C) = (delta,0,0,0,0)`

phasewise.

So the live theorem debt is now best read as:

1. prove phase-sum fixedpoint globally on odd period-3 attractors
2. prove exact asymmetry-profile collapse
   `A(C)=(delta,0,0,0,0)` globally

Once those land, pairwise symmetry is automatic, and the affine-`delta` form
is no longer just an empirical fit.
