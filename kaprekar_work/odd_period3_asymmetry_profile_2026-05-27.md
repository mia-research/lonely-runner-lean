# Odd Period-3 Asymmetry-Profile Audit

## Purpose

The last reduction note showed:

> if odd period-3 attractors satisfy
> 1. phase-sum fixedpoint, and
> 2. phasewise asymmetry constancy,
> then pairwise symmetry is forced.

This note records a stronger empirical fact:

> every currently exposed odd period-3 attractor already has the exact
> asymmetry profile
> `A(C) = (delta,0,0,0,0)`
> phasewise.

So the live theorem debt is now sharper than “prove asymmetry constancy.”
The real target is:

> prove exact asymmetry-profile collapse to the pure outer odd defect.

## Profile

Write

- `A(C) = (c9-c0, c8-c1, c7-c2, c6-c3, c5-c4)`.

The currently observed global odd period-3 profile is:

- `A(C) = (delta,0,0,0,0)`

with one common odd `delta` across the three phases of the cycle.

So the only nonzero asymmetry is the outer excess of `9`s over `0`s.
All inner complementary pairs are already balanced phasewise.

## Exact reduced sector

On the exact reduced odd period-3 census at

- `d=23`
- `d=25`
- `d=27`
- `d=29`

every period-3 attractor satisfies this profile.

Exact counts:

- `d=23`: `10/10`, all with `delta=1`
- `d=25`: `21/21`, all with `delta=1`
- `d=27`: `39/39`, all with `delta=1`
- `d=29`: `66/66`, all with `delta=1`

So the whole exact reduced sector already lives on the pure-outer-defect line.

## Boundary-tail sector

For the boundary-thread period-3 tail

- `Z0(r) = [1,r,4,4,4,4,4,4,r,4]`
- `Z1(r) = [1,4,r,4,4,4,4,r,4,4]`
- `Z2(r) = [1,4,4,4,r,r,4,4,4,4]`

every checked `r=5..24` also satisfies the same profile, now with

- `delta=3`.

So the explicit `delta=3` entrance line is already fully compatible with the
same asymmetry collapse.

## Sampled global odd universe

The full-state sample audit was re-read through the stronger asymmetry lens.
Across `5000` random odd count states at each of

- `d=19,21,23,25,27,29,31,33,39,45,55`,

every sampled distinct period-3 attractor again satisfied the exact profile

- `(delta,0,0,0,0)`.

Observed `delta` support:

- `d<=33`: only `delta=1`
- `d=39,45`: `delta in {1,3}`
- `d=55`: `delta in {1,3,5}`

So the higher affine levels do not introduce new inner asymmetry behavior.
They only raise the outer odd defect.

## Meaning

This is a materially better formulation of the remaining theorem target.

Before this note, the live odd period-3 debt read as:

1. prove phase-sum fixedpoint globally
2. prove phasewise asymmetry constancy globally

After this note, the second item sharpens to:

2. prove exact asymmetry-profile collapse
   `A(C)=(delta,0,0,0,0)` globally

That is a more rigid statement, but it is also a better theorem language,
because it matches every currently exposed odd period-3 sector exactly.

## Relation to the pairwise-symmetry reduction

The pairwise-symmetry reduction note still matters:

- if `K(C0+C1+C2)=C0+C1+C2`
- and the asymmetry profile is constant across phases

then pairwise symmetry follows from the fixed-point theorem.

This note strengthens the second premise empirically:

- the currently exposed cycles are not merely constant in asymmetry
- they already have zero inner asymmetry phasewise

So the global odd period-3 theorem path is now best read as:

1. prove phase-sum fixedpoint globally
2. prove exact asymmetry-profile collapse globally
3. inherit pairwise symmetry and then affine-`delta`

## Computational support

Runner:

- `kaprekar_odd_period3_asymmetry_profile_audit.py`

Output:

- `kaprekar_odd_period3_asymmetry_profile_audit_2026-05-27.json`
