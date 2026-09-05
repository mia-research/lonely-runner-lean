# Boundary Thread Entrance Into Affine Level `delta=3`

## Purpose

One of the remaining global odd-cycle questions was:

> how do the non-period-3 odd sectors feed into the affine hierarchy?

The explicit boundary thread `K_p` now answers that directly for the first
higher affine level.

## Thread and entrance law

Recall the boundary thread

- `K_p = [0,p,3,3,3,3,3,3,p,3]`

of dimension

- `d = 21 + 2p`.

The exact entrance law is:

> for every `p >= 8`,
> `K^12(K_p) = Z0(p-4)`

where

- `Z0(r) = [1,r,4,4,4,4,4,4,r,4]`

is the phase-0 state of the affine level-`3` family

- `R0_3(1,r,4,4,4)`.

So the boundary thread does not merely *eventually* hit the level-`3` tail.
It enters it after an exact constant time:

- `12` Kaprekar steps

for every tested `p>=8`.

## Low-parameter phase picture

The same thread therefore reads as:

- `p=1,2`: period `2`
- `p=3`: fixed
- `p=4..7`: period `5` after finite preperiod
- `p=8`: fixed, and also `K^12(K_8)=Z0(4)`
- `p>=9`: enters the level-`3` affine period-3 family after exactly `12`
  steps

This is the cleanest current example of a non-period-3 odd sector feeding into
the affine hierarchy.

## Meaning

This strengthens the global theorem path in two ways:

1. it shows that the boundary thread is not a side correction to the period-3
   grammar; it is an explicit entrance channel into affine level `delta=3`
2. it shows that at least one non-period-3 odd sector feeds into the affine
   hierarchy by an exact finite-time rule, rather than by vague asymptotic
   behavior

So the odd-cycle side is starting to acquire the right kind of grammar
structure:

- affine period-3 levels
- shell lifts between levels
- explicit entrance channels from non-period-3 sectors

## Computational support

The script

- `kaprekar_boundary_thread_affine_entrance.py`

verifies:

- `K^12(K_p)=Z0(p-4)` for `p=8..40`

with zero failures, and records the low-parameter phase table in

- `kaprekar_boundary_thread_affine_entrance_2026-05-19.json`.
