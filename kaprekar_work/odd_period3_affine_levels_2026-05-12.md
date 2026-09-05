# Odd Period-3 Affine Levels

## Purpose

The current odd cycle picture had two separate period-3 stories:

- the reduced high-minus-low=`1` affine rotor cone
- the boundary-thread tail `Z_r`

This note records the cleaner synthesis:

> both are levels of the same odd affine period-3 normal form,
> distinguished by the `9-0` asymmetry level
> `delta = c9 - c0`.

So the boundary thread is no longer just a side correction to the odd
period-3 grammar. Its tail is an explicit second affine level.

## General odd affine-delta normal form

Define the three phase states

- `R0_delta(u,v,w,x,y) = [u, v, w, x, y, y, x, w, v, u+delta]`
- `R1_delta(u,v,w,x,y) = [u, y, v, x, w, w, x, v, y, u+delta]`
- `R2_delta(u,v,w,x,y) = [u, w, y, x, v, v, x, y, w, u+delta]`

Whenever a period-3 orbit has this form, its three-phase count sum is forced
to be

- `[3u, M, M, 3x, M, M, 3x, M, M, 3u+3delta]`

with `M = v+w+y`.

So the affine levels are visible both phasewise and in cycle-averaged count
space.

## Level `delta = 1`: reduced odd rotor cone

The exact reduced odd period-3 census rows currently available at

- `d=23`
- `d=25`
- `d=27`
- `d=29`

all lie on affine level `delta=1`.

Concretely:

- every exact period-3 representative has
  `c9=c0+1`, `c1=c8`, `c2=c7`, `c3=c6`, `c4=c5`
- every full three-phase orbit fits `R_delta` with `delta=1`
- every orbit satisfies the phase-sum template
  `[3u,M,M,3x,M,M,3x,M,M,3u+3]`

This does **not** yet prove symbolic completeness of the reduced affine rotor,
but it sharpens the theorem path: the exact census now lands on one affine
level, not just one weighted shell fan.

## Level `delta = 3`: boundary-thread tail

The boundary thread

- `K_p = [0,p,3,3,3,3,3,3,p,3]`

has the verified period-3 tail

- `Z0(r) = [1,r,4,4,4,4,4,4,r,4]`
- `Z1(r) = [1,4,r,4,4,4,4,r,4,4]`
- `Z2(r) = [1,4,4,4,r,r,4,4,4,4]`

with `r = p-4`.

That tail is exactly the affine slice

- `Z_i(r) = Ri_delta(1, r, 4, 4, 4)` with `delta = 3`

and therefore has cycle-sum template

- `[3, r+8, r+8, 12, r+8, r+8, 12, r+8, r+8, 12]`.

So the `K_p` tail is not merely “another period-3 family.” It is a genuine
affine level sitting one asymmetry step above the reduced rotor cone.

## Meaning

This gives a cleaner odd period-3 split:

1. reduced affine level `delta=1`
2. boundary affine level `delta=3`

That is a much better integration than the earlier wording “reduced rotor cone
plus a boundary correction.”

The current theorem path is now:

- prove symbolic completeness of the reduced `delta=1` affine level
- decide whether the boundary thread tail is the whole `delta=3` story on the
  odd side, or only the first exposed slice of a broader boundary affine cone

## Computational support

The script

- `kaprekar_odd_period3_affine_levels.py`

verifies:

- all exact reduced-sector period-3 attractors at `d=23,25,27,29` fit
  `delta=1`, with zero failures
- the boundary tail `Z_r` for `r=5..24` fits `delta=3`, with zero failures
- the corresponding phase-sum templates hold exactly in both cases

with JSON written to

- `kaprekar_odd_period3_affine_levels_2026-05-12.json`.
