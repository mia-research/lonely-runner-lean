# Odd Period-3 Affine Hierarchy (Current Internal Picture)

## Purpose

The affine-level bridge showed:

- reduced odd period-3 attractors live on affine level `delta=1`
- the `K_p` boundary-thread tail lives on affine level `delta=3`

This note records the stronger internal fact now visible from the direct
affine-delta scan:

> the odd affine period-3 normal form already contains a hierarchy of higher
> asymmetry levels, and the boundary-thread tail is only the first exposed
> slice of level `delta=3`.

This is not yet a full odd-cycle theorem. But it changes the right global
picture from “reduced cone plus one boundary tail” to “an emerging affine
hierarchy.”

Two further exact closure steps are now in place:

- the lift
  `R_delta(u,v,w,x,y) -> R_{delta+2}(u,v+2,w+2,x+2,y+2)`
- the boundary-thread entrance law
  `K^12(K_p)=Z0(p-4)` for `p>=8`

## The exact affine-delta scan

Inside the exact period-3 normal form

- `R0_delta(u,v,w,x,y) = [u,v,w,x,y,y,x,w,v,u+delta]`
- `R1_delta(u,v,w,x,y) = [u,y,v,x,w,w,x,v,y,u+delta]`
- `R2_delta(u,v,w,x,y) = [u,w,y,x,v,v,x,y,w,u+delta]`

I scanned the exact cycles by dimension.

### Level `delta=1`

The level-`1` count sequence is

- `d=19: 1`
- `d=21: 4`
- `d=23: 10`
- `d=25: 21`
- `d=27: 39`
- `d=29: 66`
- `d=31: 105`
- `d=33: 159`
- `d=35: 231`

This matches the already-known reduced odd period-3 census perfectly.

### Level `delta=3`

The level-`3` count sequence begins at

- `d=37: 1`
- `d=39: 4`
- `d=41: 10`
- `d=43: 21`
- `d=45: 39`
- `d=47: 66`
- `d=49: 105`
- `d=51: 159`
- `d=53: 231`
- `d=55: 325`

So the `delta=3` level is not just the one explicit `K_p` tail.
It is already a full affine level with the same initial shell-count pattern as
the reduced `delta=1` level, shifted upward in dimension.

### Level `delta=5`

The scan already shows the same phenomenon beginning again at

- `d=55: 1`
- `d=57: 4`
- `d=59: 10`
- `d=61: 21`
- `d=63: 39`
- `d=65: 66`

So the affine hierarchy does not stop at `delta=3`.

And the lift note now strengthens this qualitative statement:

- every positive odd `delta` occurs in the affine grammar
- the repeated count pattern across `delta=1,3,5,...` is structural, not
  coincidental

## Role of the boundary thread

The `K_p` tail is still important, but its meaning is now different:

- it is an explicit constructive line inside affine level `delta=3`
- it is **not** the whole `delta=3` level

Concretely, the tail states

- `Z_i(r) = Ri_delta(1,r,4,4,4)`

give one 1-parameter slice of the larger level-`3` affine family.

And the new entrance law sharpens this again:

- for every `p>=8`, `K^12(K_p)=Z0(p-4)`

So the boundary thread is an exact entrance channel into affine level `3`,
not merely a family that eventually happens to land there.

So the old phrase “boundary-thread period-3 tail” remains true, but it is now
too small to describe the whole odd period-3 side at asymmetry level `3`.

## Meaning

The best current odd period-3 grammar is now:

1. a reduced affine level `delta=1`, which is already externally visible in
   the exact reduced-sector census
2. a broader higher asymmetry hierarchy, of which:
   - the boundary-thread tail is one explicit `delta=3` line
   - the direct affine scan already exposes nontrivial `delta=3` and `delta=5`
     levels
   - the lift law propagates all odd affine levels upward

So the earlier “reduced sector versus boundary thread” split was useful, but
it is no longer the best large-scale description of the odd period-3 side.

## Honest status

What is now exact:

- the affine-delta normal form itself
- exact reduced-sector realization at `delta=1`
- exact boundary-thread-tail realization at `delta=3`
- exact direct affine scan counts for `delta=1,3,5`
- exact lift `delta -> delta+2`
- exact boundary-thread entrance into `delta=3`

What is not yet closed:

- whether **every** odd period-3 attractor globally is affine-delta
- which affine-delta levels actually occur in the full odd count-state
  universe without additional sector restrictions
- how the non-period-3 odd sectors interact with the higher affine levels

So this is not yet the finished cycle theorem.
But it is a much stronger and more unified theorem path than “one reduced cone
plus one boundary correction.”

## Computational support

The scan script

- `kaprekar_odd_affine_delta_scan.py`

produces

- `kaprekar_odd_affine_delta_scan_2026-05-12.json`

and the affine-level bridge script

- `kaprekar_odd_period3_affine_levels.py`

produces

- `kaprekar_odd_period3_affine_levels_2026-05-12.json`.

The two follow-up artifacts are:

- `kaprekar_odd_affine_delta_lift.py`
- `kaprekar_boundary_thread_affine_entrance.py`

with outputs

- `kaprekar_odd_affine_delta_lift_2026-05-19.json`
- `kaprekar_boundary_thread_affine_entrance_2026-05-19.json`.
