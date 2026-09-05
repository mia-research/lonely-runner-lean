# Odd Affine-Delta Lift

## Purpose

The affine hierarchy note showed that odd period-3 levels

- `delta=1`
- `delta=3`
- `delta=5`

all occur.

This note records the exact lift mechanism connecting them.

## Lift law

Inside the odd affine period-3 normal form

- `R0_delta(u,v,w,x,y) = [u,v,w,x,y,y,x,w,v,u+delta]`
- `R1_delta(u,v,w,x,y) = [u,y,v,x,w,w,x,v,y,u+delta]`
- `R2_delta(u,v,w,x,y) = [u,w,y,x,v,v,x,y,w,u+delta]`

define

- `L_delta : (u,v,w,x,y) -> (u, v+2, w+2, x+2, y+2)`

so that

- `L_delta(R_delta(u,v,w,x,y)) = R_{delta+2}(u,v+2,w+2,x+2,y+2)`.

Then the exact verified statement is:

> if `R_delta(u,v,w,x,y)` is a genuine period-3 cycle, so is
> `R_{delta+2}(u,v+2,w+2,x+2,y+2)`.

This lift raises dimension by `18`.

## Inverse lowering

The lift is reversible on every affine cycle with

- `v>=2`
- `w>=2`
- `x>=2`
- `y>=2`

by subtracting `2` from `v,w,x,y` and lowering `delta` by `2`.

So in the currently scanned windows, affine levels `1,3,5` are not just three
observed layers. They are linked by an exact shell operator.

## Consequences

### 1. All odd affine levels occur

The base seed at level `delta` is

- `(u,v,w,x,y) = (1, delta+1, delta+1, delta, delta+2)`

which has dimension

- `d = 9*delta + 10`.

Since level `delta=1` exists and the lift is exact, this gives an infinite
odd hierarchy:

- `delta = 1,3,5,7,...`

all occur inside the odd period-3 affine grammar.

### 2. The level count patterns are shifts, not coincidences

The count tables for `delta=1`, `delta=3`, and `delta=5` are not merely
similar. They are the same affine family translated upward by repeated
application of `L_delta`.

So the repeated count pattern

- `1,4,10,21,39,66,105,...`

at successive higher odd `delta` levels is explained structurally.

## Meaning

This is the first exact result that answers part of the “which `delta` levels
occur?” question:

- every positive odd `delta` occurs in the affine grammar

What it does **not** yet prove is the stronger global statement:

- that every odd period-3 attractor in the full odd count-state universe is
  affine-`delta`.

But it turns the current hierarchy from an empirical pattern into a genuine
grammar operator.

## Computational support

The script

- `kaprekar_odd_affine_delta_lift.py`

verifies:

- `delta=1 -> 3` on all exact affine cycles through `d<=35`
- `delta=3 -> 5` on all exact affine cycles through `d<=55`
- the inverse lowering `3 -> 1` and `5 -> 3` on the same windows

with zero failures, and writes

- `kaprekar_odd_affine_delta_lift_2026-05-19.json`.
