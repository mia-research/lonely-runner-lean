# Odd Cycle Global Split (Current Theorem Path)

## Purpose

The odd cycle side now has enough exact structure that it should no longer be
described as a loose collection of special families.

This note records the current global split.

It is not yet a full odd `d=all` cycle theorem, but it is the cleanest
theorem-facing summary of what is actually internal now.

## Split

The currently verified odd cycle story still separates naturally into two
exact sectors:

1. **Reduced sector**: states with high-minus-low total imbalance `= 1`
2. **Boundary thread sector**: the explicit thread
   `K_p = [0,p,3,3,3,3,3,3,p,3]`

The reduced sector contains the previously derived odd staircase / ridge /
rotor grammar. The boundary thread sector is a different mechanism at the
grammar level, but on the period-3 side the two sectors are now linked by one
shared affine normal form:

- reduced sector period-3 lives on affine level `delta=1`
- boundary-thread tail period-3 lives on affine level `delta=3`

where `delta = c9-c0`.

## Sector I — reduced high-minus-low=`1`

### Period 5

The period-5 side is the staircase channel already isolated earlier:

- primitive staircase levels `A,C,F,G`
- decorated companion slice `D,E`
- ridge collapse at level `5`

This side is already structurally internal.

### Period 3

The reduced odd period-3 side has three equivalent descriptions:

1. weighted shell fan over `H`
2. weighted closure count
3. affine rotor cone

The affine rotor law is

- `R0(u,v,w,x,y) = [u,v,w,x,y,y,x,w,v,u+1]`
- `R1(u,v,w,x,y) = [u,y,v,x,w,w,x,v,y,u+1]`
- `R2(u,v,w,x,y) = [u,w,y,x,v,v,x,y,w,u+1]`

with constraints

- `u >= 1`
- `x >= 1`
- `v >= 2`
- `w >= v`
- `y >= v+1`

and exact generator coordinates

- `B = u-1`
- `E = v-2`
- `D = w-v`
- `A = x-1`
- `C = y-v-1`

This is exact on the current reduced odd period-3 census window.

The newer affine-level bridge strengthens the interpretation:

- this reduced cone is the `delta=1` level of the odd affine period-3 normal
  form
- its cycle-sum template is `[3u,M,M,3x,M,M,3x,M,M,3u+3]`

### Period 2

In the reduced sector, the only continuing period-2 line currently seen is `B`.

So the reduced sector already has a reasonably coherent grammar:

- staircase / ridge channel
- reduced affine rotor channel
- one period-2 boundary line `B`

## Sector II — explicit boundary thread `K_p`

The thread

`K_p = [0,p,3,3,3,3,3,3,p,3]`

has exact verified phase behavior:

- `p=1,2`: period `2`
- `p=3`: fixed
- `p=4..7`: period `5` after finite preperiod
- `p=8`: fixed
- `p>=9`: exact period `3` family

The period-3 tail is

- `Z0(r) = [1,r,4,4,4,4,4,4,r,4]`
- `Z1(r) = [1,4,r,4,4,4,4,r,4,4]`
- `Z2(r) = [1,4,4,4,r,r,4,4,4,4]`

with `r = p-4`.

So the old `d=23` / `d=25` knots are now understood as the first nontrivial
boundary phases of a broader thread, not as isolated outliers.

And the period-3 tail is now integrated more tightly than before:

- `Z_i(r) = Ri_delta(1,r,4,4,4)` with `delta=3`
- its cycle-sum template is `[3,r+8,r+8,12,r+8,r+8,12,r+8,r+8,12]`

So the boundary-thread tail is not merely “another period-3 family.” It is
the explicit `delta=3` affine level on the odd side.

## Why this matters

This split is still useful for the eventual paper:

- the reduced sector supports the internal rotor/staircase theorem path
- the boundary thread explains the old knot exceptions
- the boundary period-3 tail shows that not all odd period-3 behavior belongs
  to the reduced affine rotor cone

But it is no longer the whole large-scale odd period-3 picture. A newer direct
scan of the affine-delta normal form shows:

- reduced sector period-3 is affine level `delta=1`
- the `K_p` tail is one explicit entrance line into affine level `delta=3`
- the exact lift `delta -> delta+2` propagates the hierarchy through all
  positive odd `delta`

So the remaining odd global gap is no longer “what are these exceptions?” It
is:

1. prove the reduced affine-rotor symmetry symbolically
2. decide how much of the full odd period-3 universe is exhausted by the
   affine-delta hierarchy

## Honest status

What is now exact:

- the reduced odd period-3 affine rotor fit
- the weighted shell fan count law
- the boundary thread `K_p`
- the `Z_r` period-3 tail
- the affine-level integration `delta=1` / `delta=3`
- the first internal evidence for a broader odd affine hierarchy
- the exact odd affine lift `delta -> delta+2`
- the exact boundary-thread entrance into `delta=3`

What is not yet closed:

- symbolic completeness of the reduced affine rotor
- completeness of the odd boundary-thread side

The newest reduction sharpens the first item further.

If an odd period-3 attractor satisfies

1. phase-sum fixedpoint
2. phasewise asymmetry constancy

then pairwise symmetry is forced by the already closed fixed-point theorem,
because the phase-sum shadow cannot realize the classical `6174` asymmetry
type.

So the live odd period-3 theorem debt is no longer best read as “prove affine
rotor completeness directly.” It is now:

1. prove phase-sum fixedpoint globally
2. prove exact asymmetry-profile collapse
   `A(C)=(delta,0,0,0,0)` globally

and then inherit pairwise symmetry from the fixed-point side.

That is the current theorem path for odd cycles.
