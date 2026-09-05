# Weighted Shell Fan on the Odd Period-3 Rotor Side

## Purpose

The reduced odd period-3 side already had:

- the axial rotor line `H_m`,
- the four degree-1 shell directions
  - `A = +36`,
  - `B = +09`,
  - `C = +(45,18,27)` by phase,
  - `D = +(27,45,18)` by phase,
- and the exact residual family `J_m`.

The `J` note identified

`J_m - H_m = E = +(18+27+45)`

uniformly across phases.

The key question is whether this should be read as yet another ad hoc family,
or as the first higher-weight generator in a single rotor grammar.

## Weighted fan law

Let

- `wt(A)=wt(B)=wt(C)=wt(D)=1`,
- `wt(E)=3`.

Then define `W_r` to be the set of period-3 cycles obtained from the base
rotor `H` by all multisets of generators with total weight `r`.

Since each weight unit raises dimension by `2`, `W_r` lives at

`d = 19 + 2r`.

## Exact low-weight closure

The weighted closure reproduces the exact reduced-state period-3 counts at the
first five odd rotor levels now available exactly:

- `r=1`, `d=21`: `|W_1| = 4`
- `r=2`, `d=23`: `|W_2| = 10`
- `r=3`, `d=25`: `|W_3| = 21`
- `r=4`, `d=27`: `|W_4| = 39`
- `r=5`, `d=29`: `|W_5| = 66`

These are precisely the already-established exact census counts.

So the old `d=25` residual is not “the first failure of the shell fan.”
It is exactly the first place where the weight-3 generator `E` becomes
dimensionally available.

## Count formula

Because the weighted rotor fan has four generators of weight `1` and one
generator of weight `3`, the closure size is

`N_3(r) = sum_{e=0}^{floor(r/3)} C(r-3e+3, 3)`.

The first values are:

- `N_3(1)=4`
- `N_3(2)=10`
- `N_3(3)=21`
- `N_3(4)=39`
- `N_3(5)=66`
- `N_3(6)=105`
- `N_3(7)=159`

## Higher-dimensional evidence

Beyond that exact window, the weighted closure keeps matching the observed odd
period-3 sector under random attractor sampling:

- `d=31`, `r=6`: sampled period-3 count `105`, misses `0`
- `d=33`, `r=7`: sampled period-3 count `159`, misses `0`

The period-2 side is also sharper now.

In the exact odd census:

- `d=25` has two period-2 attractors:
  - the old `B` representative `[0,1,1,8,2,2,9,0,0,2]`
  - one extra boundary knot `[0,2,3,3,3,3,3,3,2,3]`
- `d=27` has only the old `B` line
- `d=29` has only the old `B` line

And in the higher-dimensional samples, the odd period-2 side still shows only
the old `B` line:

- `d=31`: period-2 representative `[0,1,1,11,2,2,12,0,0,2]`
- `d=33`: period-2 representative `[0,1,1,12,2,2,13,0,0,2]`

So the extra period-2 attractor at `d=25` currently reads as a low-dimensional
boundary knot, not as evidence of a continuing second period-2 line.

## Structural meaning

This compresses the reduced odd rotor side substantially:

- `H` is the primitive rotor kernel,
- `A,B,C,D` are the primitive weight-1 shell exits,
- `E` is the first primitive higher-weight shell exit,
- `J` is simply the first exposed `E`-direction,
- and the observed odd period-3 birth stream is the weighted closure of these
  generators.

That is much closer to a theorem-grade cycle grammar than the earlier picture
of one axial line plus a handful of ad hoc residual families.

## Honest status

What is now exact:

- the weighted closure reproduces the exact period-3 census at `d=21,23,25`
- `J` is exactly the weight-3 generator `E`

What is still not symbolically closed:

- a proof from the borrow/count automaton that **only** these five weighted
  generators occur on the reduced high-minus-low=`1` odd period-3 side.

And there is now an explicit scope caveat:

- the boundary thread `K_p` produces another odd period-3 family from `p>=9`
  on a different high-minus-low level,
- so this weighted shell fan is the theorem path for the reduced odd period-3
  sector, not the whole odd period-3 universe globally.

So this note promotes the reduced odd period-3 side from “family list” to
“weighted shell grammar with exact low-weight closure and strong high-weight
support,” but it does not yet claim full cycle completeness.
