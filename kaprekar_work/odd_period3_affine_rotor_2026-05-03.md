# Odd Period-3 Affine Rotor Law

## Purpose

The weighted shell-fan note identifies five odd period-3 shell directions on
top of the primitive rotor kernel `H`:

- `A = +36`
- `B = +09`
- `C = +(45,18,27)` by phase
- `D = +(27,45,18)` by phase
- `E = +(18+27+45)` uniformly, weight `3`

This note rewrites that weighted generator picture as one exact affine rotor
law.

## Exact phase law

Define

- `R0(u,v,w,x,y) = [u, v, w, x, y, y, x, w, v, u+1]`
- `R1(u,v,w,x,y) = [u, y, v, x, w, w, x, v, y, u+1]`
- `R2(u,v,w,x,y) = [u, w, y, x, v, v, x, y, w, u+1]`

Then for all integers satisfying

- `u >= 1`
- `x >= 1`
- `v >= 2`
- `w >= v`
- `y >= v+1`

the Kaprekar map is exactly

- `K(R0) = R1`
- `K(R1) = R2`
- `K(R2) = R0`

So the reduced odd period-3 side is one exact 5-parameter affine rotor family.

## Generator coordinates

Relative to the base rotor

`H = R(1,2,2,1,3)`,

the affine coordinates are uniquely

- `B = u-1`
- `E = v-2`
- `D = w-v`
- `A = x-1`
- `C = y-v-1`

and all five are nonnegative exactly when the phase-law inequalities hold.

So the weighted shell directions are not just one convenient basis.
They are the natural Hilbert-basis increments of this affine cone:

- `A` increments `x`
- `B` increments `u`
- `C` increments `y`
- `D` increments `w`
- `E` increments `(v,w,y)` together

This is the cleanest current explanation of why the odd period-3 side wants
exactly five primitive shell directions.

## Exact fit to the current odd census

Every exact period-3 attractor in the current odd reduced-state census at

- `d=25`
- `d=27`
- `d=29`

fits this affine rotor law with no residue.

So the old weighted-fan count match is now sharpened:

- not only the counts,
- but each individual exact cycle representative

lands on the same affine rotor cone.

## Structural reading

The odd period-3 side can now be read at three equivalent levels:

1. primitive shell directions `A,B,C,D,E`
2. weighted shell closure `W_r`
3. affine rotor cone `R(u,v,w,x,y)`

That is a real compression of the grammar.

## Honest status

What is now exact:

- the affine rotor family itself
- the unique generator-coordinate decomposition
- exact fit of all exact `d=25,27,29` odd period-3 census representatives

What is still not fully closed:

- a purely symbolic proof from the borrow/count automaton that **every**
  odd period-3 attractor in the reduced high-minus-low=`1` sector must satisfy
  the affine rotor symmetry `R(u,v,w,x,y)`

And there is now one explicit caveat outside that scope:

- the boundary thread `K_p` eventually turns into a second odd period-3 family
  on a different high-minus-low level, so this affine rotor note is no longer
  the whole odd period-3 story globally.

But the theorem path is now much narrower: the five-generator question has
become a single affine-symmetry completeness question.
