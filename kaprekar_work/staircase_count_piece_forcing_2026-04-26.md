# Forcing the Staircase Count Pieces from the Odd Automaton

## Purpose

The canonical staircase note and the ridge bridge note left one structural debt:

> derive the raw count-space layer pieces `N_0,...,N_4` from the odd
> borrow/count automaton itself, rather than by reading them off the verified
> family differences `A->C->F->G`.

This note closes that gap at the finite forcing level.

The main result is:

> once the gap-space staircase pieces `M_0,...,M_4` and the odd asymmetry
> alphabet are fixed, each `M_j` has a unique minimal raw count-space lift.

Those unique lifts are exactly the previously observed `N_0,...,N_4`.

## The automaton data we take as primary

Two ingredients are now already internal on the odd period-5 side.

### 1. Gap-space staircase pieces

From the canonical staircase note, the period-5 branch is governed by

- `M_0 = (0,0,0,0,0,0,1,0,0)`
- `M_1 = (0,0,0,0,1,0,0,0,0)`
- `M_2 = (1,0,0,0,0,0,0,0,0)`
- `M_3 = (0,0,0,0,0,1,0,-1,1)`
- `M_4 = (0,0,1,0,0,-1,0,1,0)`

in positive-gap count coordinates `(m_1,...,m_9)`.

### 2. Odd asymmetry alphabet

From the odd kernel template note, every stable odd period-5 staircase phase
has asymmetry vector

`e = (c9-c0, c8-c1, c7-c2, c6-c3, c5-c4)`

in the three-state alphabet

- `u = (1,0,0,0,0)`
- `v = (2,-2,1,0,0)`
- `w = (0,2,-1,0,0)`.

So any valid raw count-space lift must preserve:

1. nonnegativity of counts,
2. total dimension increase `+2`,
3. membership in `{u,v,w}`.

That is the right forcing environment.

## Minimal raw count-space lifts

Call a raw count-space layer a **minimal two-digit lift** if its delta vector

`Δ = (Δ0,...,Δ9)`

satisfies:

- `Δk in {-1,0,1}` for every `k`,
- `sum Δk = 2`.

These are exactly the smallest raw count modifications capable of moving one
staircase level upward.

The probe did the following:

1. fixed the canonical odd staircase gauge used in the earlier notes,
2. collected every occurrence of each gap piece `M_j` on:
   - the main chain `A->C->F->G`,
   - the companion slice `D->E`,
3. repeated that across `m = 0..8`,
4. and for each `j` searched **all** minimal lifts `Δ` for the ones that:
   - realize the gap-space change `M_j`,
   - stay inside the asymmetry alphabet `{u,v,w}`,
   - and work on every relevant source phase.

Each `M_j` occurred `36` times in this forcing set.

## Result

For each `j = 0,...,4`, the valid lift is unique.

The unique forced raw count-space pieces are:

- `N_0 = (0,1,0,0,0,0,0,0,1,0)`      = `+18`
- `N_1 = (0,0,1,0,0,0,0,1,0,0)`      = `+27`
- `N_2 = (0,0,0,0,1,1,0,0,0,0)`      = `+45`
- `N_3 = (1,-1,1,0,0,0,0,0,1,0)`     = `+09 -18 +27`
- `N_4 = (0,1,-1,1,0,0,1,0,-1,1)`    = `+1369 -28`

The forcing probe came back with:

- `forcing_failures = 0`
- candidate count for every `M_j`: exactly `1`

So the raw count-space staircase is now forced, not fitted.

## Interpretation

The first three layers are literal complementary odd-pair insertions:

- `N_0` inserts one `(1,8)` shell,
- `N_1` inserts one `(2,7)` shell,
- `N_2` inserts one `(4,5)` shell.

The last two are the compensating layers that keep the phase in the odd
asymmetry alphabet while realizing the mixed gap-space moves:

- `M_3 = +L79`
- `M_4 = +L3`.

So the staircase pieces divide naturally into:

### Pure odd-shell insertions

- `N_0, N_1, N_2`

### Asymmetry-preserving correction layers

- `N_3, N_4`

This is exactly what one would expect from the odd period-5 channel:

- most of the growth is by adding odd complementary shells,
- but some phases require a compensating redistribution to stay on the same
  automaton.

## Consequence

The period-5 staircase now has both halves of the operator internally pinned:

- gap-space pieces `M_0,...,M_4`,
- raw count-space lifts `N_0,...,N_4`.

And crucially, the second half is no longer “read off the verified families.”
It is forced by:

1. the canonical gap-space staircase,
2. the odd asymmetry alphabet,
3. minimal two-digit raw lifts.

That closes one of the two remaining cycle-side debts from the ridge-bridge
note.
