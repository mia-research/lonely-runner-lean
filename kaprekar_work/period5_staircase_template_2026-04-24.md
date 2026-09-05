# Canonical Period-5 Staircase Template

## Purpose

The odd-kernel template note showed that the stable odd period-5 side is not a
bag of unrelated kernels:

- `A,C,D,E,F,G`

all obey one exact staircase law on cycle-sum gap counts, and the observed
birth links all use one common layer multiset.

This note sharpens that into a canonical operator statement.

## Canonical phase gauge

There is a phase normalization in which the main staircase chain becomes:

- `S_1 = A` with rotation `0`
- `S_2 = C` with rotation `3`
- `S_3 = F` with rotation `1`
- `S_4 = G` with rotation `1`

Write the phase gap-count vectors as

`S_r = (S_r^(0),...,S_r^(4))`

with each `S_r^(i)` a 9-vector recording multiplicities of positive gaps
`1..9`.

In this gauge:

### `S_1 = A`

- `S_1^(0) = (0,1,1,1,0,0,0,2,0)`
- `S_1^(1) = (0,1,0,1,0,1,1,1,0)`
- `S_1^(2) = (0,1,0,1,1,1,0,1,0)`
- `S_1^(3) = (1,1,0,1,0,1,0,1,0)`
- `S_1^(4) = (0,1,0,1,0,2,0,0,1)`

### `S_2 = C`

- `S_2^(0) = (0,1,1,1,0,0,1,2,0)`
- `S_2^(1) = (0,1,0,1,1,1,1,1,0)`
- `S_2^(2) = (1,1,0,1,1,1,0,1,0)`
- `S_2^(3) = (1,1,0,1,0,2,0,0,1)`
- `S_2^(4) = (0,1,1,1,0,1,0,1,1)`

### `S_3 = F`

- `S_3^(0) = (0,1,1,1,1,0,1,2,0)`
- `S_3^(1) = (1,1,0,1,1,1,1,1,0)`
- `S_3^(2) = (1,1,0,1,1,2,0,0,1)`
- `S_3^(3) = (1,1,1,1,0,1,0,1,1)`
- `S_3^(4) = (0,1,1,1,0,1,1,1,1)`

### `S_4 = G`

- `S_4^(0) = (1,1,1,1,1,0,1,2,0)`
- `S_4^(1) = (1,1,0,1,1,2,1,0,1)`
- `S_4^(2) = (1,1,1,1,1,1,0,1,1)`
- `S_4^(3) = (1,1,1,1,0,1,1,1,1)`
- `S_4^(4) = (0,1,1,1,1,1,1,1,1)`

## Fixed layer operator

Define the five layer pieces:

- `M_0 = (0,0,0,0,0,0,1,0,0)`
- `M_1 = (0,0,0,0,1,0,0,0,0)`
- `M_2 = (1,0,0,0,0,0,0,0,0)`
- `M_3 = (0,0,0,0,0,1,0,-1,1)`
- `M_4 = (0,0,1,0,0,-1,0,1,0)`

Then the main chain satisfies the exact recurrence

`S_(r+1)^(i) = S_r^(i) + M_((i+r-1) mod 5)`

for `r = 1,2,3`.

So the same five layer pieces recur at every level, but the phase assignment
advances by one step each time.

This is the canonical period-5 staircase operator.

## Closed form

The recurrence unrolls to

`S_r^(i) = S_1^(i) + sum_{t=0}^{r-2} M_((i+t) mod 5)`.

This formula reproduces exactly:

- `A` at `r=1`
- `C` at `r=2`
- `F` at `r=3`
- `G` at `r=4`

with zero failures in the probe.

## Why the period-5 birth stream stops

The same closed form predicts the next level:

`S_5^(i) = (1,1,1,1,1,1,1,1,1)`

for **every** phase `i`.

So the staircase channel does not continue producing new primitive period-5
kernels indefinitely. At the fifth layer it collapses onto the all-ones ridge,
where every phase coincides.

This gives a structural explanation for the current birth inventory:

- `r=1` -> `A`
- `r=2` -> `C` / decorated companion at the same staircase height
- `r=3` -> `F` / decorated companion at the same staircase height
- `r=4` -> `G`
- `r=5` -> ridge collapse rather than a new primitive period-5 birth

So the absence of a fresh primitive period-5 kernel at `d=19` is not an
accident of the scan. It is exactly what the canonical staircase operator
predicts.

## Companion slice

The observed companion branch

- `D`
- `E`

is not a different growth mechanism.

In the gauge

- `D` with rotation `0`
- `E` with rotation `2`

the link `D -> E` uses the **same** layer pieces, only with a phase offset:

`E^(i) - D^(i) = M_((i+3) mod 5)`.

So `D,E` are best read as a decorated slice of the same staircase operator,
rather than a second independent period-5 birth mechanism.

## Consequence

The odd period-5 side is now more rigid than the earlier template hypothesis
claimed.

It is not merely “one likely staircase channel.” It already has:

- one canonical phase gauge,
- one fixed 5-piece layer operator,
- one closed-form cumulative expression,
- and one explicit ridge-collapse rule at level `5`.

That is the right normal form for the stable odd period-5 branch.

## What remains open

This does **not** yet prove the whole odd cycle grammar.

It still leaves three tasks:

1. derive the staircase operator symbolically from the borrow/count-space
   automaton rather than from aligned data;
2. explain the companion decoration `D,E` intrinsically rather than just as a
   phase-shifted observed slice;
3. connect the staircase collapse to the separate period-3 rotor channel `H`.

But the period-5 side itself now has a canonical template.
