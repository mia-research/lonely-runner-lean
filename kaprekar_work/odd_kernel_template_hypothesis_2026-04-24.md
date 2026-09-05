# Odd Primitive Kernel Template Hypothesis

## Purpose

The birth inventory showed that odd primitive cycle kernels continue to appear:

- `A_0` at `d=11`
- `B_0,C_0,D_0` at `d=13`
- `E_0,F_0` at `d=15`
- `G_0` at `d=17`
- `H_0` at `d=19`

The sharp question was:

> do these remain an expanding alphabet of unrelated seeds, or do they collapse
> into one or two deeper odd templates?

This note records the current structural answer.

## Coordinate system

For a count vector

`c = [c0,c1,c2,c3,c4,c5,c6,c7,c8,c9]`

write the complementary pairs

- `(0,9)`
- `(1,8)`
- `(2,7)`
- `(3,6)`
- `(4,5)`

and decompose each pair into:

- paired core `p = min(clow, chigh)`
- asymmetry extra `e = chigh - clow`

So every odd kernel phase state is read as:

- a 5-vector of paired-core occupancy,
- plus a small asymmetry 5-vector.

This is the coordinate system where the odd kernels simplify.

## First invariant: total asymmetry is always one high-side digit

For every primitive odd kernel phase checked in `A..H`,

`e09 + e18 + e27 + e36 + e45 = 1`.

So the odd side is not carrying arbitrary imbalance. It is always:

> one extra high-side digit sitting on top of a paired core.

On the observed period-5 branch, the asymmetry alphabet is tiny. Only three
microstates appear:

- `u = (1,0,0,0,0)`
- `v = (2,-2,1,0,0)`
- `w = (0,2,-1,0,0)`

Observed histograms:

- `A,C,F,G`: `u^3 v^1 w^1`
- `D,E`: `u^1 v^2 w^2`

So even before looking at gaps, the odd kernels already collapse to:

- one common paired-core geometry,
- decorated by a very small asymmetry alphabet.

## Second invariant: the period-5 branch obeys one staircase law

For each phase state, let `m_k` be the multiplicity of positive gap `k` in the
half-gap profile.

Summing over a full cycle gives:

- `A`: `[1,5,1,5,1,5,1,5,1]`
- `C`: `[2,5,2,5,2,5,2,5,2]`
- `D`: `[2,5,2,5,2,5,2,5,2]`
- `E`: `[3,5,3,5,3,5,3,5,3]`
- `F`: `[3,5,3,5,3,5,3,5,3]`
- `G`: `[4,5,4,5,4,5,4,5,4]`

So the stable odd period-5 branch is not arbitrary. It satisfies the exact
cycle-sum staircase law

`(r,5,r,5,r,5,r,5,r)`

for `r = 1,2,3,4` on the currently observed kernels.

In words:

> each even gap `2,4,6,8` appears exactly once per phase, while each odd gap
> `1,3,5,7,9` appears `r` times across the period-5 orbit.

This is the main evidence that `A,C,D,E,F,G` belong to one deeper staircase
channel rather than six unrelated families.

## Third invariant: staircase growth uses one fixed layer multiset

After an optimal phase rotation, the successful birth links

- `A -> C`
- `C -> F`
- `D -> E`
- `F -> G`

all use the **same** multiset of five phase increments in gap-count
coordinates `(m1,...,m9)`:

- `L1  = (1,0,0,0,0,0,0,0,0)`
- `L3  = (0,0,1,0,0,-1,0,1,0)`
- `L5  = (0,0,0,0,1,0,0,0,0)`
- `L79 = (0,0,0,0,0,1,0,-1,1)`
- `L7  = (0,0,0,0,0,0,1,0,0)`

These five increments sum to

`(1,0,1,0,1,0,1,0,1)`,

which is exactly “add one new odd layer and keep the even staircase totals
fixed.”

So the period-5 branch has a genuine template mechanism:

> one odd staircase layer is inserted each time, but distributed phasewise by a
> fixed 5-piece increment multiset.

That is much stronger than “the next kernels look similar.”

## Current best split on the odd side

### 1. Period-5 staircase channel

Observed stable kernels:

- main chain: `A, C, F, G`
- companion chain: `D, E`

These all share:

- the same cycle-sum staircase law,
- the same small asymmetry alphabet,
- the same phase-layer increment multiset.

So the current best reading is:

> there is one deeper period-5 odd staircase template, with at least two
> observed phase decorations.

The present labels `A,C,D,E,F,G` are then coordinate slices of that template,
not six unrelated species.

### 2. Period-3 rotor channel

`H` is structurally different.

Its phase gap-count vectors are:

- `[2,1,0,1,1,1,1,1,1]`
- `[1,1,0,1,1,1,2,1,1]`
- `[1,1,0,1,2,1,1,1,1]`

So there is a fixed base support

`[1,1,0,1,1,1,1,1,1]`

with one extra odd gap rotating through:

- `1`
- `7`
- `5`

This is an exact period-3 rotor, not a staircase.

In paired-core coordinates the same thing appears as a rotating surplus across
the triple

- `(1,8)`
- `(2,7)`
- `(4,5)`

with the `(0,9)` and `(3,6)` coordinates fixed.

So `H` is best read as:

> a second odd template, namely a period-3 rotating-triple kernel.

### 3. Boundary degeneration

`B` does **not** satisfy the period-5 staircase law, and it is not period-3.
Its cycle-sum vector is:

`[1,1,3,1,1,2,1,1,1]`.

So the current honest reading is:

> `B` is a low-dimensional boundary degeneration on the odd side, not yet
> absorbed into either deep template.

## Current hypothesis

The growing odd primitive alphabet appears to collapse to:

1. one period-5 staircase channel,
2. one period-3 rotor channel,
3. one boundary degeneration (`B`) at low dimension.

That is already a major reduction relative to the raw inventory
`A,B,C,D,E,F,G,H,...`.

## What is established versus conjectural

### Established by the probe

- the paired-core / asymmetry decomposition above,
- the exact staircase cycle-sum law for `A,C,D,E,F,G`,
- the exact shared layer multiset on the verified birth links,
- the exact rotor form of `H`,
- the exceptional boundary role of `B`.

### Not yet proved

- that every future odd primitive period-5 kernel lies on the same staircase
  channel,
- that every future odd primitive period-3 kernel lies on the same rotor
  channel,
- that `B` is the only boundary degeneration.

So this is a **template hypothesis**, not a theorem note.

## Immediate next target

There are now two clean directions:

1. derive the period-5 staircase channel symbolically from a count-space
   automaton, rather than just by invariant matching;
2. push the birth inventory one step further and test whether the next odd
   primitive births continue to land in:
   - staircase,
   - rotor,
   - or boundary degeneration.
