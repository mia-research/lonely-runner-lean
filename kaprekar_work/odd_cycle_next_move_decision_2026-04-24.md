# Odd Cycle Next-Move Decision

## Question

After the odd-kernel template probe, there are two plausible next moves:

1. push the odd primitive birth inventory further (`d=21`, `d=23`, ...), or
2. derive the period-5 staircase channel symbolically.

This note records which direction is structurally right **now**.

## Short answer

The correct next move is:

> derive the period-5 staircase channel symbolically.

The birth inventory has already done its job for this branch point.

## Why this is now the right move

The odd-kernel template probe found three exact facts that are too rigid to
treat as coincidence.

### 1. The stable odd period-5 side already obeys one exact staircase law

For the observed stable period-5 primitive kernels

- `A,C,D,E,F,G`

the cycle-sum gap-count vectors are:

- `A`: `(1,5,1,5,1,5,1,5,1)`
- `C`: `(2,5,2,5,2,5,2,5,2)`
- `D`: `(2,5,2,5,2,5,2,5,2)`
- `E`: `(3,5,3,5,3,5,3,5,3)`
- `F`: `(3,5,3,5,3,5,3,5,3)`
- `G`: `(4,5,4,5,4,5,4,5,4)`

So the period-5 branch is already sitting on one exact staircase law

`(r,5,r,5,r,5,r,5,r)`.

That is not weak evidence. It is already the shape of a theorem.

### 2. The birth links use one common phase-layer multiset

After phase alignment, all successful birth links

- `A -> C`
- `C -> F`
- `D -> E`
- `F -> G`

use the same 5-piece increment multiset in gap-count coordinates:

- `L1  = (1,0,0,0,0,0,0,0,0)`
- `L3  = (0,0,1,0,0,-1,0,1,0)`
- `L5  = (0,0,0,0,1,0,0,0,0)`
- `L79 = (0,0,0,0,0,1,0,-1,1)`
- `L7  = (0,0,0,0,0,0,1,0,0)`

This is the decisive structural signal.

It means we are not merely observing “more examples.” We are already seeing a
common growth operator.

Once a common growth operator appears, the right move is to prove the operator,
not to keep collecting examples of it.

### 3. The non-staircase alternatives are already separated

The same probe also showed:

- `H` is a separate period-3 rotor channel,
- `B` is a low-dimensional boundary degeneration.

So the main ambiguity is no longer “maybe there is a third stable period-5
mechanism hiding nearby.” The main ambiguity is how to prove the staircase
channel cleanly.

That changes the research priority.

## Why another birth-inventory pass is lower-value right now

A further birth pass at `d=21`, `d=23`, ... would be useful if the current
evidence were still ambiguous.

But it is no longer ambiguous in the way that matters:

- the period-5 side already has an exact staircase law,
- the birth links already have an exact common increment multiset,
- the period-3 and boundary branches are already separated.

A new birth at `d=21` would mainly do one of two things:

1. land on the same staircase channel, which we already expect;
2. create a genuinely new mechanism, which would be surprising but not the
   most likely reading of the current data.

So another birth pass would mostly be a confirmation pass, not the
highest-value theorem move.

## Practical decision rule

The right order is:

1. **first** derive the period-5 staircase channel symbolically;
2. **then** use the next odd births as an adversarial test of that theorem.

This order is better than the reverse one because:

- if the symbolic derivation works, the later birth pass becomes a clean test
  rather than an open-ended search;
- if the symbolic derivation stalls, *then* the birth pass becomes the right
  next discriminator.

## Immediate next theorem target

The sharp next target is:

> define one canonical period-5 staircase template in phase gap-count space,
> show the common layer multiset above maps staircase level `r` to level `r+1`,
> and explain `A,C,D,E,F,G` as slices or decorations of that template.

That is the correct next move.
