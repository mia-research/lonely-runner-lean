# Dead-Zone Cycle Automata
## Reframing the `d=5` / `d=7` void as pure-cycle borrow dynamics — 2026-04-24

---

## Purpose

The fixed-point story is now closed, so the natural next question is the cycle
side, especially the base-10 dead zones:

- `d=5`
- `d=7`

These dimensions are interesting because they do **not** merely lack fixed
points. They still have highly organized Kaprekar dynamics.

This note packages the dead-zone proof into a better dynamical statement:

> `d=5` and `d=7` are pure-cycle dimensions for the borrow automaton.

That is a stronger and more useful description of the void than “no constants”.

---

## Setup

From the dead-zone parameter proof:

### `d=5`

For sorted digits

`a >= b >= c >= d >= e`

define the shell-difference state

`(A,B) = (a-e, b-d)`.

Then `K(n)` depends only on `(A,B)`, so the dynamics reduce to a finite-state
map

`F5(A,B)`.

The admissible state space has size:

- `54`.

### `d=7`

For sorted digits

`a >= b >= c >= d >= e >= f >= g`

define

`(A,B,C) = (a-g, b-f, c-e)`.

Again `K(n)` depends only on `(A,B,C)`, so the dynamics reduce to a finite-state
map

`F7(A,B,C)`.

The admissible state space has size:

- `219`.

So in both dead zones the full Kaprekar dynamics collapse to a finite borrow
automaton on symmetric shell differences.

---

## New result: full attractor structure

Runner:

- `scripts/kaprekar_dead_zone_cycle_automata.py`

Machine output:

- `analysis/base10/dead_zone_cycle_automata_2026-04-24.json`

The runner computes the exact transition graph, attractor cycles, basin sizes,
and transient-depth histograms for the two parameter automata.

### `d=5`

State count:

- `54`

Attractor cycles:

- one 2-cycle with basin size `3`
- two 4-cycles with basin sizes `21` and `30`

So the full state space splits as:

`54 = 3 + 21 + 30`.

Max transient depth:

- `5`

So every admissible `d=5` shell state enters one of the three attractor cycles
within at most five parameter steps.

### `d=7`

State count:

- `219`

Attractor cycles:

- exactly one 8-cycle

Basin size:

- `219`

Max transient depth:

- `12`

So the entire admissible `d=7` shell simplex collapses onto one universal
period-8 attractor.

This is the strongest new point in the note:

> the `d=7` void is not a fragmented cycle landscape. It is a one-attractor
> borrow automaton.

---

## Explicit attractors

### `d=5` parameter attractors

2-cycle:

`(5,4) <-> (6,0)`

4-cycles:

`(7,5) -> (6,3) -> (7,2) -> (8,4) -> back`

`(6,4) -> (6,2) -> (8,3) -> (7,6) -> back`

### `d=7` parameter attractor

8-cycle:

`(8,4,3) -> (7,6,2) -> (8,4,4) -> (7,5,1) -> (9,5,3) -> (8,7,2) -> (8,6,5) -> (7,5,2) -> back`

These are exactly the attractors found in the earlier dead-zone proof, now
upgraded with the basin decomposition.

---

## Borrow-shell reading

The right way to read the dead zones now is:

1. the fixed-point equation fails because the parameter automaton has no fixed
   state,
2. but the automaton is finite, so recurrence is forced,
3. and the recurrence is highly rigid rather than chaotic.

So the void is not “nothing happens”.
It is:

> pivot closure fails, and the borrow state recirculates.

That is why the dead-zone dimensions feel so important in the story:

- they show the same borrow-shell machinery still runs,
- but instead of closing into a constant, it closes only at the automaton level
  as a cycle.

This is exactly the phenomenon the fixed-point theory had to exclude, and now
it becomes the starting point of the cycle theory.

---

## Why `d=5` and `d=7` already look different

The two dead zones are not dynamically identical.

### `d=5`

- small automaton
- three attractors
- one tiny special basin of size `3`
- two larger competing basins

This looks like a low-dimensional cycle phase with multiple competing closures.

### `d=7`

- larger automaton
- but only one attractor
- every admissible state flows to the same period-8 orbit

This looks like a much more rigid cycle phase: once fixed points disappear, the
whole shell-difference state space is captured by one cycle law.

That contrast is already mathematically interesting and probably matters for
the broader cycle program.

---

## Relation to the broader cycle story

This note does not classify all base-10 cycles.

What it does do is sharpen the cycle-side agenda:

1. low-dimensional cycle mechanisms are exact borrow automata
   - 2-digit gap cycle
   - 5-digit dead-zone automaton
   - 7-digit dead-zone automaton
2. extension-period phenomena already appear elsewhere
   - the `975` period-3 family at `d=12,16,22`

So the natural next cycle question is no longer vague.
It is:

> can the known cycle families also be organized as exact borrow-state
> automata plus shell-extension rules, the way the fixed points were?

That is the clean next research path.

---

## Main consequence

For the project story, the dead zones should now be phrased as:

> `d=5` and `d=7` are pure-cycle dimensions of the base-10 borrow automaton.

That is better than “dimensions with no constants,” because it explains why
they still matter structurally:

- they are the first places where the borrow grammar closes dynamically but not
  statically.
