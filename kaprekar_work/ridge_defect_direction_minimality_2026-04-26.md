# Minimal Ridge Defect Directions for the `H` Rotor

## Purpose

The period-5 / `H` bridge note identified the period-3 family `H` as a ridge
defect:

> remove one `(3,6)` shell from the fixed staircase ridge and reinsert it into
> one of `(1,8)`, `(2,7)`, `(4,5)`.

What was still missing was the minimality statement:

> why exactly those three directions, and not more primitive defect rotors?

This note closes that at the one-shell level.

## Ridge and shell-transfer model

The odd staircase closes at the fixed ridge

`R = (1,2,2,2,2,2,2,2,2,2)`.

Write the complementary shell pairs as:

- `09`
- `18`
- `27`
- `36`
- `45`

A **minimal ridge defect direction** is an ordered shell transfer

`P_src -> P_dst`

meaning:

1. remove one shell from pair `P_src`,
2. add one shell to pair `P_dst`.

There are `5 * 4 = 20` such ordered transfers.

The probe enumerated all twenty and classified the resulting orbit under `K`.

## Result

Among all `20` one-shell transfer defects:

- exactly `3` are primitive `H` rotors,
- exactly `3` are non-primitive captures into `H`,
- the other `14` fall into period `1` or period `5`, not new primitive
  defect rotors.

### Primitive `H` directions

These are the only three directions with `mu = 0` and period `3` on the
`H` cycle itself:

- `36 -> 18`
- `36 -> 27`
- `36 -> 45`

These are exactly the three directions already described informally in the
bridge note.

### Non-primitive captures into `H`

Three other transfers eventually enter the same `H` rotor, but only after a
positive transient:

- `18 -> 09`
- `27 -> 09`
- `45 -> 09`

So these are not primitive defect rotors. They are one-shell defects that
flow into the primitive `H` rotor.

### Everything else

All remaining one-shell defect directions fall into:

- period `1` behavior, or
- period `5` behavior,

with no additional primitive rotor.

The exact global count on the `20` directions is:

- primitive `H`: `3`
- `H` captures: `3`
- period `1`: `7`
- period `5`: `7`

## The primitive defect theorem at this scale

At the minimal one-shell level, the ridge therefore admits exactly the three
primitive rotor directions

- `(3,6) -> (1,8)`
- `(3,6) -> (2,7)`
- `(3,6) -> (4,5)`

and no others.

That is the precise minimality statement we needed.

## Interpretation

This sharpens the bridge note substantially.

The statement is no longer just:

> `H` can be written as ridge plus one defect.

It is now:

> among all minimal one-shell transfers away from the ridge, the only
> primitive rotor directions are exactly the three odd transfers out of
> `(3,6)`.

So the `H` rotor is not just nearby in count space. It is the unique primitive
one-shell odd rotor adjacent to the staircase ridge.

That is why the bridge picture is now so tight:

- staircase branch -> fixed ridge
- ridge + one primitive odd defect -> `H`

with the primitive defect directions completely exhausted at the one-shell
level.

## Consequence for the cycle-side theorem path

The two open debts from the bridge note are now both closed at the structural
level we wanted:

1. staircase count pieces `N_0,...,N_4` are forced by the automaton,
2. the ridge admits exactly three primitive one-shell rotor directions.

That moves the odd cycle side from “strong synthesis” to something much closer
to a theorem path:

- canonical staircase operator,
- fixed ridge closure,
- unique minimal rotor adjacency.
