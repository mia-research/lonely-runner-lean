# Boundary Thread `K_p` on the Odd Cycle Side

## Purpose

The old `d=25` period-2 knot is not isolated.

It sits on an explicit boundary thread

`K_p = [0,p,3,3,3,3,3,3,p,3]`

of dimension

`d = 21 + 2p`.

This note records the exact behavior now verified on that thread.

## Exact low-parameter phase diagram

The first values are:

- `p=0`, `d=21`: enters a fixed point after preperiod `14`
- `p=1`, `d=23`: period `2`
- `p=2`, `d=25`: period `2`
- `p=3`, `d=27`: fixed
- `p=4`, `d=29`: period `5`
- `p=5`, `d=31`: preperiod `3`, then period `5`
- `p=6`, `d=33`: preperiod `6`, then period `5`
- `p=7`, `d=35`: preperiod `9`, then period `5`
- `p=8`, `d=37`: preperiod `12`, then fixed

So the old `d=23` / `d=25` knots are the first two nontrivial points of a
real boundary thread, not two isolated accidents.

## Period-3 tail

From `p=9` onward the thread enters an exact period-3 family.

Writing `r = p-4`, the three phase states are

- `Z0(r) = [1,r,4,4,4,4,4,4,r,4]`
- `Z1(r) = [1,4,r,4,4,4,4,r,4,4]`
- `Z2(r) = [1,4,4,4,r,r,4,4,4,4]`

and exactly

- `K(Z0(r)) = Z1(r)`
- `K(Z1(r)) = Z2(r)`
- `K(Z2(r)) = Z0(r)`

This was verified for `r = 5..24` with zero failures.

So the boundary thread does not stop at the period-2 knots.
It eventually transitions into a second odd period-3 rotor, outside the
reduced high-minus-low=`1` sector.

## Meaning

This changes the interpretation of the old knot note.

What remains true:

- the `d=25` knot is terminal under direct one-shell continuation inside its
  old narrow local grammar,
- it is not the first point of a second continuing **period-2** line.

What is no longer the right global reading:

- “the `d=25` knot is an isolated finite exception.”

The better reading is:

- `d=23` and `d=25` are the period-2 phase of a broader boundary thread `K_p`,
- that thread then passes through fixed and period-5 behavior,
- and from `p>=9` it turns into a second explicit odd period-3 family `Z_r`.

## Relation to the reduced odd rotor cone

The old affine rotor note and weighted shell-fan note describe the exact
odd period-3 grammar on the reduced high-minus-low=`1` sector.

The `K_p` thread lies outside that sector.
So it does not refute the reduced odd rotor cone; it adds a second boundary
period-3 mechanism living on a different high-minus-low level.

That is the correct way to keep both statements true.
