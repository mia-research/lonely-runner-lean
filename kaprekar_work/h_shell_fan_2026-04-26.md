# The `H` Shell Fan on the Odd Period-3 Side

## Purpose

The reduced odd-state census revealed something important:

- `d=21` did not merely contain the old `H_1` rotor,
- it contained three additional period-3 attractors not listed in the original
  cycle grammar inventory.

At first glance that looks like a new odd mechanism.
This note shows it is not.

The right picture is:

> the odd period-3 side is an `H` shell fan.

That is, `H` is not just one rotor family on the old `+2_36` axis. It already
supports a small transverse shell algebra.

## Four degree-1 shell directions on top of `H`

Write the base period-3 rotor as `H`.

There are four natural shell directions:

- `A = +36` uniformly on every phase
- `B = +09` uniformly on every phase
- `C = +45,+18,+27` across the three phases
- `D = +27,+45,+18` across the three phases

The old inventory only contained `A`, which is the original `H_m` axis.

The new census shows that at shell degree `1` (dimension `d=21`) the full
period-3 sector is:

- `A`
- `B`
- `C`
- `D`

with no extra period-3 attractors beyond those four.

So the `d=21` “new kernels” are not a new mechanism. They are exactly the
three missing degree-1 shell directions `B,C,D`.

## Degree-2 closure at `d=23`

The next test is the degree-2 shell layer.

If the `H` side is really governed by these four directions, then at shell
degree `2` we should see exactly the commutative degree-2 closure:

`AA, AB, AC, AD, BB, BC, BD, CC, CD, DD`

That is `10` period-3 families.

The reduced census at `d=23` came back with exactly:

- period-3 attractors: `10`

and every one of them matches one of those degree-2 shell combinations.

So `d=23` is not spawning a new odd period-3 mechanism either.
It is exactly the degree-2 `H` shell fan.

## Degree-3 closure at `d=25`

At shell degree `3`, the naive four-direction commutative closure predicts

`binom(4+3-1,3) = 20`

period-3 families.

The reduced census at `d=25` finds:

- period-3 attractors: `21`

The shell-fan construction reproduces `20` of those `21` exactly, with no
extras. So at `d=25` the four-direction shell fan remains the dominant
structure, but it is no longer complete.

There is one residual period-3 attractor with cycle representative

`(1,3,3,1,4,4,1,3,3,2)`.

So the right statement is:

> the `H` shell fan explains the entire period-3 sector at `d=21` and `d=23`,
> and all but one period-3 family at `d=25`.

That is already a strong structural compression.

## Interpretation

This sharpens the cycle grammar in an important way.

Previously the odd side looked like:

- staircase channel,
- one rotor channel `H`,
- one boundary degeneration `B`.

Now the rotor channel itself has internal grammar:

- one axial shell direction `A`
- three transverse degree-1 shell directions `B,C,D`
- commutative closure through degree `2`
- near-complete closure at degree `3`

So the odd period-3 side is not just “`H_m` for `m>=0`.”
It is already a genuine shell fan.

## Consequence for the unified cycle program

This is good news for the theorem path.

It means the `d=21` and `d=23` odd births do **not** force a third odd
mechanism. They stay inside the rotor channel.

The honest remaining gap is now sharper:

- complete the `H` shell fan beyond degree `2`,
- understand the single residual period-3 family already visible at `d=25`,
- and do the analogous compression for the boundary period-2 side.

That is a much better place to be than “odd births keep appearing ad hoc.”
