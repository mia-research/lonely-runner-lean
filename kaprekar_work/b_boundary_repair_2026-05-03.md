# The `B` Period-2 Line as a Boundary Repair of `T`

## Purpose

One open question on the odd cycle side was whether the period-2 family `B`
could be absorbed into the same shell grammar, rather than left as a separate
species.

This note gives the cleanest absorption currently available.

## Statement

For every `m >= 0`, let `T_m` be the lifted unstable period-8 seed and `B_m`
the stable period-2 family.

Then exactly:

- `B_0(m) = T_0(m) + 45`
- `B_1(m) = T_5(m) + 36`

where:

- `+45` means add one `(4,5)` shell,
- `+36` means add one `(3,6)` shell.

The probe verified this for `m = 0..20` with:

- failures: `0`

and of course

- `K(B_0(m)) = B_1(m)`
- `K(B_1(m)) = B_0(m)`.

## Interpretation

So `B` is not an unrelated odd period-2 accident.
It sits directly on the boundary of the unstable `T` seed:

- one phase of `T` repaired by a `(4,5)` shell,
- one later phase repaired by a `(3,6)` shell,
- collapsing the unstable 8-cycle into the stable 2-cycle line.

That is a genuine absorption into the shell grammar.

## What this does and does not close

What this closes:

- `B` no longer needs to be treated as a totally separate primitive odd
  mechanism.

What it does **not** close:

- the full period-2 boundary side is still not complete.

The reduced odd census at `d=25` already shows one additional period-2
attractor beyond the old `B` line, so the boundary period-2 sector is still
open.

So the right updated picture is:

- `B` is absorbed as a boundary repair of `T`,
- but the broader odd period-2 boundary grammar is not yet closed.
