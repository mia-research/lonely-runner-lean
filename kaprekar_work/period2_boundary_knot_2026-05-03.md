# The `d=25` Period-2 Boundary Knot

## Purpose

The odd reduced-state census at `d=25` has one extra period-2 attractor
beyond the old `B` line:

`[0,2,3,3,3,3,3,3,2,3] <-> [0,2,4,2,3,3,2,4,2,3]`.

This note isolates its natural symmetry class and shows that, in that narrow
class, it is unique and terminal.

Scope note:
the broader story is now recorded separately in
`boundary_thread_k_family_2026-05-12.md`.
The old `d=25` knot is not globally isolated; it is one phase of the explicit
boundary thread `K_p`.

## Natural symmetric ansatz

The knot sits in the obvious boundary-symmetric family

`Q(w,x,y) = [0,2,w,x,y,y,x,w,2,3]`.

Scanning this family over a generous small box gives exactly one nontrivial
period-2 **cycle**. It appears in two parameter presentations,

- `Q(3,3,3)`
- `Q(4,2,3)`

which are just the two phases of the same 2-cycle:

- `Q(3,3,3) = [0,2,3,3,3,3,3,3,2,3]`

with partner

- `K(Q(3,3,3)) = [0,2,4,2,3,3,2,4,2,3]`.

No other `Q(w,x,y)` in the tested box closes to a 2-cycle.

So the extra `d=25` attractor is not the first visible point of a broad
three-parameter period-2 family. Inside its natural symmetric class, it is
unique.

## Terminal under one-shell lifts

To continue from `d=25` to `d=27` inside the shell grammar, the knot would
need a one-shell lift:

- add one complementary shell to its first phase,
- add one complementary shell to its second phase,
- and remain period `2`.

All ordered pairs of one-shell lifts were tested over

- `09`
- `18`
- `27`
- `36`
- `45`

and none preserved period `2`.

So the knot is terminal under the first shell-lift move that would be needed
to create a continuing odd period-2 line.

## Relation to the higher odd census

This matches the exact higher odd reduced-state census:

- `d=25`: two period-2 attractors (`B` plus the knot)
- `d=27`: only `B`
- `d=29`: only `B`

So the extra period-2 branch does not continue on the main odd reduced-state
sector.

## Honest status

What is now exact:

- the knot is unique in its natural symmetric class `Q(w,x,y)`
- the knot has no one-shell period-2 continuation

What remains open:

- a symbolic explanation of *why* this isolated `Q(3,3,3)` point exists
  at all
- whether it has any more remote continuation outside the direct shell-lift
  grammar

At the current theorem level, the right reading is:

the `d=25` period-2 knot is a finite low-dimensional boundary exception, not
evidence of a second continuing odd period-2 family.
