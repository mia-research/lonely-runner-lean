# CT.1 Numerical Direction

Date: 2026-04-12
Status: targeted computational guidance for analytic closure

## 1. What computation was actually useful

Yes: targeted numerical experiments are worth doing here.

But the useful computation is **not** a blind search for more safe fibres. The useful computation is:

- identify the exact post-transfer repair modes that could break the prime route;
- test those modes under the corrected grouped floor-reset dynamics;
- and check whether the theorem should be stated for **every** initial thin residue or only for the **existence of a well-chosen** initial thin residue.

That last point turned out to be the important one.

## 2. Tooling

New probe script:

- [ct1_prime_routeA_probe.py](/Users/trentpalelei/Desktop/Math%20Ex/tools/ct1_prime_routeA_probe.py)

This script analyzes prime dropped-unit cases under grouped floor-reset events and inspects the post-transfer interval for:

- coincident reset events,
- companion-residue re-add events,
- and the effect of the **choice of starting thin residue**.

## 3. First correction: the naive route-A statement is too strong

The earlier route-A wording was roughly:

> after transfer, no other runner can repair the companion residue in the critical interval.

That is too strong.

A random prime example at `n=11` shows why:

- `E = (13,18,60,66,68,73,86,87,109,124)`,
- a depth-1 chain occurs,
- the companion residue is re-added by runner `87`,
- but a safe fibre still appears at that same event because a **different** residue becomes uncovered.

So “the companion is never re-added” is not the right universal theorem target.

## 4. Main new discovery: the starting thin residue matters

The correct computational question is:

> given a fully covered base fibre, is there **some** multiplicity-1 residue at `b_0` whose chain is especially simple?

This appears to be the right direction.

### Exhaustive small-prime results

For fully covered prime dropped-unit tuples:

- `n=5`, speeds `<= 15`:
  - `147/147` cases have **some** thin residue with depth `0`,
  - `132/147` cases have **every** thin residue of depth `0`.

- `n=7`, speeds `<= 14`:
  - `416/420` cases have **some** thin residue with depth `0`,
  - `341/420` cases have **every** thin residue of depth `0`.

So the genuinely hard prime full-cover cases at `n=7` are only `4` tuples.

Those four are:

- `(2,6,7,8,9,10)`
- `(2,6,7,8,10,11)`
- `(2,6,8,9,10,14)`
- `(2,6,8,10,11,14)`

They collapse to two structural prototypes after ignoring divisible-speed decoration.

### Random larger-prime support

Random admissible prime samples also support the same pattern:

- `n=11`, max speed `132`, `40` full-cover samples: `40/40` had **some** good starting thin residue.
- `n=13`, max speed `156`, `13` full-cover samples: `13/13` had **some** good starting thin residue.
- `n=17`, max speed `204`, `4` full-cover samples: `4/4` had **some** good starting thin residue.

This is not a proof, but it is a very strong directional signal.

## 5. Better theorem target

The strongest computationally supported replacement for the old universal `CT.1` wording is:

> **CT.1-E (existential thin-start version, candidate).**
> In the prime dropped-unit branch, if the base fibre `b_0=L/n` is fully covered, then there exists a multiplicity-1 residue `r^*` at `b_0` such that either:
> 1. its sole-cover runner exposes a safe fibre directly at depth `0`, or
> 2. after one transfer, the resulting chain reaches a safe fibre before any genuine sustaining repair chain can form.

An even sharper computationally supported version for the tested ranges is:

> there exists a multiplicity-1 residue whose chain is depth `0` or depth `1` with no companion re-add before the first safe fibre.

That is much cleaner than asking for **every** thin residue to work.

## 6. Why this matters analytically

This changes the proof search in an important way.

We no longer need to prove:

- “any thin residue works,” or
- “every companion residue is protected from every possible repair.”

Instead, we can try to prove:

- there is always a **good choice** of initial thin residue,
- and for that chosen residue the post-transfer interval is arithmetically simple enough to close.

That is a much narrower and more believable theorem.

## 7. Recommended next analytic move

The next proof attempt should be:

1. define a selection rule for the initial thin residue at `b_0`,
2. prove that the selected residue has a privileged post-transfer geometry,
3. close the remaining `4` exhaustive `n=7` hard cases as the prototype family.

The computational evidence now strongly suggests that the right theorem is an
**existential selection theorem**, not a uniform chain theorem over all thin residues.
