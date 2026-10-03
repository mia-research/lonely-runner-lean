# Finite obstruction mechanism for adding one reading

3 October 2026. Module: `CoreWindowInsertionN.lean`.

## Exact reduction

Work in ordinary time. Suppose all core readings are clear at threshold 1/8
throughout `[L,U]`, with `0 < L <= U`. Insert a positive disparity V (it need
not actually be the fastest).

Either some point of the same window clears V as well, or there is an integer
K with

    K - 1/8 < V*L,     V*U < K + 1/8.

These inequalities say ONE capture zone contains the entire core window.
They are necessary and sufficient for V to block every point of the window.
No intermediate reading or time sample is omitted. If L is captured and the
exit `(K+1/8)/V` is at or before U, that exit is an explicit full-clear witness;
if L is clear, L itself works. Equalities at capture edges are clear, not blocked.

With the core fixed, the obstructing speeds are exactly the open intervals

    (K-1/8)/L < V < (K+1/8)/U.

This is a classification by the original readings and their window endpoints,
not by an assumed final cascade landing.

## A derived finite list, without an imposed speed cap

If `L < U`, complete obstruction forces

    V*(U-L) < 1/4,
    0 <= K < L/(4*(U-L)) + 1/8.

Thus even when V is allowed to range over every positive real number, only
finitely many K can obstruct this fixed window. `finite_obstruction_labels`
proves that all such failures are represented by a finite integer interval.

This directly supports the intended finite-mechanism reduction. Large speed
values are handled uniformly: beyond the bound derived from the window width,
the reading exits its zone before the core loses clearance. Rescaling all
speeds divides L and U by the same factor, leaving `L/(U-L)` unchanged.

In the mapping convention `R=8*t` (nearest disparity 1), write window endpoints
as A,B. The same statements become

    8K-1 < V*A,     V*B < 8K+1,
    V*(B-A) < 2,
    0 <= K < A/(4*(B-A)) + 1/8.

## Scope and next obligation

This is uniform in inserted V but conditional on a supplied core-clear window.
It does not say that one chosen window always survives insertion. Several core
windows can all be swallowed. Nor does it give a uniform lap count as the core
varies: the width ratio may become unbounded near a pinched window.

For several supplied windows, complete failure requires V to belong to every
window's finite union of forbidden speed intervals. Showing that this joint
condition is impossible, or deriving a replacement core window when it is
possible, is the next analytical target. The present module does not claim it.

The older fast-runner lemma already used the sufficient width mechanism with
a lower-order margin. The new contribution here is the exact necessary-and-
sufficient failure classification and its finite label reduction, not a claim
that the width observation itself is new.

## Delegated check

Claude was given a read-only, bounded exact-arithmetic task on the known late
arrangement `(1,73/25,99/25,253/50,321/50,697/100,363/50)`: enumerate all core
windows in R in [1,7] after removing the fastest reading, then record exactly
how that reading blocks each window. No source edits, background runs, extra
agents or global-proof inference were authorised.

### Returned result and independent corrections

Claude returned three windows. Its text incorrectly said their left endpoints
were NOT captured, misassigned width data, and suggested that being the largest
core reading explains the closer in general. Those claims are not accepted.

The independent `core_window_insertion_check_v1.py` intersects closed rational
bands directly (retaining singleton intersections, which a midpoint-only scan
could miss). It verifies the complete list:

| R-window | Fast reading's capture lap | Fast exit minus window end | V times width |
|---|---:|---:|---:|
| [1, 700/697] | 1 | 19850/84337 | 1089/34850 |
| [425/99, 3100/697] | 4 | 750/7667 | 4697/4182 |
| [150/23, 4700/697] | 6 | 1550/253011 | 25773/16031 |

All three left endpoints ARE captured, and each entire window lies strictly
inside that same capture zone. Reading 697/100 sets the right endpoint in all
three windows in this example; no universal fastest-closer rule follows.
The exact check also verifies all seven readings clear at R=9. Between 7 and
9, the minimum disparity 1 is captured, so the windows checked exclude any
earlier landing from R=1 onwards.

This exhibits a real exception that a proof must cover: having several early
six-reading windows is insufficient; the added reading can swallow all of
them. The finite obstruction description makes that exception explicit.
Deleting a reading does not simply delete its recorded cascade moves: deleting
a selected setter changes the next state, and hence other readings' subsequent
phases and capture labels. Their physical motions remain unchanged.

## Verification

Targeted module build and all seven declarations audited, with two regressions:
a genuinely swallowed window and a full capture-width window which cannot be
swallowed because its endpoints are clear. No full Spec gate, commits or pushes.
