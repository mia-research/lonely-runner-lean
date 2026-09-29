# Carrying group deadlines exactly

Source: `LonelyRunner/LRC/Spec/LapDeadlineN.lean`.
Audit: `experiments/nN/lap_deadline_axioms_v1.lean`.

For each subject disparity d and time t the ledger is computed directly:

```
q = floor(d*t - 1/8)             last opening crossed
R = q + 7/8 - d*t               remaining phase clearance
U = (q + 7/8)/d                 absolute deadline (d > 0)
```

Clearance is EXACTLY R>=0, including equality. Always -1/4<R<=3/4.
While captured around integer K, q=K-1. At that runner's next opening,
q becomes K and R becomes 3/4.

## Forward updates

For an elapsed time h, the number of openings crossed is

```
J = floor(fract(d*t - 1/8) + d*h)
q' = q + J
R' = R + J - d*h
U' = U + J/d
```

These are exact identities, valid also for multi-lap moves. For h>=0 and d>=0,
if d*h<=R, no opening is crossed, the old absolute deadline is retained, and
the runner remains clear. There is no need to choose a new lap label for it.

For a group captured around the SAME integer K>=1, its minimum disparity m
sets its exit T=(K+1/8)/m. Every group member advances exactly one label and
its deadline advances by its own period 1/d. This follows from the proved
same-lap clearance theorem, not from an assumed future grid certificate.

## Two extrema determine the group's clear interval

Let m and D be the minimum and maximum disparities in the group. Once its
common clear lap is K, its entire common clear-time interval is exactly

```
[T,U] = [(K+1/8)/m, (K+7/8)/D].
```

Capture of the extremes around the same positive integer forces T<U. The
window width is

```
U-T = ((3/4)*m - (K+1/8)*(D-m))/(m*D).
```

Thus the close-speed spread D-m quantifies the available time after separation.
All intermediate readings in that group are covered by its two extrema.
For a trajectory restricted to positive times, all disparities are positive;
the more general algebraic lemmas record their precise hypotheses explicitly.

## Remaining task

The update formulas preserve the whole state across lap changes, but they do
not prove that some eventual state has nonnegative slack for every runner.
Absolute deadlines increase on forward moves; remaining clearance need not.
Different groups can repeatedly cross each other's deadlines. Proving eventual
overlap, rather than assuming it as a certificate, remains the global step.

## Verification commands

```
lake build LonelyRunner.LRC.Spec.LapDeadlineN
lake env lean experiments/nN/lap_deadline_axioms_v1.lean
```

The audit covers every source declaration and five exact regression proofs:
deadline equality, the review example's outside-runner deadline crossing,
reset at an exact opening, a two-lap jump still ending in capture, and a
rational group-window width. This is a module-scoped check, not a full Spec gate.
