# Forced overlap within retained windows

Source: `LonelyRunner/LRC/Spec/MixedLapOverlapN.lean`.
Audit: `experiments/nN/mixed_lap_overlap_axioms_v1.lean`.
Diagnostic: `experiments/nN/redo/mixed_lap_overlap_v1.py`.

## Analytic progress

Let T be the actual cascade move from time t. Every currently captured runner
has reached its own next opening at T, regardless of its integer lap label.
If its disparity d is at most D, it remains clear throughout

```
[T, t+3/(4D)].
```

For the actual setter b, D<=3b guarantees this interval is nonempty. Thus the
positive-common-lap restriction from the earlier group theorem is no longer
required. Conversely, an old blocker still captured after this move must have
disparity strictly greater than 3b. This does not constrain newly captured
runners in the same way.

Already-clear runners can join the protected group when their stored slack R
satisfies `d*3/(4D)<=R`. These conditions are current-state inequalities, not
an assumption of future loneliness.

One outside runner e must have a clear instant in any retained interval of
length at least 1/(4e). For a protected captured group plus this one outsider,
the resulting isolation is at the first or second actual cascade move.
The disparity budget `D*(b+e)<=3*b*e` is sufficient for the needed time width.

Two outsiders a<=b must share a clear instant in any retained interval of length
at least `1/(4a)+1/(2b)`. Follow the faster exit if necessary, then the slower
exit, then at most one further faster exit. After the slower exit, the faster
repair preserves the slower runner's band. This argument works for arbitrary
positive real disparities and phases, including rational resonance.

`protected_group_overlaps_two` combines this forced overlap with the protected
readings and produces an actual lonely time inside their retained interval.
It does not claim that every configuration satisfies its width budget.

## Exact diagnostic results

Traces start at `1/(8*d_min)`; step indices are zero-based. At every successful
budget the independently constructed witness is checked against all readings.

| Arrangement | Moves to isolation | Steps meeting a sufficient budget |
|---|---:|---|
| late_a | 17 | 16 (no outsiders) |
| late_b | 24 | 22 (one outsider), 23 (none) |
| review: .99,2,3,4,5,6,7 | 6 | none |
| far_outsider: 1,1.2,1.4,1.6,1.8,2,104 | 1 | 0 (none) |

The review arrangement's first lonely time 3/8 is a singleton intersection:
runner 3 is at its opening while runner 5 is at its upper deadline. The new
positive-width sufficient budgets miss it. Earlier exact window theorems keep
these equality cases; they must NOT be discarded from the global proof.

## Still open

No result here proves that every trajectory eventually reaches one of these
width-budget states or an exact pinched overlap. Three or more unprotected
runners, insufficient widths, and switching among such cases remain possible.
These bounds prove overlap for substantive continuous regions, not universal
termination of the seven-reading cascade.

## Verification

```
lake build LonelyRunner.LRC.Spec.MixedLapOverlapN
lake env lean experiments/nN/mixed_lap_overlap_axioms_v1.lean
python3 experiments/nN/redo/mixed_lap_overlap_v1.py
```

The Lean audit covers all 13 source theorems and five exact regression proofs.
This is module-scoped verification, not a full Spec gate.
