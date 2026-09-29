# Forward transport using speed ratios and retained band deadlines

Source: `LonelyRunner/LRC/Spec/PinchTransportN.lean`.
Audit: `experiments/nN/pinch_transport_axioms_v1.lean`.

For a captured disparity b on integer lap K at time t, write

```
T = (K + 1/8)/b
eta = K + 1/8 - b*t
```

Then `0 < eta < 1/4`, `T-t = eta/b`, and every other reading moves by
`d*(T-t) = (d/b)*eta`. This is the existing exact phase-transport identity,
now used to derive clearance rather than assume it.

## Derived clearance results

1. If an old setter a is at `a*t=P+1/8` and `a<=3*b`, it remains strictly
   inside its original clear band after b's exit. In particular, a handoff
   to a faster disparity cannot immediately recapture the previous setter.
   This says nothing by itself about earlier setters several moves back.
2. If several positive disparities are all captured around the SAME integer
   K>=1, their ratios are constrained. The exit of the smallest disparity
   clears every member of that group. There is no restriction to two members.
3. If that group is the entire difference set, its exit is the actual cascade
   move and is lonely. The minimum disparity is selected from the finite set.
4. If there are outside readings, their already-calculated clear bands can be
   reused. For a reading d originally in lap M, retaining that band at T is
   equivalent to the single inequality

   `d*(K+1/8) <= b*(M+7/8)`.

   The lower bound persists because time advances and d is nonnegative.
   `group_exit_lonely_of_deadlines` combines the automatically cleared group
   with these outside deadlines and identifies the result as the actual
   cascade move.
5. If a>b are captured around the same integer K at time t, then
   `t < 1/(4*(a-b))`. The speed discrepancy forces separation in this precise
   unwrapped-lap sense.

## Essential limits

- SAME integer K is stronger than sharing a circular residue or grid class.
  Different lap labels still allow recurring captures of distinct speeds.
- K=0 does not force the group's ratios to be close; the positive-lap
  hypothesis cannot be dropped.
- The outside deadlines are explicit hypotheses, not consequences of having
  once calculated or once cleared those runners. If one is exceeded, its
  reading may enter a new capture and must be transported again.
- The next unresolved global step is controlling those successive deadline
  crossings across changing lap groups. No general termination is asserted.

## Verification

```
lake build LonelyRunner.LRC.Spec.PinchTransportN
lake env lean experiments/nN/pinch_transport_axioms_v1.lean
```

Both passed. All 11 source theorems and four regression proofs use only
`propext`, `Classical.choice`, and `Quot.sound`. The regressions cover an
outside deadline met exactly, failure of the lap-zero generalization, the
review example's outside blocker at 9/56, and coinciding circular residues
for distinct disparities on different integer laps. No full-tree gate is
claimed by these module-scoped checks.
