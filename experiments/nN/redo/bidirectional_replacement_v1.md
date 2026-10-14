# Two-sided failure and the forced successor

Checkpoint recovered 2026-10-03 after usage-limit interruption.

## Uniform symbolic results

At a lone-blocker event, let b>0 be its disparity, z its signed capture
phase in (-1/8,1/8), and let d>0, g in [1/8,7/8] describe another reading.

- Forward displacement: (1/8-z)/b. Its CURRENT band survives iff
  d(1/8-z) <= b(7/8-g).
- Backward displacement: (z+1/8)/b. Its CURRENT band survives iff
  d(z+1/8) <= b(g-1/8).
- If the same reading violates both inequalities, d>3b. If disparities
  are all <=3b, opposite failures must have different guards.

These tests concern retention of the current band, not all possible later
or earlier bands. A reading can fail a retention test yet be clear at the
proposed endpoint after changing its lap label.

If the lower guard's opening lies after the blocker's backward edge and the
upper guard's closing lies before its forward edge, retaining both guard
labels traps every candidate time inside the capture slot. Any clear candidate
beyond the forward edge must increase the upper guard's label; any candidate
before the backward edge must decrease the lower guard's label. These necessary
label changes are proved in Lean. They do not assert that the first replacement
label will always succeed.

## Exact two-sided failure

The seven subject disparities, numbered 1 through 7 here, are

    (89/8, 127/8, 79/32, 2119/128, 399/64, 87/64, 153/64).

At t=1 all seven are clear, with readings 1 and 2 on opposite boundaries.
At 2t there are two blockers; at 3t and 5t there is one blocker each.
Both immediate directions fail at each eligible lone-blocker event:

| Event | Blocker | Backward edge | Still captured | Forward edge | Still captured |
|---|---|---|---|---|---|
| 3 | 6 | 248/87 | 3 | 88/29 | 5 |
| 5 | 7 | 760/153 | 5 | 776/153 | 4, 6 |

This is an actual modulo-clearance failure, not merely failure of current-band
retention. The exact claims have Lean regression proofs.

## The forced repair at event 3

Reading 6 leaves at 88/29, carrying exactly reading 5 into capture on lap 19.
Reading 5's next opening is therefore

    (19+1/8)/(399/64) = 408/133.

All seven readings are clear there with labels

    (34,48,7,50,19,4,7).

This is not only a single example. Fix reading 5 at 399/64, and let each of
the other six disparities vary independently by at most 1/10000 from the
displayed centre. Lean proves throughout this continuous six-dimensional box:

1. At event 3, exactly reading 6 is in its capture slot; all others have
   explicit clear bands.
2. At reading 6's forward opening (33/8)/d_6, exactly reading 5 is in its
   capture slot; the other six have explicit clear bands.
3. At reading 5's next opening 408/133, all seven are clear.

This family is local, not the whole arrangement space. Its generic members
need not retain the original pinch at t=1. The two-sided-failure regression
is for the centre; the family theorems establish the forward replacement chain.

An important detail: reading 1 is clear at both forward endpoints but is
captured at 272/89 between them. Its label increases from 33 to 34. The proof
allows this return and checks the new label; it does not incorrectly require
that every formerly clear runner stay clear throughout the jump.

## Consequence and remaining obligation

There is a proved local replacement mechanism beyond failure of both immediate
directions: use the actual captured reading's forced next opening, and update
the other labels, including readings which completed a capture between endpoints.

The uniform margin/guard theorems supply necessary changes. The box supplies
a nontrivial infinite family in which that successor is successful. Neither
proves that successors cover every arrangement or an entire arbitrary AP
deformation. The next analysis must control the remaining labels for arbitrary
guards, not assume the six old bands are retained.

## Files and verification

- Lean: `LonelyRunner/LRC/Spec/BidirectionalReplacementN.lean`.
- Audit and exact regressions: `experiments/nN/bidirectional_replacement_axioms_v1.lean`.
- Exact diagnostic: `experiments/nN/redo/bidirectional_replacement_v1.py`.
- Targeted build passed; all 17 audited declarations use only standard Lean axioms.
- All 64 box-corner regression tests pass; the Lean proof covers the whole box,
  not merely its corners.
- Full Spec gate not run. These files are saved locally, uncommitted; no push.
