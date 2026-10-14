# Exact handoff-boundary perturbations

## What was tested

35 one-parameter paths through five seven-reading configurations: two existing late
examples, the manuscript's 28-move example, the doubled AP `(1,2,3,4,5,6,8)`, and
`(1,8,16,25,33,41,100)`. Each of the six nonminimal speeds was perturbed individually
by a rational parameter in `[-1/50,1/50]`; a seventh path perturbed them together in
alternating directions. The nearest reading was normalized to one.

This is a study of these paths, **not a covering of all arrangements**.

The tracer uses exact rational arithmetic. At an opening `t=A/(8*v_s)`, grid walls
are `A*v_i-q*v_s=0`; comparing two potential exits gives another homogeneous
linear wall. Since the speeds are affine in the parameter, the wall locations
are exact rationals. Intersecting their sign constraints gives an open interval
with the same complete trace. Boundary points are traced separately: equality
at distance `1/8` is clear, not blocked.

## Results

- 241 open trace cells; 276 boundary evaluations (counted per path).
- All cells terminate and all boundary evaluations are clear eventually.
- No step caps, cell caps, or unresolved parameter intervals.
- Maximum 28 moves and four simultaneous blockers.
- 486 repeated ordered-pair events in the representative cell traces.
- Capture depth increased in 350 events and decreased in 136. It is not a
  universally decreasing quantity. These are observation counts, not frequencies
  over the space of configurations.
- 30 boundary evaluations have a zero-width first common clear window.

The cell partition is checked for gaps. Each cell is replayed independently at
two further interior points. The extraction algorithm is not Lean-certified;
the capture-wall algebra and drift results below are.

## A boundary that removes 26 moves

Start with `(1,2.3509,3.2412,4.1886,5.2223,5.7871,7.4378+z)`.
Let `a=7.4378+z` and `b=5.7871`. At

`z = 193/70000`, equivalently `7*a=9*b`,

the first exit has `a*t=9/8` and `b*t=7/8`; every other reading is clear.
The first isolation is therefore a single common endpoint. The adjacent cells
take 27 moves on the left and one on the right; the boundary itself takes one.
Exact replays at `z +/- 1/10000000` confirm the two sides. Thus a tiny perturbation
can remove a long handoff chain. Move count alone is not a stable progress measure
under perturbation.

## A general law extracted and proved in Lean

At speed `a`'s lap-`K` exit, the capture depth of speed `b` on lap `L` is

`g = 8*L + 1 - (8*K+1)*b/a`.

Capture on that lap is exactly `0 < g < 2`. If a return advances the laps by
`(r,s)`, then after `q` repetitions of that same pattern,

`g_q = g_0 + 8*q*(s-r*b/a)`.

Consequently two captured endpoints require

`abs(8*q*(s-r*b/a)) < 2`.

This bounds repetition of any fixed nonzero-drift pattern. Perpetual repetition
of the same pattern forces `a*s=b*r`, not `a=b`. For example `a=7,b=8` admits
recurring capture opportunities at laps `(6+7*q,7+8*q)`, with depth exactly one.
This is **not** an endless cascade: the intervening times need not stay blocked.

These statements are formalized in `LRC/Spec/HandoffDriftN.lean`. They apply to
real speeds and arbitrary integer laps, not just the tested configurations.

## What this leaves to discover

There are now two explicit cases to track across the *whole* arrangement:
nonzero drift exhausts a fixed pair/advance pattern; zero drift preserves that
pair and requires information from the other readings. Changing pairs or lap
increments can also change the drift. The experiment does not show that seven
readings cannot sustain those changes indefinitely, nor establish a finite
global list of patterns. That remains the missing global argument.

## Reproduction

From the `LonelyRunner` project:

```sh
python3 experiments/nN/redo/handoff_boundaries_v1.py --test
python3 experiments/nN/redo/handoff_boundaries_v1.py --output experiments/nN/redo/handoff_boundaries_v1.json
lake build LonelyRunner.LRC.Spec.HandoffDriftN
lake env lean experiments/nN/handoff_boundaries_axioms_v1.lean
```

Arbitrary seven-reading paths can be supplied with `--speeds`, `--direction`
(both comma-separated rational lists), and `--radius`. Raw traces, exact walls,
grid residues/deviations, blockers, laps, and recurrence witnesses are in the JSON.
