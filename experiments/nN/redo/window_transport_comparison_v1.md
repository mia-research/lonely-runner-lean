# AP-window transport versus a two-exit place prediction

2026-09-29. Exact rational diagnostic; not a Lean theorem or universal coverage proof.

## Test fixed in the script

For eight targets, and each of eight subjects, normalize the ordered speeds to
span 7 and deform along x_j(s) = j + s(x_j(1)-j), 0 <= s <= 1.
The seven positive subject disparities have the form d_i(s) = a_i+s b_i.
For each natural lap vector k, compute its entire feasible parameter interval
from all 49 inequalities

    (8 k_j+7) d_i(s) - (8 k_i+1) d_j(s) >= 0.

Each is affine in s. Intersecting their exact half-intervals determines precisely
where this lap vector supplies an isolation window. Endpoints are included:
singleton isolation windows are not discarded. Direct window calculations at
both endpoints independently check the interval computation.

Start with the four AP lap vectors. If their intervals do not cover [0,1], use
the cascade at a midpoint of an uncovered interval to discover another vector.
This is discovery only: no cascade statement is used to verify interval coverage.
Limit discovery to 100 added vectors and 10,000 cascade moves per query; exhaustion
is not evidence of nonexistence. The selected targets consist of the AP, the
0.99-neighbour example, the three E176 exceptions, and three seeded random targets.

## Results

- 64 subject/path pairs; all 64 whole closed parameter intervals covered.
- Original four AP lap vectors alone cover 32 paths; the other 32 need new vectors.
- All endpoint clearance assertions passed.
- These are exact finite covers of these particular continuous paths, not merely
  checks at a parameter mesh. They are not kernel-checked Lean proofs.

For the endpoint subject of target (0,1,50,105,106,136,189,199), four of the
discovered windows already suffice. Coordinates are normalized to span 7.

| Lap vector, in runner order | Exact feasible s interval |
| --- | --- |
| (0,0,1,1,1,2,2) | [0, 1990/2837] |
| (0,1,2,2,3,4,5) | [199/738, 2189/2539] |
| (0,4,9,9,12,17,18) | [14726/17589, 4975/5038] |
| (0,6,13,13,17,23,25) | [3781/4271, 1] |

Consecutive intervals overlap. Thus a replacement isolation window is already
available before the previous selected one disappears. The corresponding time
can jump: this does not assert continuous transport of a single time-valued event.

## Independent two-exit prediction

On 2,008 endpoint disparity sets (the eight named targets plus 2,000 seeded random
sets), start at B = 1/(8 min d). Compute the first maximum captured-runner exit.
If exactly one runner is captured there, predict its exit as the isolation place,
WITHOUT assuming that exit clear.

- 1,066 sets clear at B.
- 599 do not have exactly one blocker after the first move (includes already clear).
- 343 have exactly one: 178 predicted exits are clear, 165 are still obstructed.
- Every clear predicted exit agrees with the independent capped cascade landing.
  This checks consistency, not an independent proof of the cascade itself.

Counterexample: disparities (99,200,300,400,500,600,700).
At B=1/792, runner 700 blocks. Its exit is 9/5600; only runner 600 blocks
there. Runner 600 exits at 3/1600, but runner 500 then blocks. Consequently
'exactly one incoming runner' alone does not imply a successful second exit.
Adding 'and its exit is clear' to the class is sound but assumes the desired
clearance; the task is to derive it from additional speed inequalities.

## Interpretation and next mathematical obligation

The methods are not mutually exclusive: two-exit rules can discover particular
lap vectors. Window inequalities are the more informative verification layer
because they describe an entire continuous region and expose the overlap.

The useful next target is to derive replacement lap vectors and their overlapping
feasible intervals from symbolic constraints on an arbitrary target, rather than
discovering a new list for each numerical target. No uniform bound on the number
of windows, lap labels, or cascade moves is established here. The finite reference
category reduction alone does not supply that missing coverage theorem.

Reproduce: `PYTHONDONTWRITEBYTECODE=1 python3 experiments/nN/redo/window_transport_comparison_v1.py`.
The run prints every path result and both summaries. No existing source, log, or
other session's experiment was modified.
