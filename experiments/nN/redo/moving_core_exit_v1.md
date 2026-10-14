# Continue both obstruction branches through named exits

2026-10-04. Source: `MovingCoreExitN.lean`.
Uses the same four moving core windows and their endpoint inequalities,
not a new experimental catalogue. Ordinary Lean time is t=R/8.

Write a=d₁, c=d₂, e=d₃, f=d₄, b=d₅. The base region retains
b>0, c>0, b≤7, e≥101/20, 51b≤91c, 1953c≤1105b, positive core readings,
and V≥b. All four original core-window inequalities remain explicit.

If the first three windows are all swallowed, earlier proofs give

    31c/17 < V < 49b/47.

Every family theorem below quantifies over ALL V≥b: surviving early
windows cover the other added speeds. The specified replacement is only
needed for the forced residual interval. There is no assumed upper bound
on the added speed in the family conclusion.

## Second-reading obstruction: 31e≤49a

The direct exit 33/a is not automatically lonely. For example, with
a=33/10, c=55/14, e=253/50, f=32/5, b=7, it occurs at R=10, where c reads
275/7, strictly between 39 and 41. With V=721/100 the added runner reads
72.1, also captured. Continuing to a different setter is necessary here.

### c opens: R=41/c

Core lap labels (1,4,5,6,8,9). Additional guards:

    73c≤41b,   41f≤71c.

Every other core band constraint follows from the base inequalities and
31e≤49a. The added runner lies in [73,79] at this instant, directly from
the forced residual interval and 51b≤91c.

### b opens instead: R=73/b

Use the same labels. In the opposite ordering 41b≤73c, it suffices that

    73f≤71b.

The whole core is clear; V is again in [73,79]. Thus the previous
b/c ordering condition is handled on BOTH sides, rather than left owed.

### f obstructs either instant: R=73/f

Failure of either f-closing condition implies

    3621b≤3731f.

This lower ratio is derived, not guessed from samples. At f's next exit
use labels (1,4,5,6,9,9). It suffices that

    41f≤73c,   73e≤55f.

All other core and inserted-reading inequalities are derived. If instead
73c≤41f, the earlier c-opening R=41/c is clear with f already on lap 9;
`late_c_family` covers that side as well.

### Combined result

`a_branch_family` combines every ordering above. Under the base region
and 31e≤49a, the ONE additional sufficient condition is

    73e≤55f.

No further order of the c, b, or f exits is assumed. This is a family
theorem, not a single core calculation. It follows actual lap changes
while carrying all the other readings. It proves a lonely instant, not
that the chosen instant is necessarily the first cascade landing.

## Fifth-reading capture strip: 63e≤49f≤65e

Use its exit R=65/f, with labels (1,3,4,6,8,8). In the same base region,
two additional guards suffice:

    65a≤31f,   3185b≤3337f.

The initially apparent guard 65c≤39f follows from the second condition,
1953c≤1105b, and b>0. It is not retained as an independent premise in
`f_family_two_guards`. All other core inequalities are derived. The
added reading is in [65,71] there for the entire residual interval.

## Non-vacuous Lean regressions

Each example is a whole family over every V≥7, with all original core
windows checked in Lean:

- (1,33/10,55/14,253/50,32/5,7): the a-obstruction is strict;
  the c-opening is R=574/55.
- (1,29/10,55/14,253/50,669/100,7): f lies strictly in the previously
  uncovered capture strip; its exit is R=6500/669.
- (1,33/10,55/14,253/50,137/20,7): BOTH earlier f-closing conditions
  fail. The combined a-branch proof still supplies isolation for all V≥7,
  with the f-exit mechanism available at R=1460/137.

The first two examples were also independently checked with exact Fractions.
The third is checked as an all-V Lean regression, not just a sampled V.

## What is still open

This does not cover every arrangement, or even every member of the base
moving-core region. In the a-obstruction branch, the combined theorem
leaves the possibility 55f<73e (e closes before f opens), although some
such cores are already covered by the individual earlier branches.
In the f-strip branch, cases failing 65a≤31f or 3185b≤3337f need further
transport or a different available window. The inserted runner's own
next exit must not be silently omitted in those cases.

The next analytical work is to carry these specific closing/opening
conflicts further, or show that other original windows survive there.
No global termination or exhaustive template cover is assumed.

## Verification

Target: `lake build LonelyRunner.LRC.Spec.MovingCoreExitN`.
Audit: `lake env lean experiments/nN/moving_core_exit_axioms_v1.lean`.
Logs: `/tmp/n8_core_exit_build.log`, `/tmp/n8_core_exit_axioms.out`.
The targeted build and audit passed; all 27 printed declarations use
only standard Lean axioms (or fewer), including all three all-V regressions.
Full Spec gate not run. No commit/push or shared-log edit in this work.
