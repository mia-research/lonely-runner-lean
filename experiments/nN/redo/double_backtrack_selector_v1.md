# Deriving the useful first replacement, rather than reflecting repeatedly

2026-09-30. This implements the agreed comparison of the four-window path with
the reflection path. It derives the FIRST useful replacement and a substantial
region where that choice works. It does not select all later replacements.

## The speed-based rule

Let t be the old clear/pinched event, d_i>0 the current disparities, q_i the old
clear lap labels, and f_i=d_i*t-q_i in [1/8,7/8]. Before testing any new isolation,
compute

    c_i = 1 if f_i >= 9/16, otherwise 0,
    p_i = 2*q_i+c_i.

These are exactly floor(2*d_i*t-1/8), the last-opening labels at time 2*t.
Both old pinching boundaries move strictly inside clearance: 1/8 -> 1/4 and
7/8 -> 3/4 modulo one. The ONLY possible new blockers are old phases strictly
between 7/16 and 9/16.

Now move BACK from 2*t to the latest preceding opening:

    age_i  = (2*f_i-c_i-1/8)/d_i,
    delta  = min_i age_i,
    T      = 2*t-delta = max_i (p_i+1/8)/d_i,
    need_i = max(0, (2*f_i-c_i-7/8)/d_i).

Every runner's lower bound holds automatically at T. All upper bounds hold
EXACTLY when max_i need_i <= delta. Only the middle-phase blockers contribute
a positive need. This is a necessary-and-sufficient pointwise test, not an
assumption of future isolation. If max need < delta, every upper margin is
strict, giving strict pairwise slacks and a replacement available beyond the
pinch in any deformation direction.

Equality needs care: clearance at a single parameter does not by itself imply
right extension. The regression constructs an old genuine pinch for which
delta=max need=0 and the selected window also dies immediately on the right.

## Exact comparison on the wide example

For the deformation toward (0,1,50,105,106,136,189,199), normalized to span 7,
the first chosen AP window has q=(0,0,1,1,1,2,2). Its pinch is

    s*=1990/2837,   t*=2837/7336.

The old fractional readings there are

    (1/8, 371/524, 365/1048, 62/131, 7/8, 65/131, 741/1048).

The rule computes carry bits (0,1,0,0,1,0,1), hence

    p=(0,1,2,2,3,4,5).

No replacement labels were provided to the selector. The last opening is that
of runner 7, on lap 5, giving T=41/56. Its exact backward quantities are

    delta=303/7336,
    max need=212775/11326784,
    strict difference=1947/86464 > 0.

The selected lap vector is feasible over

    [199/738, 2189/2539].

It is therefore already available WELL BEFORE the old pinch and extends well
beyond it. Compare the first reflection, whose right endpoint is only 3184/4535
(approximately 0.702095), just beyond the old 0.701445 pinch. The useful window
ends at approximately 0.862150. Following the same late reflected event is not
necessary.

## A broad symbolic region, not only the numerical target

Normalize by the nearest disparity AT THE PINCH. Consider

    (1, r2, r3, r4, 15, r6, r7),
    5 <= r2 <= 6,       10 <= r3 <= 11,
    23/2 <= r4 <= 12,   19 <= r6 <= 20,
    43/2 <= r7 <= 22.

The old q labels are clear at 1/8, pinned by disparities 1 and 15. The selector
computes p throughout this region. The time 41/(8*r7) satisfies all lower
bounds and STRICT upper bounds. `region_lonely` proves actual endpoint-subject
loneliness for the corresponding eight-runner arrangement. All runners are
included in the proof.

There are five free ratios on this particular pinch surface because its two
pinning readings satisfy r5=15*r1, in addition to scale normalization. This
does NOT add to or contradict the six factors of the full arrangement space.

For arbitrary span-7 target speeds d1,...,d7, this region translates into
explicit linear conditions on the original factors. Put

    E=15*d1-d5 < 0,
    W_i=10*d_i-i*E,
    W_1=d5-5*d1 > 0.

The pinch parameter is 10/(10-E), and its ratios are r_i=W_i/W_1
(`first_pinch_ratio`). Thus, for example, 5<=r2<=6 means
5*W_1<=W_2<=6*W_1; all five interval conditions are linear in target speeds.
This defines a target-speed region, not an enumeration of its points. The
five-ratio region and the ratio identity are proved in Lean; no universal
assertion that every target satisfies these bounds is made.

## Tests and failure branch

The exact selector was tested on the same 459 AP-path pinches as reflection:

- 261 produce a window extending strictly past the pinch;
- 198 fail the pointwise backward-budget inequality;
- no pointwise-clear but non-extending cases occurred in this population,
  but the additional equality regression explicitly supplies such a case.

The first failure is on the SAME wide target, with old labels
(0,1,2,3,4,5,6), at s=199/483 and old time 7/8. The far runner allows rollback
only 1/56, whereas the nearest runner requires 231/776. These are incompatible.
This diagnoses a definite pair of inequalities; it does not imply no other
replacement is available.

## Remaining work

The first useful switch is now selected from the readings and analytically
justified on an explicit region. The next branch to investigate is the failed
rollback: which other already-available window is forced by the runner needing
more rollback and the runner whose opening prevents it? We must derive that
replacement, not assume the budget inequality eventually becomes true.

The global order-8 theorem remains open. Neither the success count nor this
region proves global coverage. No commit, push, or full Spec gate was performed.

## Verification completed

`LonelyRunner.LRC.Spec.DoubleBacktrackN` builds successfully (8,267 jobs,
including replayed dependencies). All 17 audited declarations and regressions
use only propext, Classical.choice, and Quot.sound. This includes the exact
label selector, clearance criterion, region's selected maximum-opening time,
and `Arrangement.LonelyAt` conclusion. Both the 459-pinch comparison and the
separate equality regression pass with exact rational arithmetic.

The carry bits give finitely many phase branches for any fixed old lap vector.
The old integer lap labels remain unbounded; this is not a claim of finitely
many complete histories over the whole arrangement space.
