# Changed-lap replacement and review of Claude E352–E361

2026-10-04. Symbolic proof and Lean formalisation, not an exhaustive cover.

## New result

Use the moving core windows from `MovingCoreWindowsN`, with positive parameters
b,c,e, b ≤ 7, e ≥ 101/20, and the weaker condition 51b ≤ 91c.
The original linear core-window guards remain explicit. If an added reading
V ≥ b swallows the first three windows, its capture labels are forced to be
(1,4,6), and

    31c/17 < V < 49b/47.

The old rescue in [9,63/b] used 1105b ≤ 1953c. The new replacement is

    R = 49/e, ordinary time t = 49/(8e).

At this instant use core lap labels q = (1,3,4,6,7,8), and added-reading label 8.
The sufficient region is given entirely by linear guards:

    1105e ≤ 1519c,
    2401b ≤ 3337e,
    (8q_i+1)e ≤ 49d_i ≤ (8q_i+7)e, for every core reading i.

The first two inequalities place the entire forced residual V-interval inside
[65e/49,71e/49]. The remaining guards prove core clearance independently.
In particular, if d_5=b, the guard 65e ≤ 49b is required; clearance of V alone
does not establish it.

`MovingCoreFallback.family_isolated` proves existence for EVERY V ≥ b in this
core region. No upper bound on V is assumed: outside the forced residual
interval, one of the first three core windows already supplies isolation.
No intermediate cascade exit is needed for this existence theorem, and it
does not assert that R=49/e is the first cascade landing.

## Non-vacuous extension across the old boundary

Lean-checked core:

    d = (1, 29/10, 55/14, 253/50, 32/5, 7),
    b=7, c=55/14, e=253/50.

It satisfies all 48 old core guards and all 12 replacement guards, but
1105b > 1953c. All V ≥ 7 are covered by the new theorem.

For V=721/100 specifically, all three early windows are swallowed with
labels (1,4,6). The old late core window is [9,9], where VR=64.89 is captured.
Its proposed replacement is R=6500/721 > 9 and therefore too late for that
window. The new instant R=2450/253 is clear for all seven readings.
The audit proves the capture inequalities and strict old-window miss exactly.

## Delegation and independent checking

Claude received a bounded, read-only task: verify the replacement algebra,
derive all core guards, and find a rational example beyond the old face.
It confirmed the containment algebra and identified the separate core guard
65e ≤ 49b. Its returned example used e=21/4 and did NOT give a full core:
that value violates the old late-window guard 9e ≤ 47. It was rejected.
Its suggestion that the residual upper bound was unavailable also overlooked
the supplied V < 49b/47 and containment guard. Neither claim was used.

The corrected full core above was checked independently using exact fractions,
then verified in Lean for all added speeds. Claude's output is discovery
evidence; the theorem and its hypotheses are the proof.

## Verification

- `lake build LonelyRunner.LRC.Spec.MovingCoreFallbackN`: PASS.
- `lake env lean experiments/nN/moving_core_fallback_axioms_v1.lean`: PASS;
  all 12 printed declarations use only standard Lean axioms (or fewer).
- Existing `moving_core_windows_axioms_v1.lean`: PASS after the refactor;
  all 12 original declarations/regressions remain axiom-clean.
- No sorry, native_decide, or new axiom introduced.
- Full Spec gate NOT run. No commit or push in this turn.

The extraction was factored into `family_isolated_of_residual`, with its
residual existence obligation explicit. Both concrete family theorems
discharge that obligation. Existing theorem interfaces are retained.

## Latest Claude work: formalisation opportunities

Reviewed running log through E361 and `k6map_structure_v1.md` and
`tie_structure_v1.md`.

1. **R1/R2, swallowing whole clear components:** much of this is already
   formalised by `CoreWindowInsertion.swallowed_iff`, `swallowed_speed_iff`,
   and `CoreWindowCompatibility.joint_capture_iff`. The additional bridge is
   an exhaustive component description of the six-reading clear set; do not
   duplicate the interval algebra or assume component coverage.
2. **Singleton windows:** the promising next theorem is that an interior
   isolated clear instant has both a phase-1 reading and a phase-7 reading,
   and conversely these boundaries isolate a clear instant locally for a
   finite set of positive readings. `WindowPinchN` and `PinchReflectionN`
   already supply related fixed-lap and active-boundary machinery; extend
   those carefully to the local modular-clear-set equivalence. Truncated
   domain endpoints require separate treatment. This addresses zero-width
   cases without discarding equality.
3. **Pins and chains of tight constraints:** connectedness of the graph of
   tight binary constraints at a positive normalised vertex is a useful
   symbolic target. An independent basis can be a spanning tree; all tight
   rows need NOT form a tree when extra equalities hold. Products along a
   path generalise `MappedCascadeRules.two_capture_speed_bound`. This does
   not yet bound the products. Restricting anchor heights to {1,7,9} needs
   the corresponding cell/history hypotheses, not an arbitrary-lap claim.

## Corrections that constrain what we may formalise

E354 refutes the apparent ~16.2 gate-crosser ceiling with X24 (~24.38).
E359 refutes the first-window longest-component lower bound 2/(7 rho_6).
Neither is available as a theorem premise unless explicitly assumed.
The native order-seven slack result is not refuted: it does not put its
window inside the first [1,7] window. Sampled absence of mixed reference
classes was also retracted; region representatives do not determine all
windows throughout their region.

E361's lap-free profile proposal needs another distinction: removing lap
labels does NOT make raw component counts uniformly finite. Already the
first two normalised readings (1,8n), for any positive integer n, leave
exactly 6n disjoint positive windows on [1,7]:

    [(j+1/8)/n, (j+7/8)/n], j=n,...,7n-1.

This can be the first two readings of an ordered seven-reading arrangement;
its stage-two profile therefore has unbounded counts. The nearest reading
is already fixed to 1, so this is not removed by overall rescaling. This
does NOT rule out finitely many parameterised mechanisms: this entire
infinite family itself has the one formula above. A finite classification
must quotient such repetitions or keep n as a parameter, rather than count
each raw profile as a separate finite type.

## Remaining boundary

We have covered a genuine additional variable-core region, not all of
1105b > 1953c. Cores failing the new guard inequalities still require a
different replacement or a proof that an earlier window cannot be swallowed.
No exhaustive cover or global n=8 proof is claimed.
