# Moving-core replacement: derive the guards and cross another lap boundary

2026-10-04. Work within the AP/grid deviation and cascade-window route.

## Result

Write the six core readings as d₀,…,d₅, with c=d₂, e=d₃, b=d₅.
Retain the four original core windows and their exact linear endpoint
conditions from `MovingCoreWindowsN`. Assume

    0<b, 0<c, b≤7, e≥101/20, 51b≤91c,
    1953c≤1105b, V≥b, and all core readings positive.

This is the side where the original R=max(9,65/V) rescue need not fit.
Earlier work required an additional collection of linear guards to use
R=49/e. The new derivation proves that all those extra conditions follow
from the original windows except

    49d₁≤31e, 49d₄≤63e.

In particular the inserted-reading conditions 1105e≤1519c and
2401b≤3337e are DERIVED, not separately assumed. The whole core lower
band constraints and four of the six upper constraints are derived too.

## A changed lap recovers another region

If 65e≤49d₄, the fifth core reading has already exited its next capture
zone at the same instant R=49/e. Use labels

    (1,3,4,6,8,8)

instead of (1,3,4,6,7,8). Its new upper bound follows from the original
windows and numeric bounds. Thus it is enough that

    49d₁≤31e, and either 49d₄≤63e or 65e≤49d₄.

Each family theorem quantifies over EVERY V≥b, without a ceiling on V.
Either an early core window survives, or the previously proved forced
residual interval 31c/17<V<49b/47 places V safely in lap 8 at R=49/e.
The proof locates an isolation; it need not reproduce the first landing.

`isolation_or_two_obstructions` makes the remaining branch split exhaustive
WITHIN THIS CORE REGION: either isolation exists or

    31e<49d₁,
    or 63e<49d₄<65e.

The latter is a genuine capture strip, not the whole half-space beyond the
old closing edge. Equality at either end is handled as clear. The first
alternative is currently an unhandled closing-edge branch, not a claim
that no other lonely event exists.

## Exact regression beyond the previous family

    d=(1,29/10,55/14,253/50,69/10,7).

It satisfies all 48 original window endpoint conditions and lies beyond
1953c=1105b. The old fifth guard fails. At R=2450/253 its fifth reading
is 735/11, between 65 and 71, hence clear on lap 8. The regression proves
isolation for every V≥7, not just one sampled added reading. All original
and replacement inequalities were also checked independently with Fractions.

## Delegation

Claude was asked for a bounded symbolic investigation of the remaining
a- and f-blocker exits. Its reply did not preserve the supplied lap labels
(in particular b's lap 8) and did not use all supplied core constraints.
Its proposed continuation was not used as evidence or as a Lean premise.
The guard reduction and new family above were derived independently.

Potential next setters are 33/d₁ and 65/d₄ when the corresponding readings
are actually captured. A replacement there must recheck every other core
reading and V. No assertion that separation of those two alone suffices.

## Relation to the wider record

Read the latest E367–E369 as well as the previous index review. The new
J=3 counts remain float-LP tree results with explicit range and slack
limitations; they do not supply an exhaustive Lean cover. Their modest
growth for gate-crossing regions motivates finding reusable mechanisms,
not assuming the observed list has closed.

The working proof route remains:

1. ordered/scaled arrangement reduction;
2. AP/grid isolation and exact deformation/window inequalities;
3. derive available replacement labels from those inequalities;
4. show these mechanisms cover all remaining core regions and the entire
   deformation, without assuming that the sampled templates are exhaustive.

This work advances step 3 and gives a smaller, exact branch list for one
region in step 4. It does not prove step 4 globally. The full entry-by-entry
index-to-Lean crosswalk is still unfinished; this report is not that audit.

## Files and verification

Source: `LonelyRunner/LRC/Spec/MovingCoreTwoGuardsN.lean`.
Audit/regression: `experiments/nN/moving_core_two_guards_axioms_v1.lean`.
Build log: `/tmp/n8_two_guards_build.log`.
Audit output: `/tmp/n8_two_guards_axioms.out`.
Targeted build and audit both passed. All nine printed declarations use
only standard Lean axioms (or fewer), including the all-V regression.
No full Spec gate, commit, push, or shared-log update in this turn.
