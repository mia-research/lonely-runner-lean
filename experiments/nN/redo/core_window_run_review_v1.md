# Findings index v4: mechanisms formalised from E366 and E316/E327

2026-10-04. Read the complete attached `CASCADE_FINDINGS_INDEX_v4.md`
(E269–E362), then running-log E363–E366. Document instructions were treated
as source material, not permission to change shared logs or other sessions.

## E366: now a general symbolic theorem

Source: `LonelyRunner/LRC/Spec/CoreWindowRunN.lean`.

Let S be any finite positive core and V a positive inserted reading.
Suppose a finite cascade zone run starts at b and ends at T. Let [L,U]
be a core-clear window with b≤L≤U<T. Then:

- exactly one V-zone contains the whole closed window;
- its named pair (V,K) occurs in the supplied run;
- the result includes L=U (singleton windows);
- the actual max-exit iteration supplies such a run via `run_of_iterate`.

This strengthens `Run.covers`, which previously supplied only a blocking
reading, to a covering zone explicitly present in the path. Whole-window
containment reuses `CoreWindowInsertion.swallowed_iff`; it is not a new
version of the E302/E354 interval argument.

For E366 set S to the six slower readings, V=rho_7, b=1/8, and
[L,U]=[A/8,B/8] for a K6 window [A,B]⊆[1,7]. Any run endpoint above 7/8
passes it. No visit to R=9, termination theorem, or complete template list
is needed for this conditional path constraint.

## The observed distinctness also has a proof

Take ordered core-clear points a<b in different components, with a core
reading d blocked at some intervening s. Its whole zone lies between a
and b: neither endpoint can be inside that zone, since both are core-clear.

If d≤V, this core zone is at least as wide as a V-zone. Hence the same
open V-zone cannot contain both a and b. `different_components_different_labels`
formalises this using the separating blocked point, not a precomputed list
of components. `labels_ordered` then shows the distinct V-lap labels increase.

Thus the distinct-zone and ordering implications are symbolic, not merely
12,078 successful checks. A separate finite-list cardinality theorem was
not added; the injection ingredients are now proved.

The theorem is independent of core size. It applies with five readings
and V=rho_6 as well, whenever a run passes a K5 window. This supplies the
one-level-down implication named as untested in E366, without asserting
that every K5 window is passed or giving an exhaustive K6 template list.

Do not read "middle readings cross the gaps" as exclusivity: extra V moves
between core windows remain possible, as E366 itself reports.

## Earlier work recovered: inert replacement

Source: `LonelyRunner/LRC/Spec/InertReadingN.lean`.

E316/E327's sufficient rule is now proved against the actual `move`:
inserting a reading clear at each visited core state preserves every move
in the specified finite prefix. Two such readings can be interchanged
without changing that prefix. A reading merely having the same phase at
one event does not satisfy this premise automatically.

This gives a sound reduction for inactive readings. It does not erase
active readings or prove a universal finite collection of arrangement types.

## Other formalisation priorities from the whole index

1. **E312/E313 local crossing and tail update:** connect a changed endpoint
   inequality to the creation or disappearance of the actual neighbouring
   clear component, preserving equality/touch cases (E317's exception).
   Reuse the existing pinch/deformation modules before restating derivatives.
2. **E277/E280 simultaneous boundaries:** audit the existing active-boundary
   inequalities against the tied cases before proving a new multi-pinch
   classification. First-order tests alone did not decide every tie.
3. **E359 singletons and tight-row chains:** extend the existing fixed-lap
   pinch machinery to the local modular-clear-set singleton criterion;
   formalise connected tight-constraint paths with vertex hypotheses explicit.
   Extra tight rows need not themselves form a tree.
4. **E364 templates:** use the mandatory inserted-zone labels above to
   derive linear constraints for symbolic window families. The count 115
   is sampled, not an exhaustive theorem. No universal bound on the middle
   readings or positive K6-width floor has been established by these results.

The static inserted-speed compatibility algebra is already in
`CoreWindowInsertionN` and `CoreWindowCompatibilityN`. The new work is the
connection to path membership, distinctness, order, and inert replacement.

## Gate follow-up

`FirstGateN` formalises the unconditional width rule and exclusion of lonely
endpoints in (7,9), and proves the full three-event equivalence under the
explicit additional hypothesis that non-minimum readings are ≥2. The width
argument alone does not prove the unrestricted equivalence marked PROVED
in E340. See `first_gate_formalisation_v1.md` for the exact local skip
example and the distinction from a full run starting at R=1.

## Verification and scope

Targeted builds: `CoreWindowRunN`, `InertReadingN`, `FirstGateN`.
Audits: `core_window_run_axioms_v1.lean` (8 theorems + singleton regression),
`inert_reading_axioms_v1.lean` (3 theorems), `first_gate_axioms_v1.lean`
(14 theorems + 3 local-skip regressions). Only standard Lean axioms.
Full Spec gate not run. No commit/push or shared-log edits in this work.

These are necessary constraints on a run that passes supplied windows,
plus a sufficient inert replacement rule. They do not prove that every
arrangement supplies an exhaustive window family or that its cascade ends.
