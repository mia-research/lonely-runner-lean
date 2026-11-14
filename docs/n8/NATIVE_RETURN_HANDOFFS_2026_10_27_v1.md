Rules: 1–4, 8–20.
# Native returner handoffs — 2026-10-27, v1

[L] NativeReturnHandoff derives the next actual move from surviving original physical readings and their opening comparisons, without assuming clearance at its destination.
[L] For an actual Q→P, write s_i=|v_i−v_k|, L_i=ceil(s_i P−7/8), and S={i≠k:advance(s_i,Q,P)>0 and s_i P<L_i+1/8}; S equals the captured set at P.
[L] A survivor j forces P→R_j=(L_j+1/8)/s_j exactly when s_j(L_i+1/8)≤s_i(L_j+1/8) for every i∈S; a maximal survivor exists, and ties give the same actual opening.
[L] A sole physical survivor needs no opening-order assumptions; multiple physical survivors of one equal disparity also force their common opening, including symmetric competitors around an interior subject.
[L] The selected reading has zero advance to its own opening; if all previous survivors share its disparity, every new survivor lies outside that previous group.
[OWED] Replacement of a group does not imply globally decreasing survivor sets: newly captured outsiders can form a larger group.
[L] NativeReturnHandoffArrangement joins no-return and recovered-return successors to the already proved NoReturnClass and CanonicalReturnClass, preserving actual positive two-move traces.
[L] Relative-entry family: each other captured reading has s_i≤3s_j, while every clear reading satisfies s_i/4≤s_j(L_i+7/8−s_i P); these entry inequalities derive unchanged labels at R_j.
[L] First-closing c satisfies s_i(L_c+7/8)≤s_c(L_i+7/8) for every physical i≠k; its sufficient quarter face is s_c/4≤s_j(L_c+7/8−s_c P).
[L] NativeHandoffEntryFaces proves the exact sharp entry face s_c(L_j+1/8−s_j P)≤s_j(L_c+7/8−s_c P) iff every successor label is unchanged, given actual handoff entry and first-closing order.
[L] No-return at R_j is also equivalent to zero advance of this single first-closing reading; failure of the sharp face forces that reading to advance, without asserting it remains captured.
[L] Inclusion chain: relative-entry⊆quarter-entry⊆sharp-entry↔no-return-successor⊆recovered-successor; sole-survivor variants remove the opening-order input.
[L] Ten new catalogue bridges reuse branch21; the21 overlapping top-level alternatives are unchanged, and these inclusions are not disjoint arrangement counts.
[T 129197/129197] All22476 survey and106721 nearest-tree handoffs reproduce actual recorded next moves from S alone, retaining all ties and continuing outcomes;15959 no-return,1769 recovered-return and111469 continuing successors.
[T 20160/20160] The complete four-block physical controls include15120 interior subjects and8400 handoffs:2525 no-return,510 recovered-return and5365 continuing;18 handoffs have several physical survivors of the same disparity.
[T 137597/137597] Sharp entry agrees exactly with no-return on all three complete stored handoff populations:18484 sharp-entry successes,11340 quarter successes,7144 sharp successes beyond quarter.
[T] Complete entry-face v2 controls verify the single first-closer return criterion:103185 continuing successors retain that closer captured,13649 clear that closer while another reading survives, and2279 recovered successors clear all returned readings.
[T] All137597 original selected setters avoid immediate reselection; this is a local law and supplies no bound on future repeats or the number of moves.
[T] The full survey/nearest consumer detects20714 cases where a sole previous survivor is replaced by several new survivors; all such cases remain in the continuing population.
[EXACT] Scripts/results are source-hash linked; AST checks reject float literals/calls, and all116599 stored states of the4939 nearest-tree controls remain Fraction; old float-LP regions are not certified.
[SCOPE] These general local theorems and conditional entry families do not establish that every admissible arrangement reaches one of the isolation families; full n=8 remains open.
[NEXT] Separate the forced first-closer return into recovered/continuing outcomes and follow its interplay with the other surviving original readings;13649 continuing controls have already cleared the first closer, so “the closer always sets the next move” is false on these exact points.
[FILES] New Lean:NativeReturnHandoff.lean,NativeReturnHandoffArrangement.lean,NativeHandoffEntryFaces.lean; exact controls:native_return_handoff_map_v1,native_return_handoff_consumers_v1,native_return_handoff_physical_v1,native_handoff_entry_faces_v1/v2,native_handoff_exactness_v1.
[PROVISIONAL: counting tool] Inherited grid/ceiling opening selectors; [PROVISIONAL: covering] inherited finite parameter joins; new ceiling labels coordinate given states and select no isolation time.
