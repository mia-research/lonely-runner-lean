Rules: 1–4, 8–20.
# Native opening-face exchange and grid cohorts — 2026-10-28, v2

[L] Two competing captured openings force the next actual maximum opening when the remaining captured readings' original opening comparisons lie below that maximum; no target isolation is assumed.
[L] At a reference competitor opening T0, a moved reading satisfying dT0=N+1/8+ε has its own opening before/equal/after T0 exactly when ε is positive/zero/negative; this is an exact arbitrary-real speed-deformation rule, not a floating-point approximation.
[L] For tied readings dT=N+1/8 and sT=K+1/8, d(8K+1)=s(8N+1); at positive T they share scale h=1/(8T), with d=h(8N+1),s=h(8K+1).
[L] CohortClass has all currently captured physical readings sharing that opening and retains each originally clear outsider's closing comparison independently; their shared opening is derived as an actual move.
[L] GridCohortClass is proved equivalent to CohortClass using its exact local residue-one scale representation, keeping the chosen subject moving and the original eight speeds positive/distinct.
[L] This is a partial disparity-grid cohort around one chosen subject, not a complete residue grid for all physical speeds and not simultaneous isolation of every runner.
[L] Captured partner inputs permit either s_i≤3s_c or the exact selected opening tie, while clear outsiders require the selected opening not to pass their original current-window closing.
[L] These inputs preserve every original integer window, so an actual partner move joins the previously proved NoReturnClass and isolates the subject.
[L] PartnerClass and CompactClass coalesce: choose the fastest physical tied setter, preserving the same selected opening; tied partners then satisfy the compact ratio and the earlier compact partners still do.
[L] The earlier HandoffRelativeClass embeds into this compact-partner input by deriving the outsiders' exact closing comparisons from its sufficient retained quarter faces; no clear outsider is deleted.
[L] FaceClass combines the two-candidate actual handoff and its selected branch's partner input, joining the old no-return family; six catalogue bridges preserve21 overlapping top-level alternatives rather than add disjoint type counts.
[T 5043/5043] Every one of1681 multiple-frontier physical controls (1005 original,676 previous deformations) generates three exact speed perturbations across its competing-opening face;5032 proposals remain admissible and11 inadmissible proposals are retained.
[T 5032/5032] Every admissible proposal replays its complete default cascade to isolation; this is finite point evidence, not proof of universal occurrence or full n=8.
[T] Selected reading label/capture is preserved4959 times and changes73 times; clean below/tie/above face exchanges number1672/1661/1600, while26 stable controls retain an additional symmetric tied-group competitor and are kept outside the simple pair exchange.
[T] Stable local outcomes include3387 no-return isolations,266 recovered-positive-return isolations and1306 continuing moves; all5032 local inputs include3459 no-return,266 recovered-positive-return and1307 continuing moves.
[T] Only2490 new default histories visit their supplied old local entry; actual local move tests and default-path occurrence remain separate, and all unvisited/changed-prefix controls are retained.
[T 46/46] Admissible deformations that cross a physical speed rank are sorted/relabelled exactly, and the named subject/setter correspondence and entire default move history are checked under that permutation; no equal or stationary physical speeds are admitted.
[T 165190/165190] Partner consumers cover137597 original stored handoffs,12248 earlier deformed-history moves,5032 new local entries and10313 new default-history moves; these populations can overlap and are not165190 distinct arrangements.
[T] Across those input checks,27000 satisfy compact-or-tied partner conditions,18611 satisfy the stronger shared-opening cohort condition, and1174 cohort checks have several distinct disparities; their grid representations and no-return outcomes agree exactly.
[T] The retained exceptions include817 no-return inputs beyond the sufficient partner ratio/tie input,3885 isolations with positive recovered returns, and133488 continuing moves; no sufficient inequality is promoted to a universal forced condition.
[EXACT] native_opening_face_exactness_v3 validates five script/result pairs, original source hashes and inherited exactness links; every new computation uses Fraction/Lean real arithmetic and all equality boundaries remain exact.
[SCOPE] These are proved native deformation/handoff rules, a local grid equivalence and coalescence of sufficient isolation inputs; forcing every admissible arrangement into such an input remains open.
[NEXT] Follow the outsider closing boundaries in the1307 new local continuing cases and the changed-label controls; the tied cohort can clear while outsiders return, so the reference grid must retain their actual carried/returned phases rather than supply isolation by itself.
[FILES] Lean:NativeOpeningFaceExchange.lean,NativeCapturedPartnerJoin.lean,NativeCohortReturns.lean; controls:native_frontier_tie_deformation_v1,native_captured_partner_controls_v1–v4,native_opening_face_exactness_v3.
[PROVISIONAL: counting tool] Inherited grid/ceiling selectors; [PROVISIONAL: covering] inherited finite parameter joins; this work introduces neither density/coverage nor a global time/move budget.

[L] Without assuming outsiders retain their windows, every currently captured shared-opening cohort member has zero label advance and clears at the common opening; any capture afterward must be a previously clear outsider.
[L] An outsider returns exactly when its original closing boundary is strictly passed; closed equality retains clearance, and independent advances remain unbounded.
[L] Isolation at the cohort opening is equivalent to clearance of those originally clear outsiders alone; this is a local reduction of duties, not a claim that future capture sets decrease.
[L] RecoveredCohortClass allows positive outsider returns whose new lower openings have already passed; it embeds into the existing CanonicalReturnClass and proves isolation, while retained CohortClass embeds into RecoveredCohortClass.
[T] Across165190 overlapping move checks,124346 have a shared captured opening;20738 satisfy recovered-cohort inputs, comprising18611 retained-cohort inputs and2127 positive-return recovered-cohort inputs;103608 shared-cohort moves continue.
[T] Multiple-disparity shared cohorts occur1709 times across overlapping populations;535 have returned outsiders and516 continue, preserving the counterexamples to tie-alone isolation.
[AUDIT L] FullAuditV37 PASS1260 theorem reports/270 modules, only propext/Classical.choice/Quot.sound, all source hashes matching; three new modules and six catalogue bridges add36 reports sinceV35.
[INTEGRATION] Prior audited sources remain byte-identical except the owned ArrangementTypesOct26 catalogue; source comparisons v35_to_v37 and v36_to_v37 retain the evidence.
