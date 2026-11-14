Rules: 1–4, 8–20.
# Four-block packet exits — 2026-10-27, v3

[NOTATION] Unit physical block step; T=m+1/8,S=g+h+j,R=1/2+ST−a−b−e,N=4m+a+b+e,D=4+S,P_s=(N−sm+9/8)/(D−s),Z=(N+17/8)/D,L=(a+b+e+9/8)/S; all data exact and native gap laps explicit.
[L] UnitAPPacketPhase.phase_at_anchor proves one AP-packet phase identity for any named physical opening runner and return lap: readingi atP hasphaseq+1/8+(i−anchor)(uP−m), under explicit unit-step and integer-lap identities.
[L] FourBlockLongTailArrangement.LongTailClass proves all8subjects for p,q,r≥1,p+q+r≤4 under native bands andS+8R≤9, removing the earlier left singleton guard; retained actual setters7→6→5 lead to the closed third exit.
[L] FourBlockLongTailExit proves the strict complementS+8R>9 forces the next original setter4, keeping allseven readings; the exception is an actual continued branch.
[L] FourBlockFourthArrangement.FourthClass proves all8subjects for1+1+1+5 with5S+24R≤31,5≤S+4R and9<S+8R; its actual native setter sequence7→6→5→4 isolates atP_3.
[L] FourBlockOuterReturnArrangement.OuterReturnClass proves all8subjects for1+1+1+5 with3S+16R≤22,31<5S+24R,R>7/8; its actual native sequence7→6→5→4→7 isolates atZ.
[L] FourBlockOuterReturnBounds.closed_join provesZ=P_3 exactly when the supplied shared face5S+24R=31 holds; the two native mechanisms meet at the same opening.
[L] FourBlockInnerArrangement.InnerExitClass proves all8subjects for1+1+1+5 withS≤3,5S+24R≤39,13≤2S+8R,jL−e≥1/4,R>7/8; allseven original readings are proved clear atL without assuming isolation.
[L] InnerExit.earlier_faces derives31<5S+24R and22<3S+16R from its input faces, distinguishing its native parameter region from the previous return-exit region; no exclusion from every other existential catalogue representation is claimed.
[L] The inner anchor phase proof consumes UnitAPPacketPhase; FourBlockInnerEpisode now proves the full six-setter reference trace 7→6→5→4→7→3, and FourBlockInnerCutMove proves the strict cut forces only original reading 2 next.
[L] Every new all-subject class retains positive/injective physical inputs, arbitrary signed affine scale/common drift and subject relabels; no physical runner is made stationary.
[L] ArrangementTypesOct26 now consumes OuterTailCoveredClass; the previous outer-return family embeds into the common four-partition outer-tail family, and all earlier families remain included; its 20 top-level OR branches overlap and do not give an exhaustive type count.
[T576/576] Stored long-tail controls retain144initial-grid exits,168third-opening exits and264forced fourth continuations across both endpoint orientations.
[T1152+1152] Independent third-face original/mirror subject controls retain48exact endpoint exit equalities and48strict fourth-continuation controls.
[T720+720] Fourth-opening controls retain60clear/30captured endpoint cases,9lower/21upper equalities and18strictly beyond the earlier third exit;24invalid native parameter rows are explicit.
[T720+720] Outer-return controls retain42actual returned-endpoint exits,28without the earlier left input guard,12lower/18shared upper equalities and30negative captured controls;36invalid native rows are explicit.
[T840+840] Inner-anchor map retains10qualified six-setter reference exits with60internal and10opposite-endpoint checks;25invalid native rows and95unqualified endpoint rows are explicit.
[T288+288] Independent inner-cut controls retain24exits,12exact cut equalities,4double closed faces and12strict cases captured by original reading2;6invalid residual parameter rows are explicit.
[OBS] All new experiment paths use Fraction arithmetic; pre-run AST audits found only Fraction-based divisions and no float literals/calls on used paths.


[L] FourBlockInnerReturnMove separates actual outer capture S+8R<11 from its later isolation face; InnerCaptureBounds excludes S=3,R=1 by exact integer lap consistency, retaining the closed issue explicitly.
[NOTATION] K=(a+b+9/8)/(g+h), M=(m+a+b+e+17/8)/(1+S), P=(a+9/8)/g, w=(h+j)P−b−e, U=(2m+a+b+e+25/8)/(2+S), and tau_X=X−m.
[L] FourReturnClass proves all eight subjects for 1+1+1+5 with native bands, S≤3, 3S+8R≤17, 49≤11S+24R, jM−e+tau_M≤1, and gM−a≤7/8 or 9/8≤gM−a; tau_M lies in [1/2,7/12].
[L] FourBlockFourReturnEpisode proves the actual reference setters 7→6→5→4→7→3→2→4 when the named strict capture faces hold; a competing captured reading is allowed because every next opening is bounded by the directly proved native M exit.
[L] SingletonReturnClass proves all eight subjects at P from three packet faces: tau_P≥1/2, 1≤w+tau_P, and w+4tau_P≤11/4; the remaining six physical subjects reuse the native internal and opposite-endpoint witnesses.
[L] FourBlockSingletonReturnEpisode proves the corresponding actual eight-setter reference path ending 2→1 under its strict original singleton capture face; no isolation witness is assumed.
[L] FourBlockReturnJoins proves P=M at gM−a=9/8; the native M bounds imply the singleton packet faces there with w+tau_P=1, so the two opening roles meet exactly.
[L] FiveReturnClass proves all eight subjects at U from native bands, S≤3, S+2R≤19/4, 17≤5S+8R, jU−e+2tau_U≤2, and gU−a≤7/8 or 9/8≤gU−a; tau_U lies in [5/8,3/4].
[L] FourBlockLateSingletonMove proves only reading 1 is captured at M on its strict singleton strip; FiveReturnMove proves the next move P→U when 7/4<w+2tau_P<2, retaining all seven original competitors.
[L] The same UnitAPPacketPhase identity is consumed with inner anchor 3/return lap 1, returned anchor 4/lap 2, and returned anchor 5/lap 3; this is a shared phase mechanism, not a claim that every return has that diagonal lap role.
[T 576+576] four_block_four_return_map_v2 retains 12 qualified M exits, 60 unqualified endpoint controls and 2088 invalid native assignments; its earlier all-invalid calibration is preserved as v1.
[T 480+480] four_block_singleton_return_map_v2 retains 42 qualified P exits, 6 inner and 12 outer packet equalities, 18 unqualified endpoint controls and 1884 invalid native assignments; v1 is preserved.
[T 96+96] four_block_return_closed_join_v2 retains 4 exact opening equalities, 8 strict opening comparisons and 2 actual final setter ties {1,4}; 564 invalid native assignments remain recorded.
[T 12+12] four_block_return_branch_join_v1 verifies complete original reference paths and mirrors for all twelve prior strict-inner-cut controls: ten end at M and two at P; no global complement exhaustion is asserted.
[T 864+864] four_block_five_return_map_v4 retains 21 qualified U exits, 18 lower and 3 upper opening equalities, 6 original cut equalities, 87 unqualified endpoint controls and 6372 invalid native assignments; all three earlier calibrations are preserved.
[T 12+12] four_block_late_singleton_map_v2 verifies the native M→P→U conditions and original/mirror histories on all twelve later singleton-strip controls; the P exit faces fail and reading 5 is captured there.
[T 33+33] five_return_residual_map_v1 retains the unresolved strict U faces: only 1, only 2, or both 1 and 2 are captured, with all original subsequent histories and mirrors saved.
[T 33/33] six_return_roles_v1 finds relative return lap 4 in 3 cases and lap 5 in 30; only original reading 7 is captured at each recorded runner-6 return, so the return lap must remain explicit.
[L] FullAuditV12 PASS: 665 theorem reports across 179 modules, only propext/Classical.choice/Quot.sound, all source hashes matched; V11 (656/175) and V10 (628/161) remain historical snapshots.
[L] V10→V12 source comparison finds only ArrangementTypesOct26 changed among the earlier 161 modules; 18 new modules contain 37 new theorem reports, with no explicit sorry/admit/axiom declarations.
[OBS] All new return/singleton experiments use exact Fraction arithmetic; AST checks across 17 scripts found no float literals or float calls, and the original cascade/clear helpers use exact Fraction operations.
[OWED] Strict U cut continuations, both runner-6 return-lap roles, broader partitions and exhaustive residual classification remain open; full n=8 is not claimed, and explicit native integer indices are not asserted to exist for arbitrary gaps.
[PROVISIONAL: counting tool] Inherited grid/ceiling selectors; [PROVISIONAL: covering] inherited finite coefficient/parameter joins.

[L] FourBlockOuterLapPhase retains any supplied integer outer return lap rho at Q=(4m+a+b+e+rho+1/8)/(4+S); the original tail phase is rho+1/8+(i−7)(Q−m), with all original integer laps retained.
[L] The exact faces 11S+16R≤16rho−42 and 8rho−27≤7S+8R imply tau_Q∈[13/16,1]; all five AP readings 3..7 clear for 1+1+1+5 without a fixed return-lap assumption.
[L] Original cut 2 requires its own integer window kappa: rho−kappa−3/4≤jQ−e+4tau_Q≤rho−kappa; the earlier one-sided cut candidate incorrectly fixed that window for the lap-6 outer return and is superseded.
[L] OuterLapClass proves all eight subjects from these native faces and the explicit two original cut windows; its finite normal form forces rho=4,5,6 and 0≤ell≤kappa≤2, by native phase/order identities and integer consistency.
[L] OuterLapMove proves the actual runner6→7 handoff on any retained lap q with tau_6∈(3/4,1) and the named Q_(q+1) exit bands; all original competing openings are retained.
[L] OuterTailClass extends the same packet proof to p,q,r≥1,p+q+r≤4: the four physical partitions 1+1+1+5,2+1+1+4,1+2+1+4,1+1+2+4; readings 4..7 clear automatically and the three original left readings have explicit bands L.
[L] OuterTailClass.finite_normal_form proves that every member has one of those four partitions, rho=4,5,6, and ordered labels 0≤L0≤L1≤L2≤3; these are finite discrete roles inside this family, not exhaustion of all admissible arrangements or existence of arbitrary native gap indices.
[L] outerLap_into_outerTail embeds the preceding outer-return class with L=[ell,kappa,rho−4]; outerLapCovered_into_outerTailCovered proves preservation of its entire earlier union, allowing the common family to replace the special case in the root catalogue.
[L] OuterTailMove proves the same actual runner6→7 handoff across all four partitions, including entries with additional captured competitors, from the directly derived native exit at Q.
[T 400+400] outer_lap_map_v3 retains 18 qualified endpoint exits across rho=4,5,6, 12 lower opening equalities, 3 cut equalities, 32 unqualified endpoint controls and 15310 invalid native assignments; all 33 prior runner6 return controls satisfy the corrected rule and isolate after the actual outer handoff.
[T 1600+1600] outer_lap_partitions_v1 transfers the original extreme gap-lap assignments through every physical partition and retains the unqualified shapes rather than assuming the old singleton-prefix parameters suffice.
[T 2112+2112] outer_lap_partitions_v2 uses balanced native gap-lap assignments and finds 29,22,25,27 qualified endpoint instances in the four respective partitions, with all eight assigned witnesses checked; all 264 native input assignments were separately verified exactly.
[T 103+103] outer_tail_handoff_v1 verifies one actual runner6→7 move to isolation on every qualified balanced instance and reflection; relative runner6 laps are 3 (32 cases),4 (32),5 (39), with 16 entries containing other captured competitors.
[T 65+65] outer_tail_residual_v1 retains all unresolved original prefix resumptions inside the proved packet faces, with 30 distinct finite control words; 96 other endpoint controls lie outside those packet faces, and re-entry to the next native comparison fails in all tested residuals.
[P; T 45/65] outer_packet_retention_v1 tests displacement from Q to the first left-cut opening P: D(P−Q)≤3/4 and D(P−Q)+3(1−tau_P)≤3/4 retain the original AP packet 4..7 in 45 cases and explain 33 one-move exits when the three original left cuts clear; this retention lemma is the next Lean target.
[L] FullAuditV13 PASS: 695 theorem reports across 188 modules, permitted standard axioms only, all source hashes match; compared with V12 only the catalogue changed among the prior 179 modules, with 9 new modules and 30 new theorem reports.
[OBS] New outer-return experiment sources passed AST checks for float literals and float calls; numerical operations use exact Fraction arithmetic and the previously inspected original cascade helper.
[OWED] Native packet retention under a displaced left opening, the remaining prefix continuations, broader partitions and exhaustive classification remain open; the finite roles above do not prove full n=8.
