Rules: 1–4, 8–20.
# Four-block packet exits — 2026-10-27, v1

[NOTATION] Unit physical block step; T=m+1/8,S=g+h+j,R=1/2+ST−a−b−e,N=4m+a+b+e,D=4+S,P_s=(N−sm+9/8)/(D−s),Z=(N+17/8)/D,L=(a+b+e+9/8)/S; all data exact and native gap laps explicit.
[L] UnitAPPacketPhase.phase_at_anchor proves one AP-packet phase identity for any named physical opening runner and return lap: readingi atP hasphaseq+1/8+(i−anchor)(uP−m), under explicit unit-step and integer-lap identities.
[L] FourBlockLongTailArrangement.LongTailClass proves all8subjects for p,q,r≥1,p+q+r≤4 under native bands andS+8R≤9, removing the earlier left singleton guard; retained actual setters7→6→5 lead to the closed third exit.
[L] FourBlockLongTailExit proves the strict complementS+8R>9 forces the next original setter4, keeping allseven readings; the exception is an actual continued branch.
[L] FourBlockFourthArrangement.FourthClass proves all8subjects for1+1+1+5 with5S+24R≤31,5≤S+4R and9<S+8R; its actual native setter sequence7→6→5→4 isolates atP_3.
[L] FourBlockOuterReturnArrangement.OuterReturnClass proves all8subjects for1+1+1+5 with3S+16R≤22,31<5S+24R,R>7/8; its actual native sequence7→6→5→4→7 isolates atZ.
[L] FourBlockOuterReturnBounds.closed_join provesZ=P_3 exactly when the supplied shared face5S+24R=31 holds; the two native mechanisms meet at the same opening.
[L] FourBlockInnerArrangement.InnerExitClass proves all8subjects for1+1+1+5 withS≤3,5S+24R≤39,13≤2S+8R,jL−e≥1/4,R>7/8; allseven original readings are proved clear atL without assuming isolation.
[L] InnerExit.earlier_faces derives31<5S+24R and22<3S+16R from its input faces, distinguishing its native parameter region from the previous return-exit region; no exclusion from every other existential catalogue representation is claimed.
[L] The inner anchor phase proof consumes the generic UnitAPPacketPhase identity; its full six-setter reference trace is tested but not yet formalized end-to-end.
[L] Every new all-subject class retains positive/injective physical inputs, arbitrary signed affine scale/common drift and subject relabels; no physical runner is made stationary.
[L] ArrangementTypesOct26 now consumes InnerCoveredClass, whose nested unions retain the earlier FourBlockClass plus all four new exit families; its20top-level ORbranches are overlapping sufficient families, not20disjoint/exhaustive mathematical types.
[T576/576] Stored long-tail controls retain144initial-grid exits,168third-opening exits and264forced fourth continuations across both endpoint orientations.
[T1152+1152] Independent third-face original/mirror subject controls retain48exact endpoint exit equalities and48strict fourth-continuation controls.
[T720+720] Fourth-opening controls retain60clear/30captured endpoint cases,9lower/21upper equalities and18strictly beyond the earlier third exit;24invalid native parameter rows are explicit.
[T720+720] Outer-return controls retain42actual returned-endpoint exits,28without the earlier left input guard,12lower/18shared upper equalities and30negative captured controls;36invalid native rows are explicit.
[T840+840] Inner-anchor map retains10qualified six-setter reference exits with60internal and10opposite-endpoint checks;25invalid native rows and95unqualified endpoint rows are explicit.
[T288+288] Independent inner-cut controls retain24exits,12exact cut equalities,4double closed faces and12strict cases captured by original reading2;6invalid residual parameter rows are explicit.
[OBS] All new experiment paths use Fraction arithmetic; pre-run AST audits found only Fraction-based divisions and no float literals/calls on used paths.
[OWED] The inner-anchor six-setter trace, its strict cut continuation and broader packet returns remain native continuation targets; fulln8 and exhaustive finite residual classification remain open.
