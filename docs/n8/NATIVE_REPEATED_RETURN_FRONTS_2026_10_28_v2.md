Rules: 1–4, 8–20.
# Native repeated-return fronts — 2026-10-28, v2

[L] The fast-captured versus previously-recovered first-closer split is now proved in Lean, rather than only observed in stored points.
[L] For an actual P→R and selected surviving c, write T=(N+1/8)/s_c, N=label(s_c R), K_i=label(s_i R), E=N+1/8−s_c R and r_i=K_i+7/8−s_i R; E lies strictly between0 and1/4 by the native capture faces.
[L] Return level m means a canonical integer-window label advance; it is not a count of actual moves or necessarily completed physical revolutions.
[L] Exact unbounded level law: advance(s_i,R,T)≥m iff s_c(r_i+m−1)<s_i E, for every integer m≥1; no advance index or number of moves is capped.
[L] A captured reading has r_i>3/4, so reaching level m forces s_i>(4m−1)s_c; in particular a captured repeater exceeds3s_c, and one with s_i≤7s_c advances exactly one label.
[L] A clear/carried reading has0≤r_i≤3/4 and repeats precisely when s_c r_i<s_i E; its first repeat needs no nontrivial disparity-ratio floor, because it may already be at its closing face.
[L] The generic carried-window consequence is s_i>4(m−1)s_c for level m, valid also for captured readings but weaker there; this is a local phase law, not a global time or move bound.
[L] If the selected entry P is nonnegative, every positive returned label is at least1; hence N≥1 in the joint-label laws below.
[L] Captured joint-label law: 2K_i>(8m−2)N−m; one label advance gives K_i≥3N and at least two give K_i≥7N, retaining N,K_i,m as unbounded integer parameters.
[L] Generic carried joint-label law: 8K_i>32(m−1)N−4m−3; at least two label advances give K_i≥4N−1, explaining a different native label arrangement from the captured branch.
[L] Failure of a group's exact sharp face forces its first current closer g to advance again; if captured at R it satisfies the fast ratio, otherwise it occupies the closed retained band and carries both positive old and new advances.
[L] The two-prefix rule is now a named Lean theorem: a new return is either an old positive returner crossing its CURRENT closing at R, or an old nonreturner crossing its retained ORIGINAL closing at P.
[L] RepeatedSingleEntry supplies the two prefix inequalities that leave only the repeated disparity s_g; it is equivalent to a single returned-disparity successor together with a positive old advance for g.
[L] That entry forces a dichotomy: g's group recovers and T isolates, or it is the only captured disparity group and forces its displaced opening U; physical equal-disparity competitors remain named and distinct.
[L] Repeated recovery and repeated relay with original-boundary fit embed into the existing single-return families; a broader repeated relay with recovered positive returns joins the existing HandoffRecoveredClass.
[L] Repeated relay with no new advances embeds into the broader recovered-relay family; three new catalogue bridges preserve the21 overlapping top-level alternatives.
[T 137597/137597] Complete stored handoffs retained, including116834 actual continuing relays; all1643673 critical-level comparisons agree with exact phase crossing, with no finite test claimed to exhaust all m.
[T] All3161 captured repeated-reading uses satisfy the strongest observed native ratio and joint-label rung;2586 in the first disparity band have exactly one advance;164448 positive-reading uses satisfy the generic carried ratio/label law.
[T 8165/8165] Every failed returned-group first closer satisfies the proved split:1941 fast captured cases and6224 previously recovered cases; current and new capture roles remain separate.
[T] The new repeated-single entry occurs1786 times:71 fast-captured and1715 previously-recovered;130 recover at T and1656 force another handoff.
[T] Of those1656 handoffs,635 satisfy original-boundary fit and6 more isolate with recovered positive returns;1015 continue, retained explicitly rather than inferred away by the new laws.
[T 3452/3452] Every admissible new physical deformation history is replayed in full;12248 actual relays and171690 critical-level checks pass, including24 captured-rung and11702 generic carried-rung reading checks.
[T] These new physical histories contain105 repeated-group failures (21 fast-captured,84 previously-recovered),27 repeated-single entries and6 next-fit isolation-family inputs; the other21 next relays remain explicit continuing/other inputs.
[EXACT] native_repeated_return_exactness_v1 passes eight script/result pairs, source hashes and inherited exact-state links; every calculation is Fraction/Lean real arithmetic and all physical speeds stay positive/distinct.
[SCOPE] These are native necessary constraints, exact local equivalences and conditional isolation-family joins; the disparity or label inequalities alone are not sufficient for isolation, and full n=8 remains open.
[NEXT] Follow multiple simultaneous repeated disparities: the fast branch increases disparity and its capture-label rung, while the carried branch is governed by its actual remaining closing gap; do not turn these local facts into a descending-group or move-budget argument.
[FILES] Lean:NativeRepeatedReturn.lean,NativeRepeatedReturnArrangement.lean,NativeRepeatedReturnLabels.lean; complete controls:native_repeated_return_front_v4.py/.json and native_repeated_return_deformations_v4.py/.json; earlier versions retained unchanged.
[PROVISIONAL: counting tool] Inherited grid/ceiling opening selectors; [PROVISIONAL: covering] inherited finite parameter joins; new ceilings label given states and introduce no density/coverage method.
