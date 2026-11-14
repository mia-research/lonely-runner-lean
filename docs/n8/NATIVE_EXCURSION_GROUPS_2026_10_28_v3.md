Rules: 1–4, 8–20.
# Native excursion groups and setter reduction — 2026-10-28, v3

[L] Entry excursion X_i=s_i E−d r_i, with d the selected disparity, E=N+1/8−dR and r_i=K_i+7/8−s_iR, equals d(s_iT−K_i−7/8) at the forced opening T.
[L] Exact independent label advance a_i is characterized by d(a_i−1)<X_i≤d a_i, with all natural a_i unbounded and original K_i=label(s_iR).
[L] Given that advance, capture is exactly X_i<d(a_i−3/4), and clearance is exactly d(a_i−3/4)≤X_i; combining with the entry band retains both closed recovery faces and strict captures.
[L] This proves the displacement split for multiple simultaneous returned disparities, including recovered members interleaved with captured members; no one-cut recovery pattern is imposed.
[L] If the captured parts of these independent bands leave one disparity group, that group forces its next actual opening even when several other disparities have returned and recovered.
[L] Remaining clear readings' native retained quarter faces then join the old relative-capture family; the number of returned disparities need not be one, and all physical clearance obligations remain.
[L] The general simultaneous-capture order uses residual D_i=d(a_i−3/4)−X_i; D_i=d(label(s_iT)+1/8−s_iT), so D_i>0 exactly for capture.
[L] Comparing s_g D_i≤s_i D_g over all positive residuals is exactly the actual maximum-opening order atT; a positive-residual g satisfying these comparisons forces the next move, preserving all ties.
[L] Captured ratios s_i≤3s_g and retained quarter faces for nonpositive residuals derive the next relative-entry family; this is a sufficient conditional entry family, not proof the inequalities always hold.
[L] Single surviving-disparity relay inputs embed into the general residual-order relay family; these are overlapping representations, not disjoint additional types.
[L] Setter dominance is independent of these sufficient faces: if captured i is faster than captured j but its current integer label is no larger, i's opening is strictly earlier and i cannot set the next move.
[L] Therefore a selected faster survivor must have a strictly larger label than every slower survivor; candidates outside this label-record frontier can be removed from opening selection, while retaining them in all physical clearance tests.
[L] If the surviving label-record frontier has one disparity, its actual handoff is forced without supplying every opening comparison; adding the existing first-closing quarter face joins the old quarter family.
[L] The selected label record is also forced in original-entry coordinates: for every slower captured j, K_j+a_j<K_g+a_g, deriving the ordering constraint directly from independent excursion bands and actual residual selection.
[T 137597/137597] Complete stored handoffs retain all116834 continuing relays; excursion bands reproduce every advance/capture and12195 all-recovered exits,78644 single-surviving-disparity exits and25995 multiple-surviving-disparity exits.
[T] Among single-survivor exits,9188 have several returned disparities;2838 satisfy next retained quarter inputs, including566 such multi-return cases; other continuing exceptions remain in the controls.
[T] General residual order reproduces every stored actual successor and all55 tied successor groups;4091 next relative-entry inputs pass, including1253 with several surviving disparities.
[T 3452/3452] All admissible new physical histories replay exactly, including12248 relays;541 pass the residual-relative input,58 with multiple surviving disparities, while483 single-survivor inputs include18 with several returned disparities.
[T] Complete dominance controls include137597 original handoffs and12248 new physical-history handoffs, checking189420 physical survivor-candidate uses and removing3721 dominated candidates across3492 handoffs without changing any actual setter or tied opening.
[T] Unique-frontier quarter inputs occur9245 times in original stored controls, including863 with several surviving disparities; new deformation histories add499 inputs, including4 with several surviving disparities; these overlap existing quarter isolations.
[T] The complete frontier diagnostic retains examples where the winner is the second, third, fourth or fifth distinct disparity on the frontier; neither its slowest nor fastest member is assumed to win.
[T] All100 recorded simultaneous-setter groups across the original and new-history controls satisfy their exact common residue-one representation s_i=h(8L_i+1), h=1/(8T), at the shared opening; this is local point evidence and does not assert a complete residue-grid arrangement.
[EXACT] native_excursion_exactness_v3 passes eight source/result pairs with source hashes and inherited exactness links; every computation is Fraction/Lean real arithmetic, and old float-LP regions remain uncertified.
[SCOPE] Excursion/ordering equivalences expose exact native structure and dominance removes setter candidates; occurrence of sufficient next-entry faces for every admissible arrangement and full n=8 remain open.
[NEXT] Analyze the remaining multi-disparity label-record frontier using its ordered lower-opening residuals, distinguishing actual opening ties from merely equal labels; no count of observed frontier sizes is a global bound or arrangement exhaustion proof.
[FILES] Lean:NativeReturnExcursion,NativeExcursionArrangement,NativeExcursionOpeningOrder,NativeSurvivorDominance; controls:native_excursion_groups_v1/v2/v3,native_excursion_physical_histories_v1/v2,native_survivor_dominance_v1/v2/v3.
[PROVISIONAL: counting tool] Inherited grid/ceiling opening selectors; [PROVISIONAL: covering] inherited finite parameter joins; new ceilings coordinate given states and introduce no density argument.
