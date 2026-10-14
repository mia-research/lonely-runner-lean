# Cascade findings index, v5 (DRAFT, 2026-10-04; supersedes v4, v3, v2 and v1, kept unchanged)

One line per log entry in `RUNNING_LOG_order8_v1.md`, E269 onward (v1 and v2 started at E323; E269-E322 were read in full on 2026-10-04 for this version). Earlier work: `CASCADE_ACCOUNT_v1.md`, `MECHANISM_MAP_v4.md`. Grades: [LEAN] axiom-clean theorem; [PROVED] derivation checked exactly; [TESTED n/N] exact, n violations of N; [VERIFIED] the log's own word for an exact check; [reasoned] derived by hand, not checked; [TREE] float-LP tree (1e-9 slack) with exact members, not certificates; [OBS] observed in a list or search, not derived. **RETRACTED / CORRECTED / SUPERSEDED / WITHDRAWN** marks a statement withdrawn later. "Leaf-only" = counted over the stored terminal cells before the E347 fix: lower bounds for sets, upper bounds for infima, not frequencies. Add new lines at the end; do not edit old lines (append a correction line instead).

Objects: readings rho_1 = 1 < ... < rho_7; zones ((8j-1)/rho, (8j+1)/rho); start R = 1; landing R* = first unblocked R; lonely windows = closed intervals of unblocked R.

## E269-E322 (owner-directed mapping before this session's tree and agent work)
- E269 Map v4 cut and compile-diffed; the cascade's mechanics need no cover (the C1-shape's case: excluding a joint cover is its statement); "covering" as a question's object has been an imported shape (Q7 withdrawn, E215).
- E270 Owner: the finite cover. `Cover8 M` (Lean `RegimeSkeletonN.lonelyRunnerAt8_of_cover8`) is the one owed statement; `ArrangementShapeN.reduction_iff` (stated in Lean in an untracked file, read in the log; build and axioms not rechecked here): any arrangement is an affine rescaling of one ordered shape 0 = x_0 < ... < x_7 = 7 (six free values). `1..7, 17` and `1..7, 10^10` fall in different proved cases (the latter closed by R8, `blockRule8_one`). E269's reply that the record had no finite-list statement **CORRECTED** (Cover8 is it).
- E271 Design of the finite cover for approval (`FINITE_COVER_DESIGN_v1.md`); E145's types defined by the landing make finiteness hold by construction and "every arrangement has a type" the conjecture ([reasoned] there).
- E272 Owner: start from the conditions (`ARRANGEMENT_CONDITIONS_v1.md`, [reasoned]): a reading against a scale is free, locked or between; types finite by the reasoning; the drift quantity |eps|L is not shown finite. **CORRECTED in E274** (the regime split with an open middle is bookkeeping; `ARRANGEMENT_CONDITIONS_v2.md`, v1 retained).
- E273-E274 About 22,000 arrangements in six families (74 cells of 300): moves <= 13, R* <= 5.02, no rise with laps, deviation or scale ratio; the drift quantity is a coordinate, not a requirement (E272 corrected); the generators lie mostly outside `EightResidual` (the same sampler reach that E326 later retracts as a claim about the cascade). E273's landing-lap design **flawed** (K grows with the scale ratio by definition).
- E275 Owner: the deformation from the AP is the route; the multi-pinch defined (two or more readings on one edge at a pinch); a literature search launched.
- E276 Literature: a published computer-assisted proof of eight runners exists (Rosenfeld, arXiv:2509.14111; Trakulthongchai for nine, ten); no reduction by deformation found; recorded as data, not adopted.
- E277 First-order multi-pinch criterion derived: the window is non-empty after the pinch iff min over leaving readings of u >= max over entering readings of u (u = e_i/d_i).
- E278 Tao's reduction translated to native objects, as reported by a subagent (only the abstract was checked; the proof was not read) (orders 3-7, R8, TrainCollapseN, SplitChainN); the E278 dichotomy and its evenness branch **WITHDRAWN** (E279).
- E279 Owner: no evenness needed, only that any arrangement can be locally arranged in an AP/grid style. Local types (residue, sign per reading, class) finite, no height bound, "the lap never enters" [reasoned; **CORRECTED** by E302/E303/E311: beyond lap 0 the carry-in is scaled by the lap count 8k, not by the class]; the work is the carrying rule across walls.
- E280 Multi-pinches read: the criterion agrees with the exact test at the non-tied events (0 mismatches in 922 + 270; 6 tied events per case are not decided by first order); interleaving common (147 of 232, 13 of 69) but every such event has a margin window (0 of 147, 0 of 13 without); statement (T) (tight arrangements have only simple pinches) owed, [VERIFIED] readings <= 24 (E113).
- E281 Owner: not the conjecture itself; existence may not be necessary; do walls and hand-off belong? E279's closing bullets **WITHDRAWN**.
- E282-E283 Local-type test on 28,056 arrangements: the sign-and-residue type decides loneliness at the bound and, for one bad reading, names the first setter; it does not fix the landing rank or the move count; 0 of 5,978 residual members are lonely at the bound.
- E284 Owner: mover/exit and "bad reading" are proxies; E283's closing paragraph **WITHDRAWN**.
- E285-E286 The complete grid's named instant stays lonely out to q = 61.7, about 120 times the proved radius 0.5 (exact loneliness, 0 failures in 12,000 grids); the landing is almost always earlier than it.
- E287 Owner: the failure was the proxy's; the first isolation is not needed; E286's comparison columns **WITHDRAWN**.
- E288-E289 Owner: the movement of the isolation point as the proof; isolation binds only the two neighbours; the 14-formula test dropped; E288's "must not run off" **WITHDRAWN**.
- E290 Crosswalk: `DeformationN`/`PathWindowN` already state the owner's argument in Lean; one hypothesis (`WindowBound`).
- E291 Owner: ask "is it needed by the argument" of everything.
- E292-E295 Lean reading; E292's "the missing statement is the grid-selection rule", E293's "which is the conjecture itself" for the owner's route and "no argument on disk", and E290's "Not in Lean" section **WITHDRAWN** after reading seven modules in full and parts of others (E293, E294, E295; ten modules still unread at E294); one hypothesis `WindowBound` remains.
- E296 `SegmentWindowN` [LEAN]; the one-mover window fails to be uniform at lattice points (T ~ P/(4a)); E295's coalescence claim **WITHDRAWN**.
- E297 Integer grid D = 1 and its 2-adic refinement; no lonely instant on the 2-adic grid for 6.1% (exhaustive N = 20); the examined ones are lonely elsewhere (checked in the 25 printed cases); "rule not obtained" **WITHDRAWN for the displacement** in E299 (the 2-adic counts dropped as not needed).
- E298 `IntegerGridN` [LEAN]. E299 `IntegerDisplacementN` [LEAN] (`lonely_of_displacement`). E300 cascade move at the grid instant coded [LEAN]. E301 second move and composition already exist; the D = 1 grid is the cascade's start only when d_min = 1 (**CORRECTION** of E297/E299).
- E302 Certificate (b, k) in deviation form [reasoned]. The fastest reading V against the lonely set F of the six slower readings: V's blocked set is open arcs of length 1/(4V), period 1/V; a component of F of length >= 1/(4V) is not inside one arc. **This is the K6 argument that E354 (R1) and E358 (R8) later re-derived.**
- E303 Cascade anatomy on one residual set (1,2,3,5,7,12,16); its tag "residual" **WITHDRAWN** (E304).
- E304 Existing residual material found and reused; E303 used a partial field set (the current `EightResidual` has 22 fields; no 7-subset of [1,40] is in it).
- E305 Anatomy on the real members: in the members shown (B1 #0, 1, 3, 5, 7 and C1 #0, 1, 2; not a survey): B1 (fastest reading in (7,9)) are lap-1 staircases of the upper block (one ends at lap 2), C1 land in one move at lap 6-11; the landing's setter is at position exactly 1.000; E311 over all members: C1 1-7 moves, last setter laps 4-46.
- E306 The AP has exactly four lonely instants per period, all isolated points (R = 1, 3, 5, 7) [VERIFIED]; complete grids (laps < 4) lonely at the four in 16,384/16,384.
- E307 `ClassDeviationN` [LEAN]; a class instant `a` is blocked by a lapped fastest reading exactly when |a(rho_7 - 8)| < 1; R = 1 is destroyed for rho_7 in (7, 9).
- E308 Each AP event is a tangency of two zones; the first event is not always kept (thresholds near 51/7 and 54/7); presentation rule: give speeds.
- E309-E310 The frozen runners' lonely set is unchanged when others move; the landing lies in a component of it (90 runs); with three or four movers no step has an empty lonely set in (0, 9.5] (0 of 4,898, a measurement).
- E311 Cascade paths under deformation: carried blockers; no-move paths 1,577 of 1,860 (one deformed runner); at moves 2 and 3 of the single-mover runs every setter is frozen (210 of 210). (The handover records an earlier claim that hops land on frozen edges as withdrawn; E313 states that hops do not go to frozen edges only.)
- E312 Effective-crossing rule [VERIFIED 598/600 + 2 unobservable, locality 170/170], five crossing types; scope exception X6 (E317): a predicted crossing that was a touch at the coincidence rho_6 = 9 rho_1.
- E313 A hop is the birth or death of a lonely window [VERIFIED 1,716/1,716, 0 exceptions]; two zones of consecutive readings chain only if y/x <= (8j+1)/(8j-1).
- E314 AP pair map: a cross of strips rho in (7, 9) + 8Z; plateaus and bands.
- E315 Categories by result: 6,347 arrangements, 719 distinct paths; link data on 2,717 consecutive setters [VERIFIED] (never rank up with lap <= 0, never the same rank, never rank down with a higher lap).
- E316 Grids with extra laps; three deformed runners; inert readings [VERIFIED 61,752 replacements]; the one-runner catalogue is not a predictor for three movers (landing equal in 229 of 983, lower in 625, higher in 129).
- E317 Autonomous run: symbolic cells, extremes found by search and evaluated in exact arithmetic (lower bounds: 28 moves, R* about 11.95 in the one-lap window), cluster window (adversarial sup q found; W6 tested, not proved), exceptions X1-X8; float artefact ("401 moves") removed.
- E318 Why R about 12: the landing is the left end of a component that contains R = 12 in the two best arrangements; the first surviving class event is even (12 or 14); R* <= 12 not derived. **Re-observed as E343.**
- E319 One-lap window tree: finite, 27,517 nodes; supremum 26433/2209 = 11.966 [TREE].
- E320 Two-lap window tree (343,070 nodes, same supremum) [TREE]; lap compression fails (4,922 of 31,585).
- E321 The extremal vertex is tangent to d_min's second window edges (9 and 15), 47 = 8*6 - 1.
- E322 Threshold sensitivity (1e-6, 1e-9, 1e-12) identical [CHECKED]; a cell thinner than 1e-12 would be missed by all three (exact certificates owed).

## E323-E362 (this session's tree, agent and consolidation work)
- E323 One-lap path words: 6,705 distinct, not Markov in the last letter. [TREE, leaf-only]
- E324 Three-lap tree: sup unchanged. The late-state dictionary uses marginal ranges (an over-estimate, E352); its 24.40 entry for T = 9 was later matched by an exact crosser (X24, E354).
- E325 Taxonomy of 14 classes on 52,000 samples; landing = least unblocked R >= 1 [TESTED 0/72,000]; K2a empty [PROVED]; exit-tie rule (smallest entry, then highest rank).
- E326 Setter = largest exit [TESTED 0/152,170]; next state depends on previous zone only [TESTED 0/80,000]; link-rule clauses [TESTED 0/136,199] (E315 had the link data on 2,717 links). Sampler-reach statements (rank 1 inert, longest path 12) **RETRACTED**: rank 1 sets, 28-move paths exist.
- E327 A reading's change preserves the state sequence when it and its image are clear at every visited state (sufficient: 21,781/21,781); every failure found had a blocking reading (not shown necessary); look-alike families exist.
- E328 Taxonomy on tree cells (99.8% two-or-more moves, opener lap >= 2): leaf-only, **SUPERSEDED** (E348).
- E329 Readings sit just past their exit edge at the landing (12,897 vs 1,066): one member per cell, leaf-only, a witness-choice statistic (E341).
- E330 59 J=2 members land above 7 with rho_7 > 9 (to 16.19): **corrects** "none above 9" (existence stands; counts leaf-only).
- E331 Step-0 law [TESTED 0/20,000]; LP witnesses disagree with the exact cascade in 2,939 of 9,652 cells; ZoneLink axioms checked.
- E332 Transition types (direction, lap change) grow with the window; per-lap rank sequences strictly decreasing [TESTED 0/372,642]; owner: patterns to rules to mechanisms; d_min/d_max cover the continuous values.
- E333 K2s1 empty [PROVED]; closer = opener's own reading only for rank 7 [PROVED, TESTED 1,593/1,593].
- E334 Staircase: distinct first k+1 setters => rho_{7-k} > 7(7/9)^k [PROVED]; infima 735/289, 3381/2125, ... over members: leaf-only, float-LP vertices (upper bounds on the true infima).
- E335 Lap-free pairs with four unfound: **SUPERSEDED** (E347 finds all four).
- E336 Owner: the pair categories were this session's theory, not the cascade's; use clever tests.
- E337 Floating point/slack in agents and in the tree; exact-only rule; tree cell lists are float-LP.
- E338 AST float audit: the cascade code is exact on Fraction input; the tree and agent libraries use floats.
- E339 Two simple reducibility forms tested and not supported (opener lap lowering keeps the states in 6 of 9,197 members, leaf-only; one common grid spacing, an exploratory float count); the cluster-scale form and lowering of other readings were not tested.
- E340 **d_min gate** [PROVED, TESTED 110,081/110,081 leaf members]: landing > 7 iff reading 1 sets a move (lap 1, from a state in (7,9)) iff a state equals 9; no landing in (7,9); two phases. The agent's float correlations, k-means and "nothing between 6.785 and 7" were withdrawn there.
- E341 R* atoms are a witness artefact (one LP point per cell); member-list statistics (E329, E340) describe the member list.
- E342 Phase rotation p(R+8) = p(R) + 8 frac(rho); mirror symmetry about 4m when m rho_y is an integer [TESTED 0/12,000 per m]; integer arrangements: sample maximum landing 3.769 (66,000), none above 7.
- E343 Extremal window straddles 12 (re-observation of E318); vertex pins 9 rho_5 = 15 rho_3 = 47 (leaf-list statistics; the vertex facts are exact).
- E344 Extremal cell: six tight "exit = entry" equalities; in-cell bound R* <= 9(8*11+1)(8*4+1)/(8*6-1)^2 = 26433/2209 [exact, Farkas certificates]; 1,485 cells, nothing above.
- E345 Opener's earlier blocking state and lap-ratio bound: 4,931 of 4,939 members (8 have opener d_min); leaf-only.
- E346 The 8 leaf members landing at 9 form one narrow family (rho_7 in [7.3633, 7.3645]); **CORRECTED by E347**: other arrangements with opener d_min and landing 9 exist outside it ((1,6) with rho_7 = 7.26, (1,7) with rho_7 = 7.873); phase 2 has 0-9 moves in the leaf list.
- E347 **CORRECTION: stored terminal cells were leaves only** (98% of sampled arrangements land at an internal node); all four pairs occur (43 of 49; six diagonals impossible).
- E348 J=1 on all outcome regions: 19,679 regions, 46 openers, 66 lap-free classes, 38 pairs (members); erratum: the J=1 leaf-coverage figure 502 had not been measured.
- E349 Old-code J=3 finished: sup 26433/2209 unchanged [TREE] (the supremum is taken at every node).
- E350 Inert quotient, rank reflection and lap shift do not collapse the J=1 regions (members).
- E351 Phase-2 words: 330 in J=1, no rule found beyond the maximum exit; removing the fastest reading removes the gate crossing in all 7,567 J=1 crossers [TESTED]; six-reading landings found stay near 3 [OBS, search values, W6 tested only].
- E352 3.6 million exact arrangements outside the windows: no violation of gate/closer/staircase found, no new outcome type found, nothing above 26433/2209 reached by the searches run. The "reach ceiling" **RETRACTED** (E354).
- E353 Line scans of the ceiling (rho_7 <= 16.19): **RETRACTED** (E354).
- E354 **X24: exact gate crosser with rho_7 = 24.38**; gate crossing iff every component of K6 (clear set of readings 1..6 on [1,7]) lies in one open zone of reading 7 [PROVED (follows from the definitions; the argument is E302's); checked on X24 and on all 319,807 members in E362]; ceiling open.
- E355 Whole lonely set never empty in all tested [OBS]; lattice windows mirror-symmetric about 4m [TESTED]; "no {1,7}+{3,5} window" **RETRACTED** (E359).
- E356 Run state: J=3 paused/resumed; foreign Lean process noted (Lean is on hold, E222).
- E357 J=2 complete regions (293,333): 66 lap-free classes, 38 pairs, same as J=1 (members, lower bounds); lattices s = 1, 2, 3 enumerated exhaustively over a_7 <= 40, 44, 45 (rho_7 <= 40, 22, 15): 37 pairs, max landing 49/13, 33/7, 17/3, none above 7; path words keep growing. (Same shape as E279/E283: finite coarse types, laps and magnitudes not fixed by them.)
- E358 Six-reading cell bound is the record's R8 (and E302); **bound L >= 2/(7 rho_6) RETRACTED** (E359).
- E359 Counterexample tuple (1, 6559/2279, 26236/6779, 231/47, 26236/4115, 7): L = 135/3748 < 2/49; pins at heights 1, 7, 9 [PROVED from P1 (every tight row has at most two nonzero entries; P1 checked on 7,003 fine cells)]; single-point windows classified; pair-law rule (window holds both classes iff it contains [x, x+2]; forces rho_7 < 3) is a derivation with 0 mismatches in about 120,000 sets and no second-opinion pass.
- E360 Run state; keep-awake (app hold + caffeinate on the tree).
- E361 Cascade = min of the intersection of seven periodic sets; carving K_1 > ... > K_7 (order-independent final set).
- E362 Window-count profiles do not stabilise (43,635); the crossers' K6 prefix profiles did in one step (117 in J=1; 75 of a J=2 sample inside them): a sample, J=3 not yet tested.

- E363 Owner asked whether later results were preferred over earlier ones: E269-E322 read in full; re-derivations found (E302 = E354 R1 / E358 R8; E318 = E343; E274 = E326's sampler reach; E279/E283 = E357/E362 shape).
- E364 Gate crossers: 115 distinct K6 templates over 16,152 tuples (stable in random order within these sources; non-crossers 179,727); top bound of rho_7 = rho_{y'}(8j+1)/(8j'-1) (a window's right-end label and a lap j of reading 7); X24 sup 129 rho_2/15 [exact].
- E365 Owner: "suprema, coverage or density in disguise?" Answer: an extremum of one coordinate is not a measure; closure values are limits not attained; state ceilings as zone coincidences and attained arrangements.
- E366 **Mechanism [PROVED, TESTED 12,078/12,078]:** every K6 window lies in exactly one zone of reading 7 and that zone is a move of the path before the gate; a crosser's path alternates between readings 2..6 and reading 7 at the K6 windows.
- E367 Templates of K_k by level, crossers vs non-crossers: 7, 29, 87, 137, 115 (k = 2..6) vs 23, 752, 5,618, 12,485, 15,193; adjacency closure delegated.
- E368 **Complete J=3** (stop regions included): 1,878,060 regions; gate-crossing regions 7,855 / 7,940 / 7,947 at J=1, 2, 3 (4,332 / 4,395 / 4,402 paths); new J=3 crossing paths all rho_7 in [23, 24.4]; X24 is in a leaf region (E354's "test of the stop-region fix" wording corrected).
- E369 **Outcome catalogue in the cascade's own objects** (opener, window A/B, region): 14 classes at J=1, 2, 3; window-B regions 7,854 / 7,939 / 7,946 with short opener-lap ranges per rank; window-A regions grow 15- and 6-fold.

## Open
Why R* < 12 (absolute ceiling of rho_7, rho_6 for crossers; per-cell ceilings are anchor x lap-ratio products, no bound on the product; why the maximisers' anchor is rank 5 or 6); infimum of the six-reading ratio (0.8825 found, rho_6 = 7); phase-2 word rule; K6 positive floor on a bounded box (would give a finite catalogue of crossers modulo d_max); exact (non-float) cell feasibility; further crossing islands beyond rho_7 = 25 (adjacency closure running); `Cover8 M` and `WindowBound` (Lean, E270, E295); statement (T) (E280); the tail-update rule and the Lean statements of the five crossing types (E312).

## Run state (2026-10-04)
Complete J=3 tree finished (E368); adjacency closure of the crossing regions running (agent). Memory: `project_n8_cascade_map_2026_10_03.md`, `feedback_n8_exact_not_float_2026_10_03.md`.
