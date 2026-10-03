# Cascade findings index, v2 (DRAFT, 2026-10-04; supersedes v1, which is kept unchanged)

One line per log entry in `RUNNING_LOG_order8_v1.md`, E323 onward; earlier work in `CASCADE_ACCOUNT_v1.md`. Grades: [LEAN] axiom-clean theorem; [PROVED] derivation checked exactly; [TESTED n/N] exact, n violations of N; [TREE] float-LP tree (1e-9 slack) with exact members, not certificates; [OBS] observed in a list or search, not derived. **RETRACTED / CORRECTED / SUPERSEDED** marks a statement withdrawn later. "Leaf-only" = counted over the stored terminal cells before the E347 fix: lower bounds for sets, upper bounds for infima, not frequencies. Add new lines at the end; do not edit old lines (append a correction line instead).

Objects: readings rho_1 = 1 < ... < rho_7; zones ((8j-1)/rho, (8j+1)/rho); start R = 1; landing R* = first unblocked R; lonely windows = closed intervals of unblocked R.

## Before E323 (see the account)
Hop = birth/death of a lonely window; effective-crossing rule; inert readings; lap compression fails; window trees (rho_7 <= 9, 17, 25) with supremum 26433/2209 = 11.966 at a closure vertex, never attained [TREE: float LP, evaluated at every node]; Lean: ZoneLinkN link rule, IntegerGridN, SegmentWindowN, ClassDeviationN, IntegerDisplacementN.

## Log lines
- E323 One-lap path words: 6,705 distinct, not Markov in the last letter. [TREE, leaf-only]
- E324 Three-lap tree: sup unchanged. The late-state dictionary uses marginal ranges (an over-estimate, E352); its 24.40 entry for T = 9 was later matched by an exact crosser (X24, E354).
- E325 Taxonomy of 14 classes on 52,000 samples; landing = least unblocked R >= 1 [TESTED 0/72,000]; K2a empty [PROVED]; exit-tie rule (smallest entry, then highest rank).
- E326 Setter = largest exit [TESTED 0/152,170]; next state depends on previous zone only [TESTED 0/80,000]; link-rule clauses [TESTED 0/136,199]. Sampler-reach statements (rank 1 inert, longest path 12) **RETRACTED**: rank 1 sets, 28-move paths exist.
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
- E343 Extremal window straddles 12; vertex pins 9 rho_5 = 15 rho_3 = 47 (leaf-list statistics; the vertex facts are exact).
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
- E354 **X24: exact gate crosser with rho_7 = 24.38**; gate crossing iff every component of K6 (clear set of readings 1..6 on [1,7]) lies in one open zone of reading 7 [PROVED (follows from the definitions); checked on X24 and on all 319,807 members in E362]; ceiling open.
- E355 Whole lonely set never empty in all tested [OBS]; lattice windows mirror-symmetric about 4m [TESTED]; "no {1,7}+{3,5} window" **RETRACTED** (E359).
- E356 Run state: J=3 paused/resumed; foreign Lean process noted (Lean is on hold, E222).
- E357 J=2 complete regions (293,333): 66 lap-free classes, 38 pairs, same as J=1 (members, lower bounds); lattices s = 1, 2, 3 enumerated exhaustively over a_7 <= 40, 44, 45 (rho_7 <= 40, 22, 15): 37 pairs, max landing 49/13, 33/7, 17/3, none above 7; path words keep growing.
- E358 Six-reading cell bound is the record's R8; **bound L >= 2/(7 rho_6) RETRACTED** (E359).
- E359 Counterexample tuple (1, 6559/2279, 26236/6779, 231/47, 26236/4115, 7): L = 135/3748 < 2/49; pins at heights 1, 7, 9 [PROVED from P1 (every tight row has at most two nonzero entries; P1 checked on 7,003 fine cells)]; single-point windows classified; pair-law rule (window holds both classes iff it contains [x, x+2]; forces rho_7 < 3) is a derivation with 0 mismatches in about 120,000 sets and no second-opinion pass.
- E360 Run state; keep-awake (app hold + caffeinate on the tree).
- E361 Cascade = min of the intersection of seven periodic sets; carving K_1 > ... > K_7 (order-independent final set).
- E362 Window-count profiles do not stabilise (43,635); the crossers' K6 prefix profiles did in one step (117 in J=1; 75 of a J=2 sample inside them): a sample, J=3 not yet tested.

## Open
Why R* < 12 (absolute ceiling of rho_7, rho_6 for crossers; per-cell ceilings are anchor x lap-ratio products, no bound on the product; why the maximisers' anchor is rank 5 or 6); infimum of the six-reading ratio (0.8825 found, rho_6 = 7); phase-2 word rule; K6 positive floor on a bounded box (would give a finite catalogue of crossers modulo d_max); exact (non-float) cell feasibility; complete J=3 with stop regions.

## Run state (2026-10-04)
Complete J=3 tree (`path_tree_par7.py 3 3 8`) in progress; its region near rho_7 = 24.4 tests the stop-region fix. Memory: `project_n8_cascade_map_2026_10_03.md`, `feedback_n8_exact_not_float_2026_10_03.md`.
