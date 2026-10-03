# sigpair_decision_v1 -- (opener rank, closer rank) pairs of the window rho_7 <= 17

Grades: [EXACT-ARR] = exact Fraction arrangement, verified with `outcome()` (outcome_classes_v2.py); [EXACT-INF] = every node of an exhaustive decision tree excluded by an exact Farkas certificate (Fraction multipliers, verified in Fractions); [PROVED] = derived below; [COUNT]; [UNDECIDED].
Floats (HiGHS) only guess multipliers/points; nothing below rests on a float verdict.

## 1. Result for the four pairs  [EXACT-ARR]

All four pairs occur in the window rho_7 <= 17. Readings rho_1 = 1 < ... < rho_7, each verified by `outcome()` (opener (rank, lap), closer (rank, lap)); file `sigpair_nice_witnesses_v1.json`.

| pair | arrangement (rho_2..rho_7) | R* | opener | closer | width | moves |
|---|---|---|---|---|---|---|
| (1,6) | 73/25, 99/25, 253/50, 321/50, 697/100, 363/50 | 9 | (1,1) | (6,8) | 0.0387 | 20 |
| (1,7) | 3311/1000, 4607/1000, 5521/1000, 3173/500, 3639/500, 7873/1000 | 9 | (1,1) | (7,9) | 0.0182 | 23 |
| (2,1) | 367/100, 553/125, 1253/250, 5487/1000, 6217/1000, 7817/1000 | 2500/367 | (2,3) | (1,1) | 0.188 | 18 |
| (5,1) | 101/25, 129/25, 153/25, 36/5, 281/25, 659/50 | 245/36 | (5,6) | (1,1) | 0.194 | 25 |

Also exact: (1,2): 171/50, 119/25, 143/25, 13/2, 188/25, 204/25 (R* = 9, closer (2,4)); (1,3): 76/25, 211/50, 127/25, 583/100, 167/25, 29/4 (closer (3,5)).
More witnesses (7 for (1,6), 2 for (2,1), 8 for (5,1)) in `sigpair_witnesses_nodes_v1.pkl`, `sigpair_node_J2_o*_c*_*.jsonl`.

## 2. Why 480,000 random evaluations and the cell data did not show them  [EXACT-ARR, COUNT]

`terminals5_J2.pkl` records only tree nodes with no children (`if nchild == 0` in path_tree_par5.py). A node that has children AND a region where every reading is clear (the cascade lands there) loses that landing region: it is in no terminal cell. Evidence, exact: the arrangement of the earlier agent for (1,3) (`missing_pairs_search_s1.out`) has an 18-move path whose only terminal extension is cell 106704 (path + (2,3),(3,4)); no terminal cell has the arrangement's own path. Of the 175,463 distinct path-prefix nodes of the J2 terminals, 74,049 are terminal paths and 101,414 are internal. The witnesses for (1,2),(1,3),(1,6),(1,7),(2,1) have paths that are internal nodes (checked: path not in the terminal set, in the prefix set). The (5,1) witnesses have terminal paths (7 of 8): they lie inside the stored boxes of terminal cells (e.g. cells 52520, 52525, 52688, 52690) whose exact member has pair (5,6), so a cell holds several closers and the member pair is a lower bound. Consequence: member/cell-signature pair sets (34 of 49 here, `sigpair_members_J2_v1.out`) are lower bounds, and the signature-LP method of envl_* applied to terminal cells cannot see internal-node landings.

## 3. Method (what was actually run)

Object: for a path P (setter ranks and laps), region L(P) = {rho_1 = 1 < ... < rho_7 <= 17, cascade follows P and lands}. Exact rows: setter s_{k+1} blocked in lap j (open); each other reading y at state k is clear (closed gap [8l+1, 8l+7]) or blocked (open zone) with exit <= next state's R (strict against higher index, matching outcome()'s tie rule); final state all clear; closer rows (entry (8l+7)/rho_c <= every other entry, strict against lower rank). Decision tree over laps (reading by reading, state by state, fail-first order), each node excluded by an exact Farkas certificate or expanded; a leaf yields an exact interior point (rational projection onto pinned equalities when needed) re-verified by `outcome()`. Verdict FEAS (exact arrangement) / INF (all nodes certified) / BUDGET (pass 2 with an exactly certified relaxation box). Files: sigpair_lib_v1.py, sigpair_exact_v1.py (decide_exact, decide_node, farkas, interior_exact), sigpair_node_run_v1.py, sigpair_scan_v1.py.
Node set = prefixes of the J2 tree's terminal paths (`sigpair_nodes_J2_v1.pkl`). Completeness of the pair set relative to the tree: a path that is no prefix of any tree path would be invisible; not checked beyond the 110,081 members and the witnesses above.

## 4. Method checks

- Known pairs (3,1), (4,1), (7,1), (1,3) (exact arrangements from missing_pairs_search_s1.out): `decide_node` on each arrangement's own path returns FEAS with an exact path-equal witness (4 of 4).
- J1 cell-level float run (all 9,652 cells, search guide only): 33 pairs; members' pairs: 9,197 members, the member pair was found feasible in its own cell except 4 thin cells (6,7) [status TOUCH = slack below 1e-11]; the exact procedure (interior_exact/polish) was added after that run.
- Exact INF controls: (1,1) INF at all 614 nodes with opener rank 1; (2,2) at all 13,342; (3,3) at all 24,164; (4,4) at all 27,813 (every node, window-box pass 1, 0 uncertified, 0 budget). (5,5): 18,510 of 33,261 nodes scanned, 0 FEAS; (6,6): 3,713 of 35,667 scanned, 0 FEAS (stopped on request; these two are partial). This agrees with the closer lemma stated by the coordinator (diagonal pairs k < 7 impossible); my own weaker derivation: if some reading t has rho_t > (4/3) rho_s then t has an entry strictly inside (R*, R* + 6/rho_s), so the closer is not s.
- (2,1): 8,750 nodes scanned before the first run was stopped: 2 FEAS, rest INF. (5,1): 8,250 nodes (one half) scanned: 7 FEAS.

## 5. Pair set of the window rho_7 <= 17

Exact arrangement exists for: the 34 member pairs (`sigpair_members_J2_v1.out`), plus (1,2), (1,3), (1,6), (1,7), (2,1), (3,1), (4,1), (5,1), (7,1): 43 pairs.
Absent member pairs (15): (1,1) (1,2) (1,3) (1,6) (1,7) (2,1) (2,2) (3,1) (3,3) (4,1) (4,4) (5,1) (5,5) (6,6) (7,1). Of these 9 now have exact arrangements; remaining 6: (1,1), (2,2), (3,3), (4,4), (5,5), (6,6) -- the diagonal. Status: proved impossible by the coordinator's closer lemma; my exact scans give INF for (1,1)..(4,4) over all nodes, partial for (5,5), (6,6). So the pair set is the 43 pairs, 49 minus the six diagonal pairs k < 7 ((7,7) occurs: 198 members), conditional on the node set being complete.
[UNDECIDED, not run]: exhaustive per-pair counts of nodes/cells for all 49 pairs (the cost was about 10 s per node in all seven closers under CPU contention, 175k nodes); per-cell exact counts for the 7,003 member-less cells (script `sigpair_cellexact_v1.py` written; a 71-cell test run gave 82 feasible, 414 infeasible, 1 uncertified (cell, closer) verdicts; not run on all); pairs feasible only in member-less cells: not determined. Cell-level counts in the request (per-pair cell counts) are therefore not delivered; per-pair member counts are in `sigpair_members_J2_v1.out`.

## 6. Float artefacts found and corrected

- Slack-threshold INF/TOUCH verdicts in the first LP version excluded boundary points (clear gaps are closed, blocking zones open); thin and pinned cells (rho_7 = window edge) were misreported until closed-gap rows and exact projection were used.
- The "infeasible in all cells" statement for the four pairs that a terminal-cell float LP would give is false: it reflects the missing internal-node landing regions, not an exclusion.
