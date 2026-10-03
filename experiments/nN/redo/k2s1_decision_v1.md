# K2s1 decision (v1)

Verdict: (A). K2s1 is empty. The proof below uses no bound on any reading, so it covers rho_6, rho_7 beyond 17.

## Statement
Class K2s1: nmoves >= 2, last setter s with lap 1 (R* = 9/rho_s), and the closer is (s,2), i.e. the smallest entry (8j-1)/rho_y >= R* is 15/rho_s from reading s (code tie rule: lowest rank wins ties).

## Proof
Let p be the setter of the move before the last (exists: nmoves >= 2). R1 = landing of that move = its exit = (8 j_p+1)/rho_p, and R1 < R* = 9/rho_s. Window W = [9/rho_s, 15/rho_s), length 6/rho_s. K2s1 requires no entry of any y>=1 lap in W.

Case A, rho_p >= (4/3) rho_s. Entries of p: (8j-1)/rho_p, j>=1, step 8/rho_p <= 6/rho_s = |W|, first entry 7/rho_p <= 5.25/rho_s < 9/rho_s. A progression with step <= |W| starting below W has a member in the half-open W. That entry is < 15/rho_s, so it precedes s's lap-2 entry; the closer is not (s,2).

Case B, rho_p < (4/3) rho_s. If j_p >= 2 then R1 >= 17/rho_p > 12.75/rho_s > R*, contradiction with R1 < R*. j_p = 0 is impossible (zone (-1/rho,1/rho) lies below 1 <= R). So j_p = 1 and R1 = 9/rho_p < 9/rho_s, so rho_p > rho_s. Then p's lap-2 entry 15/rho_p lies in (11.25/rho_s, 15/rho_s), inside W. It is strictly below 15/rho_s, so the closer is not (s,2).

Both cases contradict the closer being (s,2). QED. The proof does not use the tie rule for the opener, any bound on rho_7, or any lap >= 2 blocker: lap >= 2 zones of every reading with rho < (4/3) rho_s start above R* (45/(4 rho_s) > 9/rho_s), and any reading with rho >= (4/3) rho_s is Case A-type (it itself has an entry in W). Fast readings matter for the closer exactly in this way: they can only remove the class further.
Side fact (also forced): s=1 would need a reading in (7,9) and all others < 4/3, so Case A/B already cover it.

## Evidence (all exact Fractions, path()/outcome())
- k2s1_lemma_check_v1.py / .out: 40,000 exact arrangements (10,000 each: (2,1)/(1,1) cell boxes ranks 2-5 with ranks 6,7 pushed to 17/100/1000; readings in (1,12); readings in (1,20/100/1000); narrow band 1..1.33 x b). Of these, 6,003 had >=2 moves with lap-1 opener; every one was in Case A (448) or Case B (5,555), each case's inequality chain asserted exactly (entry found in W by enumeration in A; lap of p = 1, rho_p > rho_s, 9/rho_s <= 15/rho_p < 15/rho_s in B). Violations: 0. K2s1 hits: 0.
- k2s1_lp_cells_v1.py: the 60 tree cells with last move (2,1) or (1,1) (52 + 8). Per cell, LP over the cell's reading box (+ landing in the cell's [Rlo,Rhi]) for "no entry of any y in [9/x_s,15/x_s)", with per-reading thresholds J_y enumerated by DFS. Result: 0 of 60 feasible (506 LP nodes) (k2s1_lp_cells_v1.out); with ranks 6,7 upper bound raised to 1000: 0 of 60 (same file pattern, k2s1_lp_cells_v1_top1000.out). Control (window shortened to [9/x_s, 9.5/x_s), k2s1_lp_control_v1.out): 52 of 60 cells feasible, so the LP is not vacuous.
- Limits: the LP imposes the box, not the full path-following constraints, so it is a relaxation (infeasible => empty; feasible would need exact verification, none arose). Floating LP (HiGHS), margin t > 1e-9 required for feasibility; an infeasible verdict at a boundary-only (t=0) solution would be missed, but the exact proof does not rely on it.

## Redirect items
(1) fast readings to 100/1000 from the cells: covered by the proof and by the mode-0 samples; closed.
(2) sub-cell closer condition as linear inequalities per cell: LP above, 0/60; closed within the box relaxation, and by the proof generally.
(3) lap >= 2 blockers: cannot occur at or below R* when all rho < (4/3) rho_s; when some rho >= (4/3) rho_s, that reading has an entry in W (Case A). Closed by the proof; no open case remains.
