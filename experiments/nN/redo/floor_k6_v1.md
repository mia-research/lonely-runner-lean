# floor_k6_v1 -- record only (stopped on the owner's instruction, 2026-10-04)

No script was written or run for this file. No background process was started. Every computed value below is quoted from `k6map_structure_v1.md`, `ceil_gate_crosser_v1.md` or `GATE_LEMMAS_v1.md` (exact Fractions there); the items marked HAND are derived here by hand and NOT tested. No floor is claimed.

## (a) K6 empty or one-point-only
* Exact tuple with K6 empty or finite: none in the record, and none produced here.
* Searched in the record (not by me): integer six-sets {1}+five in [2,24] (33,649), halves (142,506), thirds (237,336), mixed halves/thirds (98,280): K6 never empty and never all one-point windows. Metropolis on total K6 length (rho_6 <= 9: 130 restarts; rho_6 <= 30: 67 restarts): smallest total length 0.13862 / 0.15571, no empty or finite K6. Three adjacency walks (10,702 cells): no such cell. Stated as: not reached by those searches.
* Not searched: rho_6 > 30; a complete exact decision over cells.
* HAND, not run: an exact criterion (a method, not a result). For the strict-order system u_{i+1} < u_i (u = 1/rho) every row of a zone chain (entry_{k+1} < exit_k, exit_k < exit_{k+1}, R=1 < exit_0, last exit > 7, and rho_6 <= B) is binary (p u_a < q u_b). Feasibility is then a negative-cycle test (product of ratios around a cycle <= 1) in exact Fractions, so "K6 empty (or finite, with exit = entry links allowed) for some tuple with rho_6 <= B" is decidable by a depth-first search over irredundant chains. It was not implemented, so this gives no verdict on (a).

## (b) Infimum of r_6 L_max (record values)
Smallest 7 r_6 L_max / 2 found: 6615/7496 = 0.882471 (cell minimum, closure vertex, attained by the valid tuple)
rho = (1, 6559/2279, 26236/6779, 231/47, 26236/4115, 7); L_max = 135/3748 (four windows of that length); r_6 L_max = 945/3748.
Tight rows (exact dual weights 9537, 7935, 6647, 5865 over 29984), as exit-equals-entry statements: exit of (6,3) = entry of (5,3); exit of (3,2) = entry of (6,4); exit of (5,4) = entry of (2,2); exit of (2,2) = entry of (3,3). The position of rho_4 is not binding. rho_6 = 7 is the entry (6,1) = R=1 tie. The 50 lowest cells all have rho_6 = 7 (or 47/7: entry (6,6) = 7).
Not done here: the facet-crossing walk with the 1.3 threshold; the true infimum is undecided (three walks reached nothing lower).

## (c) Recursion (HAND; untested against the sweeps)
Carving K_k = K_{k-1} minus the open zones of reading k; w_k = 2/r_k; zones of one reading are spaced 8/r_k, so consecutive zones leave a closed gap of exactly 6/r_k.
Piece lemma. Let W be a window of K_{k-1} with length l > w_k. W meets zones of reading k in one of three ways:
* no zone: a piece of length l.
* exactly one zone: if the zone lies strictly inside W, two pieces of total length l - w_k, so the longest is >= (l - w_k)/2; if it covers an end, a piece >= l - w_k.
* two or more zones: W is connected and meets both, so it contains the whole gap between them, a piece of length 6/r_k.
So the longest piece is >= min((l - 2/r_k)/2, 6/r_k) whenever l > 2/r_k, and l_1 = 6.
What closes: the inequality l_{k-1} > 2/r_k, which holds for every k whenever each reading is large enough relative to the one before it (the case l_{k-1} ~ 6/r_{k-1} gives it for r_k > r_{k-1}/3), but each carve can halve the length, so a positive explicit floor needs spacing conditions on the readings.
What does not close: l_{k-1} <= 2/r_k. Then every window of K_{k-1} may lie inside a zone of reading k (one per zone, by L2) and K_k can be empty; nothing in the lemma excludes it. For k = 6 this is exactly L3's condition with K_7 replaced by K_6.
The recursion does not use L2. No violation count was computed.

## Exceptions
Nothing new computed; (b) and the searches are the record's. The record's statement (iii) of the task, R8, was not examined. No lemma in GATE_LEMMAS format was written.
