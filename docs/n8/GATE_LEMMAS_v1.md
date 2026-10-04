# The gate lemmas, with proofs (v1, 2026-10-04, DRAFT pending adversarial review)

Objects only from the cascade: readings 1 = ρ_1 < ρ_2 < ... < ρ_7 (speed minus the subject's, units of d_min; all positive and distinct); zones Z(y,j) = ((8j−1)/ρ_y, (8j+1)/ρ_y), j ≥ 1, open, pairwise disjoint for one reading, each of width 2/ρ_y; a point R ≥ 1 is *blocked* if it lies in some zone; the cascade from R = 1 jumps from a blocked state to the largest exit among the zones containing it; the *landing* R* is the first unblocked R ≥ 1 (the least unblocked point, because every point passed over lies inside a used zone). Reading 1's zones are (7,9), (15,17), ...; R ∈ [1,7] is never blocked by reading 1 (its j = 0 zone ends at 1).

Carving: K_1 = [1,7]; K_k = K_{k−1} minus the zones of reading k (k = 2..7). A *window* of K_k is a connected component (a closed interval; one point allowed). K_7 is the set of lonely windows in [1,7]; the order of the readings does not change K_7.

Status of each statement: P = proved here by hand (no computation used in the proof); T = tested exactly on the stated sets (a check, not part of the proof); L = in Lean (`ZoneLinkN`).

## L1 (the gate) [(a), (b), (c) P; (d) T only]
(a) R* > 7 ⇔ K_7 = ∅; no landing lies in (7,9). (b) If R* > 7 the path has a state in (7,9). (c) At the first such state s_0, reading 1 is a blocker with exit 9; it is the setter unless some other zone containing s_0 also contains 9 (exit > 9). (d) OBSERVED, not proved: reading 1 is always the setter there, so "R* > 7 ⇔ reading 1 sets a move ⇔ a state equals 9": 0 exceptions among 15,203 crossing members (J=1 7,567, J=2 7,636) and the 12,078 crossing tuples of E366.
*Proof of (a)–(c).* (a) R* ≤ 7 ⇔ some point of [1,7] is unblocked ⇔ K_7 ≠ ∅, because reading 1 does not block [1,7]. If K_7 = ∅, every point of (7,9) is blocked by reading 1's zone (7,9), so R* ∉ (7,9) and R* ≥ 9. (b) A zone of a reading y ≥ 2 has width 2/ρ_y < 2, so a jump from a state s ≤ 7 lands at an exit < s + 2 ≤ 9; the first state above 7 therefore lies in (7,9) (a state equal to 7 is unblocked and would be the landing). (c) At s_0 the zone (7,9) of reading 1 has exit 9; another blocker's exit exceeds 9 only if its zone contains s_0 and 9, i.e. the reading blocks R = 9. ∎
*Gap (d).* A reading y ≥ 2 that blocks R = 9 and whose zone contains the first state above 7 would be the setter instead of reading 1, and reading 1 would never set a move although R* > 7. No argument excludes this; the exact searches (members, seeds, 3.6 million constructed arrangements, and 119,997 random arrangements with a zone straddling 9, none of which crossed) found none. The statement E340 graded [PROVED] was proved only as (a)-(c).

## L2 (one window per zone) [P; T pending (`one_window_per_zone_v1.out`)]
For k = 2..7, a zone of reading k contains at most one window of K_{k−1}.
*Proof.* Suppose two consecutive windows W_1 = [a_1,b_1] < W_2 = [a_2,b_2] of K_{k−1} lie in one zone Z of reading k. The gap (b_1,a_2) is non-empty and contained in Z, so its length is at most |Z| = 2/ρ_k. A point x of the gap is not in K_{k−1} but lies in [1,7], so it is blocked by a zone V of some reading y < k. The endpoints b_1 and a_2 belong to K_{k−1}, so V contains neither; V is an interval containing x, hence V ⊂ (b_1,a_2). Then 2/ρ_y = |V| ≤ |Z| = 2/ρ_k, i.e. ρ_y ≥ ρ_k, contradicting y < k. ∎

## L3 (reading 7 crosses every window of K_6; gate crossers) [P; T 12,078/12,078]
Suppose K_7 = ∅ (R* > 7). Then each window of K_6 lies inside exactly one zone of reading 7 (existence: a window point is blocked, not by readings 1..6, so by reading 7; uniqueness: connected, zones disjoint), the windows lie in pairwise distinct zones (L2), and each such zone is a setter zone (a move) of the path before the gate.
*Proof of the last claim.* The used zones of the path cover [1, R*) (each used zone contains the previous exit; the union is connected from 1). A window point lies in a used zone; the only zones meeting K_6 belong to reading 7; so the zone of reading 7 holding the window is a used zone, i.e. a move. ∎
*Corollary.* A gate crosser's path has at least n_6 moves by reading 7, where n_6 is the number of windows of K_6. Moreover ρ_7 < 2/(length of the longest window of K_6).

## L4 (closer) [P; T 1,593/1,593]
Let R* be a landing with window [R*, R* + w], opener the zone (s,j) of reading s whose exit is R*, and for each reading y let p_y = R*ρ_y mod 8 ∈ [1,7] be its position at R* (p_s = 1). The first entry after R* is that of the reading minimising (7 − p_y)/ρ_y. The opener's own reading is that minimiser only if s = 7.
*Proof.* A reading y with ρ_y > ρ_s has (7 − p_y)/ρ_y ≤ 6/ρ_y < 6/ρ_s = (7 − p_s)/ρ_s. ∎ Hence K2s1 (≥ 2 moves, opener lap 1, closer the opener's reading) is empty: the opener would be rank 7 on lap 1, so a previous setter p slower than 7 on lap 1 would need ρ_p > ρ_7, and on lap ≥ 2 an exit 17/ρ_p < 9/ρ_7, i.e. ρ_p > (17/9)ρ_7; neither holds.

## L5 (the staircase) [P; T 119,278 members and 400,000 random per window]
(a) Each move multiplies the state by at most (8l+1)/(8l−1) ≤ 9/7 (the state lies inside the zone, hence beyond its entry (8l−1)/ρ, and the new state is its exit (8l+1)/ρ). (b) The setter of the move from state R_k has ρ > 7/R_k. (c) Consecutive setters differ (the setter is at position 1 at its exit). (d) If the first k+1 setters are distinct then ρ_{7−k} > 7(7/9)^k.
*Proof.* (a) as stated. (b) zone entry ≥ 7/ρ < R_k. (c) clear. (d) the i-th setter has ρ > 7/R_{i−1} > 7(7/9)^{i−1} by (a) and R_{i−1} < (9/7)^{i−1}; the k+1 distinct setters have ranks ≤ 7 − k at their lowest, so ρ_{7−k} ≥ that setter's reading. ∎

## L6 (link rule) [L, `ZoneLinkN`; T 136,199]
After a move to the exit of (s,j), a slower reading blocks only at a lap ≤ j and a faster one only at a lap ≥ j+1; equal readings cannot link.

## Consequences that follow from L1-L6 and an observation, not from them
The opener of a gate-crossed outcome (R* = (8j+1)/ρ_s ∈ [9, 15)) has lap j = (ρ_s R* − 1)/8, so the confinement of the B opener laps (rank 2: 3-5, 3: 4-6, 4: 5-6, 5: 5-8, 6: 7-9, 7: 8-18 at ρ_7 ≤ 25) is an exact consequence of two things not proved here: a bound on the readings of crossers (observed ρ_6 ≤ 8.14, ρ_5 ≤ 7.07, ρ_4 ≤ 6.19, ρ_3 ≤ 5.28, ρ_2 ≤ 4.76; ρ_7 up to 24.38) and R* < 12 (observed 11.966 maximum). The 14 outcome classes (opener rank × window, minus "opener 1 in window A", plus no move) are every logically possible combination, so their number is not evidence of anything by itself.

## What is not proved (the pieces the pattern needs)
1. L1 (d): reading 1 is the setter at the first state above 7 (equivalently: no reading blocks R = 9 with a zone that also contains that state while the chain crosses). A proof or a counterexample (the exact fine-cell machinery can search for the second: a gate-crossing fine cell whose path has no reading-1 move).
2. A floor for the longest window of K_6 (or any bound ρ_7 ≤ F(ρ_2..ρ_6)): the first-window form L ≥ 2/(7ρ_6) is false (E359).
3. A bound on the readings ρ_2..ρ_6 of gate crossers.
4. R* < 12 for gate crossers.
