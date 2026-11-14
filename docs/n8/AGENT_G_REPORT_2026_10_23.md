Rules: 5 (no runner at speed 0; readings are differences from a subject of speed > 0), 7 (covering and counting steps tagged), 15 (exact Fractions; no floats in statements), 16 (new files only), 18 (grades below).

# Agent G report, 2026-10-23: three movers, all disparities strictly above the least frozen reading

## Result
25 of the 51 frozen sets of `Sdisp3` carry `landing_threeMoverCover_<set>` for ALL real disparities d1, d2, d3 > a (a = least frozen reading), no upper threshold, conclusion `exists a in disparitySet, Lands` (the form of `ThreeMoverLandingAll`): 12, 13, 23, 123, 124, 125, 135, 234, 235, 245, 2345, 2346, 2347, 2356, 2357, 2367, 2456, 2457, 2467, 2567, 3456, 3457, 3467, 3567, 4567. [L], axioms `[propext, choice, Quot.sound]`, 0 sorry / native_decide / axiom / admit / unsafe, untagged 0, each file compiled singly with `./check.sh`. Tags: [PROVISIONAL: covering] (existence of a common clear instant of the three movers in some lonely piece of the frozen set is a finite box cover) and [PROVISIONAL: counting tool] (`r2_rect`, `r3_rect`, `big3`).

## Files created
Lean (`LonelyRunnerFresh/Fresh/`): `S3CoverLemmas.lean` (`clear3_swap12/23`, `exists_clear3_perm` sorted-to-any-order, `wit3` point witness, `r2_rect` rule R2, `r3_rect` rule R3, `big3`); `S3Cover_<set>.lean` for the 25 sets above (each: `fpieceM`, `gapM`, `coverM`, `landL3<set>_<j>` mechanism per piece, chunked cover lemmas `exM<set>_<k>`, `coreM`, `exists_union3_<set>`, `land3_later_<set>`); `S3Cover_All.lean` (25 theorems `landing_threeMoverCover_<set>`).
Python (`experiments/n8/`): `s3cover_v1.py` (exact box cover), `s3cover_gen_v1.py` (generator; re-checks every leaf and every reconstructed box with an independent function before emitting Lean). Also `s3_sample_v1.py` (exact random sample, [OBS]).

## Method
Mechanism: `landL3<set>_<j>` is the three-mover analogue of `landL`: if pieces i < j hold no common clear instant (Clear3) and piece j does, the first lonely instant exists (`IsFirst`), lies in piece j and is the first common clear instant from its left end (`first_three_clear`, `lonely_insert3_iff`); `land3_later_<set>` assembles by `by_cases` on each piece. Existence is the cover on the sorted region d1 <= d2 <= d3 (`exists_clear3_perm` removes the ordering). Leaf rules: H (`big3`, A1 (r-l) >= 4), R3 (mover X clear on [p,q], other two Y <= Z with q-p >= 1/A_Y, `two_clear_in2`), R2 (two movers clear on [p,q], third with 4 A_c (q-p) >= 1, `firstPt`), P (point witness). Splitting: relative width, unbounded dimensions split at the exact R2/R3 threshold. A first version bounded d3 wrongly in one unbounded split; the box-reconstruction assertion caught it and it was fixed before any Lean was written.

## Per-set data (J = last piece used, leaves, d1 > D handled by big3)
| set | J | leaves | D | set | J | leaves | D |
|---|---|---|---|---|---|---|---|
| 12 | 0 | 329 | 13 | 2346 | 2 | 1124 | 48 |
| 13 | 0 | 1347 | 24 | 2347 | 2 | 1629 | 64 |
| 23 | 0 | 156 | 18 | 2356 | 2 | 1117 | 48 |
| 123 | 0 | 1347 | 24 | 2357 | 2 | 1614 | 64 |
| 124 | 2 | 1349 | 26 | 2367 | 2 | 1174 | 50 |
| 125 | 2 | 1946 | 27 | 2456 | 2 | 1157 | 48 |
| 135 | 6 | 2118 | 27 | 2457 | 2 | 1349 | 56 |
| 234 | 0 | 250 | 26 | 2467 | 6 | 1684 | 64 |
| 235 | 0 | 510 | 36 | 2567 | 2 | 1625 | 64 |
| 245 | 0 | 510 | 36 | 3456 | 0 | 249 | 39 |
| 2345 | 0 | 510 | 36 | 3457 | 0 | 633 | 48 |
| 4567 | 0 | 245 | 43 | 3467, 3567 | 0 | 633 | 48 |
J is the least of the tried values {0,2,6} (a bound, not the true maximum landing piece). Rule families: all three of R2, R3, P in every set; later pieces (R2/R3/P in pieces 1 to 4) only in the J > 0 sets; H only for d1 > D.

## Not proved (51 less 25 = 26 sets)
Cover attempted with cap 3000 leaves (J in {0,2,6}, depth 24):
- Cover found but larger than the cap (not compiled): 134 (4557 leaves), 126 (3258), 1236 (5014), 136 (4815), 146 (5393).
- Not closed at depth 24 (failing boxes printed by the generator are depth-budget artefacts: for 1234 the two reported boxes close in 3 to 4 leaves when started afresh, so these likely close at larger depth with a cover of roughly 4700 leaves): 1234, 1235, 1237, 145.
- Not attempted (thresholds D 80 to 280, leaf counts expected to grow with D): 156, 1245, 1246, 1247, 1256, 1257, 1267, 1345, 1346, 1347, 1356, 1357, 1367, 1456, 1457, 1467, 1567. No exact uncovered-region map was produced beyond the above; no region is shown to lack a common clear instant (sampling `s3_sample_v1.py` for 1234: 3000 of 3000 samples in (1,30) held one in piece 0; with d in (1,12) a few needed pieces 1, 2, 5) [OBS].
Also not proved: movers at or below a, mixed regimes, the cascade's path inside the landing piece. Nothing committed; no existing file edited; `RUNNING_LOG_order8_v1.md` untouched.
