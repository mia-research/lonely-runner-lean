Rules: 5 (no runner at speed 0; readings are differences from a subject of speed > 0), 7 (covering and counting steps tagged), 15 (exact Fractions, no floats in statements), 16 (new files only), 18 (grades below).

# Agent D report, 2026-10-23: two movers, the 25 frozen sets with a failing first-piece region, all movers beyond the least frozen reading

## Result
All 25 remaining frozen sets of `Sdisp2` (37 less the 12 clean ones of `S2Clean_All`) are done for ALL real `d1, d2 > a` (a = least frozen reading): 125, 1235, 1245, 1345, 12345, 12347, 12367, 1236, 1246, 1256, 1346, 1356, 1456, 12346, 12356, 12456, 13456, 12567, 13567, 12467, 13467, 12357, 12457, 13457, 14567. Together with Agent B's 12 clean sets, all 37 frozen sets now carry the two-mover landing statement for both disparities strictly above the least frozen reading. No region was left uncovered; no set needed reasoning beyond "least piece holding a common clear instant".

## Method (differs from the brief in one respect, deliberately)
The brief asked for per-polygon NONEXISTENCE proofs for the first wide piece. They are not needed and were not built. The theorem is stated with the case split on the existence statement itself:
- `exists_union_<set>`: for all `d1, d2 > a`, SOME lonely piece `P_j` of the frozen set, `j <= J`, holds a common clear instant of the two movers. Proved by a finite box cover of `{d1 <= d2}` (columns in `d1`, cells in `d2`), each box certified in some piece by `wit_pt` (point witness), `r1_rect` (rule R1) or `big_both` (both movers large). A box may use any piece, so the boundary of the first piece's failing region never has to be cut by a slanted line: where piece 0 fails, piece 1 or later is certified for the same box.
- `landL<set>_<j>` (the step-1 theorem, any piece index): for any `d1, d2 > 0`, IF no piece `i < j` holds a common clear instant and piece `j` does, THEN the first lonely instant `T` of the frozen set with both movers exists (`IsFirst`), `T` lies in piece `j`, and `T` is the first common clear instant at or after the left end of piece `j`. Earlier pieces are excluded by the hypothesis, the gaps between pieces by `fnot` (`gapL`), later pieces by order (`coverL`). No period shift lemma was needed: pieces are listed in the first lap only (index `<= 5 < ` one period), so the shift lemma of the brief does not enter.
- `land2_later_<set>`: assembled by `by_cases` on each piece in turn (not-exists in piece `i` is the hypothesis `hn_i` of the next `landL`), concluding `IsFirst` and, as a disjunction over `j`, the landing piece with its minimality clause.
- `S2Later_All.lean`: `landing_twoMoverLater_<set>` in the same Lands form as `S2Clean_All` (cascade sequence reaches `T`; every fixed point equals `T`), hypotheses `a < |x1 - (c+k)|`, `a < |x2 - (c+k)|`, `hS : Sdisp2 k m1 m2 = F`.

Per-set cover data (J = last piece index needed, the least J for which the cover closed; columns in `d1`; boxes; big-both threshold D0 = least `ceil(1/L_j)` over pieces `<= J`, and the piece used for it):

| set | J | columns | boxes | D0 | big piece |
|---|---|---|---|---|---|
| 125 | 1 | 6 | 9 | 7 | 1 |
| 1235 | 1 | 14 | 22 | 15 | 1 |
| 1245 | 1 | 10 | 19 | 11 | 1 |
| 1345 | 3 | 21 | 53 | 20 | 0 |
| 12345 | 5 | 22 | 52 | 20 | 0 |
| 12347 | 3 | 22 | 55 | 18 | 1 |
| 12367 | 3 | 15 | 29 | 13 | 1 |
| 1236 | 1 | 9 | 18 | 10 | 1 |
| 1246 | 2 | 31 | 46 | 32 | 1 |
| 1256 | 1 | 13 | 36 | 12 | 1 |
| 1346 | 3 | 10 | 21 | 11 | 3 |
| 1356 | 2 | 18 | 51 | 15 | 1 |
| 1456 | 3 | 25 | 57 | 23 | 3 |
| 12346 | 4 | 15 | 29 | 16 | 3 |
| 12356 | 2 | 18 | 51 | 15 | 1 |
| 12456 | 5 | 33 | 65 | 32 | 1 |
| 13456 | 4 | 26 | 60 | 23 | 3 |
| 12567 | 4 | 26 | 69 | 24 | 1 |
| 13567 | 4 | 24 | 47 | 24 | 1 |
| 12467 | 3 | 20 | 53 | 18 | 3 |
| 13467 | 4 | 29 | 70 | 28 | 2 |
| 12357 | 4 | 25 | 63 | 24 | 2 |
| 12457 | 2 | 20 | 59 | 14 | 2 |
| 13457 | 5 | 51 | 145 | 45 | 3 |
| 14567 | 4 | 49 | 136 | 45 | 3 |

Note on J: it is the least J for which the box cover closes, an upper bound for the landing piece, not the maximum landing piece seen. The easy sets 125, 1235, 1245 need J = 1 (the 7 failing pairs of the brief land in piece 1, `[9/40, 3/8]` for 125). 1345 and 12345 need pieces up to 3 and 5 (the grid had single pairs landing in pieces 2, 3 and 5).

## Files created
Lean, all in `LonelyRunnerFresh/Fresh/`, each compiled singly with `./check.sh`, all axiom outputs `[propext, choice, Quot.sound]`, 0 sorry / native_decide / axiom / admit / unsafe, untagged 0:
- 25 files `S2Later_<set>.lean` for the sets above (14,850 lines in total with `S2Later_All.lean`). Each holds `fpieceL`, `gapL`, `coverL`, `landL<set>_0..J`, `colL<set>_<ci>` (one lemma per column, `set_option maxHeartbeats 400000 in`), `coreL`, `exists_union_<set>`, `land2_later_<set>`. `set_option maxHeartbeats` is used on the column lemmas only (the one-block version of 1345 timed out at 200000).
- `S2Later_All.lean`: 25 theorems `landing_twoMoverLater_<set>`.
Python, in `experiments/n8/`: `s2later_cover_v1.py` (exact multi-piece box cover), `s2later_gen_v1.py` (generator; re-checks every certified box with an independent function before emitting Lean) and `s2later_gen_v1.out` (per-set cover data), `s2later_sample_v1.py` and `s2later_sample_v1.out`.
Existing files used unchanged: `S2CleanLemmas.lean` (`wit_pt`, `r1_rect`, `big_both`, `clear2_symm`), `CascadeLanding2.lean`, `CascadeLanding2b.lean`, `TwoMoverLandingAll.lean`. No existing file was edited; nothing committed; `RUNNING_LOG_order8_v1.md` untouched.

## Grades
- [L] for every theorem listed. [PROVISIONAL: covering]: `exists_union_<set>` (finite box cover), and the gap covers `coverL`. [PROVISIONAL: counting tool]: `r1_rect`, `big_both` by inheritance.
- [OBS] `s2later_sample_v1.out`: 400 random exact rational pairs per set for 9 sets (125, 1345, 12345, 12347, 12367, 1236, 12456, 13457, 14567) with `d1, d2` in `(a, D0 + 5)`: the freeze landing (first piece whose movers-only cascade from its left end stays inside it) equals the full cascade landing in all samples, and the landing piece never exceeded J. Sanity check only, not part of any proof.

## Not proved
- Movers at or below the least frozen reading `a`, and the mixed regime where a mover disparity lies below `a` (also not required here).
- The cascade's path inside the landing piece, and which setter moves in which order.
- No characterisation of the failing region of the first wide piece as a union of polygons was produced; the Lean statement avoids needing it. The region itself is therefore described only by [OBS] counts (`s2_fail_region_v1.out`) and by the certificates: for 125 the cover assigns every `(d1, d2)` in `d1 <= 7` a piece-0 or piece-1 certificate.
- Whether J is the true maximum landing piece for each set: J is the least index at which the cover closed, so the true maximum is `<= J`; the sample shows lower values for the sets sampled.
- `Sdisp2`-set membership of the arrangements (existence of `(k, m1, m2)` giving each set) is not part of these theorems; they are stated for any `(k, m1, m2)` with the given `Sdisp2`.
