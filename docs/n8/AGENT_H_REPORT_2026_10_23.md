Rules: 5 (no runner at speed 0; readings are differences from a subject of speed > 0), 7 (covering and counting steps tagged), 15 (exact Fractions, no floats in statements), 16 (new files only, nothing committed), 18 (grades below).

# Agent H report, 2026-10-23: three movers, the remaining 26 frozen sets

## Result
All 26 remaining sets of `Sdisp3` now carry `landing_threeMoverCover2_<set>` for ALL real disparities d1, d2, d3 > a (a = least frozen reading; no upper threshold), conclusion `exists a in disparitySet, Lands`, same form as `landing_threeMoverCover_<set>`: 134, 126, 1236, 136, 146, 1234, 1235, 1237, 145, 156, 1245, 1246, 1247, 1256, 1257, 1267, 1345, 1346, 1347, 1356, 1357, 1367, 1456, 1457, 1467, 1567. With agent G's 25 sets this is 51 of 51 [L]. Axioms of every `landing_threeMoverCover2_<set>` (in `Fresh/S3Cover2_All.lean`): `[propext, choice, Quot.sound]`; sorry, native_decide, axiom, admit, unsafe all 0; untagged 0. Every file was compiled singly with `./check.sh` (per-file log scan: 0 errors, 0 nonstandard axioms, 0 forbidden words in all 826 files). Tags: [PROVISIONAL: covering] (existence of a common clear instant of the three movers in some lonely piece is a finite box cover) and [PROVISIONAL: counting tool] (`r2_box`, `r3_box`, `big3`).

## Method (no new kind of rule was needed)
Same mechanism and rules as agent G (H big3, R3, R2, P; landL3 / land3_later; `exists_clear3_perm`), with the cover search of G (`s3cover_v1.py`, copied unchanged to `s3cover2_v1.py`). Changes: (1) leaf lemmas `r2_box`, `r3_box`, `wit3_box` in `S3Cover2Lemmas.lean`: box bounds `A <= d <= B` as hypotheses, so a leaf is closed by `norm_num` on numerals only; the generator passes the exact hypothesis term for each bound tracked along the path (no `linarith` per leaf); roughly 0.017 s per leaf. (2) The case tree is cut into region files of at most 1500 leaves (`S3Cover2_<set>_R<k>.lean`, each independent), plus a main file with the mechanism, the top of the tree and the assembly. (3) The cap was removed; the depth-limited sets (1234, 1235, 1237, 145) closed at depth 60 with J = 6 (the "depth-budget artefact" guess was right). Every leaf is re-checked in exact Fractions (`check_cert`, imported from G's generator) and every reconstructed box is asserted equal to the search's box before Lean is written. J (last piece used) is the least tried of 6, 8, 10: J = 6 except 1246, 1345, 1357, 1456, 1567 (J = 8) and 1347 (J = 10); a bound, not the true maximum landing piece.

## Per-set data (leaves in the sorted-region cover; D = d1 threshold handled by big3; regions = region files)
| set | J | leaves | D | regions | set | J | leaves | D | regions |
|---|---|---|---|---|---|---|---|---|---|
| 126 | 6 | 3225 | 32 | 3 | 1257 | 6 | 26385 | 56 | 47 |
| 134 | 6 | 4557 | 43 | 4 | 1267 | 6 | 11994 | 50 | 17 |
| 136 | 6 | 4815 | 39 | 4 | 1345 | 8 | 19044 | 80 | 39 |
| 145 | 6 | 5832 | 43 | 6 | 1346 | 6 | 8280 | 43 | 7 |
| 146 | 6 | 5393 | 35 | 5 | 1347 | 10 | 26475 | 69 | 49 |
| 156 | 6 | 9348 | 46 | 9 | 1356 | 6 | 14799 | 60 | 15 |
| 1234 | 6 | 4733 | 43 | 4 | 1357 | 8 | 17338 | 38 | 32 |
| 1235 | 6 | 7883 | 60 | 7 | 1367 | 6 | 11920 | 50 | 15 |
| 1236 | 6 | 5014 | 39 | 5 | 1456 | 8 | 45789 | 92 | 69 |
| 1237 | 6 | 5435 | 38 | 5 | 1457 | 6 | 40640 | 56 | 74 |
| 1245 | 6 | 6151 | 43 | 6 | 1467 | 6 | 38944 | 71 | 63 |
| 1246 | 8 | 9295 | 48 | 9 | 1567 | 8 | 168909 | 94 | 288 |
| 1247 | 6 | 6294 | 38 | 6 | 1256 | 6 | 10060 | 46 | 10 |
Total: 518,552 leaves across 26 sets. Leaf kinds per set (R2 : R3 : P) are in each main file's docstring; H leaves occur only through the `d1 > D` branch of `coreM`. Leaf count does not follow D alone (1357 has D = 38 and 17,338 leaves; 1567 has D = 94 and 168,909): [OBS], the thresholds were not tabulated against the counts further.

## Files created (all new)
Lean, `LonelyRunnerFresh/Fresh/`: `S3Cover2Lemmas.lean` (`r2_box`, `r3_box`, `wit3_box`; imports `S3CoverLemmas`); for each of the 26 sets `S3Cover2_<set>.lean` (pieces `fpieceMX<set>_j`, gaps, `coverMX`, `landL3X<set>_j`, top of the tree `exMX<set>_root`, `coreMX`, `exists_union3_X<set>`, `land3_later_X<set>`) and region files `S3Cover2_<set>_R<k>.lean` (826 `S3Cover2*` files in all, about 300 MB, 1567 alone 99 MB); `S3Cover2_All.lean` (26 theorems `landing_threeMoverCover2_<set>`). Python, `experiments/n8/`: `s3cover2_v1.py` (cover search, copy of `s3cover_v1.py`), `s3cover2_gen_v1.py` (generator). No existing file edited; nothing committed; `RUNNING_LOG_order8_v1.md` untouched.

## Not proved
Movers at or below a; mixed regimes; the cascade's path inside the landing piece; no region is shown to lack a common clear instant (the covers are existence statements, `by_cases` on each piece). The 1567 cover (168,909 leaves) is a large artefact; a stronger leaf rule (for example a pair-clear-component rule R4) was not needed and not written, so none is reported. Scratch logs of the runs are in the session scratchpad, not in the project.
