# Signed split AP chart proof and review, v1

Rules: 1–4, 8–18. New files only; no commits, existing gates or pins altered. Signed readings retain the same physical subject and do not introduce stationary physical runners.

- [L] `Fresh/SignedSplitMiddle.lean` proves49 exact real-parameter charts,12 joined strips, and `signed_split_middle` for every `1≤r≤3`, integer `r−6≤m<0`, and `m+r/8≤a≤m+1−r/8`; all seven signed readings of `splitTrain r a` remain1/8-clear at an explicit positive chart flank.
- [L] All133 negative-reading rewrites use the original signed product, its exact negation, and `distInt_neg`; no reading is removed or approximated. All equality edges are retained.
- [L] Final `check.sh Fresh/SignedSplitMiddle.lean` returns0; all62 theorem axiom lists are exactly `propext, Classical.choice, Quot.sound`; placeholder/native_decide/unsafe scans zero. Harmless unused-tactic linter warnings remain on exact numeric branches.
- [OBS, exact] Reproducible `experiments/n8/signed_split_middle_review_v1.py` passes1,617 complete-cascade controls (33 exact rational parameters per chart), checking49 seven-band charts and12 interval joins; maximum11 actual moves. The signed-to-magnitude coefficient identity is checked reading by reading. Controls are diagnostics, not the symbolic proofs.
- [TREE] `experiments/n8/signed_split_middle_gen_v1.py` generates source directly from the49 exact charts in `signed_split_middle_v1.json`; sample values are never premises of the generated theorems.
- [source reviewed] `SignedSplitAP.lean`, `SignedSplitAPAll.lean`, and `InterleavedGridShift.lean` proof bodies show no mathematical correctness gap: integer laps `(m+j)N` persist, packet reversal is exactly `j↦L−j`, both unbounded ends use the established positive family, and the floor/fractional split reduces to precisely these12 middle strips. Root owns their compilation and physical assembly.
- [PROVISIONAL: counting tool] inherited ceiling/floor selections locate named AP/grid phases; [PROVISIONAL: covering] supports the finite PARAMETER interval splits. No density or time-window covering assertion is used by these chart proofs.
- [OWED/complement] Does not classify arbitrary unequal-step AP blocks or all multi-block arrangements. The physical same-step two-block consumer and integer-collision exclusions are assembled separately.
