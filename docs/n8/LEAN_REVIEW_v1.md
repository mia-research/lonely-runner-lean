# Lean review v1 (2026-11-02): items 1 to 4 over both trees

Owner request (2026-11-02): *"Yes, run 1 to 4"*. Trees: N = nested repo `LonelyRunner/LonelyRunner` (1,434 files parsed), F = `LonelyRunnerFresh/Fresh` (4,859 of 4,950 `.lean` files hold declarations). Rule 22, the other 91: (i) feature: no declaration; (ii) what forces it: each consists only of `import` lines and `#print axioms` lines, with at most a module docstring and `set_option` (85 import and `#print` only, 3 with a docstring, 3 with a docstring and `set_option`; `ArrangementTypesOct26FullAuditV*`, `JointAuditOct29` and similar audit files); two files also have lines starting otherwise, docstring continuation lines in `TrainFlankThreeBlockAudit` and `--` comments in `ArrangementTypesOct26Audit`, neither a declaration (`experiments/lean_review/unparsed_files_v1.{py,out}`, first token of every line); (iii) a different kind of file from the rest, audit files that print axioms of declarations made elsewhere; not a parser miss. Understood. Method: a text parser over every file (`experiments/lean_review/extract_decls_v1.py`, 1,987,584 declaration headers, comments stripped), then `review_items_v1.py`; full tables in `experiments/lean_review/review_tables_v1.md`. **Heuristic, not Lean's elaborator**: `variable` binders are not seen; item 4 compares signatures as text, so a renamed bound variable hides a duplicate (the E759 `lastOpening` case below is one it missed). No build was run.

## Findings (one line each)

**Item 1, target links** (33 theorems; table 1).
- N: 15 theorems conclude `LRC.Spec.LonelyRunnerAt8`, every one from a named hypothesis (`WindowBound`, `Cover8 M`, `WideStep8 M`, `CaseB8`/`CaseC8`, `ExistenceAt8`, `ExistenceAt8_congruence`, `ArrBlockRule8` ×4 with `ArrBoundedCovered8`, the five door forms, the slowest-runner, arrangement and residual forms); 3 are `↔`; 1 starts from the target. None concludes it with no hypothesis.
- F: 7 `↔` with `Fresh.LonelyRunnerEight`, 2 conclude it from a hypothesis (`DisplacementPath`; `owed_pair_imp_lre` from two path Props), 5 start from it. None concludes it with no hypothesis.
- No theorem in either tree mentions both targets.

**Item 2, owed register** (table 2).
- F: 50 declarations tagged `STANDING: OWED`, 43 distinct names (7 repeated in `*Free.lean` copies). 33 have a theorem whose conclusion is the Prop, 14 of them with no binders.
- **14 OWED tags are stale**: the Prop has an unconditional theorem in the folder (signature read, axioms not re-run). Among them `Fresh.Ladder.SixDisparitiesLonely` (six positive real readings lonely at `1/8`; `OwedDischarged.sixDisparitiesLonely_proved`), `FiveDisparitiesLonely`, `GridGlobalIsolation`, `FiveDisparitiesLowQuotient` and ten `Fresh.Where.*` cascade facts (`WhereProofs.*`).
- F, concluded only from hypotheses (12): `LonelyRunnerEight`, `NatLonely8`, `ResidualLonely8`, `ResidualRest`, `ResidualRest2` to `ResidualRest5`, `StrongGate`, `FiveCarve`, `FiveReach`, `SuccessorIsolation`.
- F, no theorem concludes these at all (16): `DisplacementPath`, `CascadeForm`, `CandidateScaleForm`, `PathLonelyBound`, `ConjectureGivesBound`, `SecondStage.OneMultipleCellExists`, `FiveChainWeight`, `NoSmallIntegerCrosser`, `ReadingsAboveFifteenSevenths`, `ReachFourSharp`, `ReachFiveSharp`, `FourDistinctLaw`, `CompatAll`, `SixDisparitiesQuotientBounded`, `GridInstantDisplacement`, `ResidualRest6`.
- N: the 9 named hypotheses of item 1: 6 concluded by no theorem (`CaseB8`, `CaseC8`, `ArrBlockRule8`, `ArrBoundedCovered8`, `WindowBound`, `Cover8`); 3 concluded only conditionally (`WideStep8`, `ExistenceAt8`, `ExistenceAt8_congruence`). The door, slowest, arrangement and residual hypotheses are quantified forms and are not in the register (not covered).

**Item 3, PROVISIONAL tags** (table 3; raw lines, comments included).
- N: 10 files, 13 covering and 23 counting-tool tags, all in order-8 or residue files (`OrderEightNativeMarginN` 7 covering).
- F: 3,522 files, 31,822 covering and 1,544 counting-tool tags. 29,064 covering tags are in the 1,164 generated landing certificates `CertRS/B*.lean` (one `hcov` per certificate). The ladder families carry the rest (`S3Cover2` 850 + 850, `ThreeMoverLarge` 102 + 51, `TwoMover*`, `S2*`, `OneMover*`).

**Item 4, duplicates** (table 4).
- Across trees: 30,510 signature groups (63,022 declarations) in 331 (N file, F file) pairs; the largest are F's `Nv_*` files (476 in F) copying N's order-6 and order-7 files (`IntLRC_6_BHK_Prop11` ↔ `Nv_OrderSixPropElevenN` 256 groups; `OrderSevenU5A*N` ↔ `Nv_OrderSevenU5A*N` about 200 each).
- Within F: 4,778 groups (1,311,177 declarations); 3,394 groups (1,307,025 declarations) lie wholly in `Cert*` folders; 1,384 groups (4,152 declarations) do not (`dup_withinF_nocert_v1.txt`).
- This session's duplicates: all 43 `fpieceX<S>_k` (E756, `PairCarriedTables.lean`) restate frozen-piece lemmas already present as `fbp`, `fpieceL`, `fpieceB`, `fpieceBL` (`S2Below_*`, `S2Later_*`, `OneMoverBelow*_*`); E759's `lastOpening` / `last_opening_clear` restate `Fresh.Localisation.lastOpening` / `clear_between` (found by reading, not by the script).
- Within N: 1,177 groups (3,103 declarations).

## Not covered by this review
- Whether any theorem is correct or axiom-clean: no build, no `#print axioms` in this review.
- Quantified hypotheses (door, slowest, arrangement, residual forms) in item 2.
- Duplicates up to renaming of bound variables or namespaces other than `Fresh.*` / `LRC.*`.
- Item 5 (one tree): owner's decision.
