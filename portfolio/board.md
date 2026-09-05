# Portfolio Board
**Phase:** 0 complete → Phase 1 OPEN
**Last updated:** 2026-02-25
**Gate status:** PASS ✅ — 96.6% assigned (134 frontier, 3.4%)

---

## Track Scorecard

| Track | Artifacts | Queue | Claims seeded | Top claim status | Phase 1 ready |
|-------|-----------|-------|---------------|-----------------|----------------|
| LRC | 692 | track_assigned | 0 (pending Catalog Agent) | — | ✅ OPEN |
| Cross_Domain_Methods | 1,023 | track_assigned | 0 | — | ✅ OPEN |
| RH_LFunctions | 886 | track_assigned | 0 | — | ✅ OPEN |
| Prime_Systems | 490 | track_assigned | 0 | — | ✅ OPEN |
| Algebra_Candidates | 479 | track_assigned | 0 | — | ✅ OPEN |
| Integer_Dynamics_Kaprekar | 233 | track_assigned | 0 | — | ✅ OPEN |
| **Frontier_Unclassified** | **134** | frontier_queue | — | — | — |
| OUT_OF_SCOPE | 766 | out_of_scope | — | — | — |
| **TOTAL** | **4,703** | | | | |

---

## Phase 0 Gate

```
Metric                        Value      Target     Status
────────────────────────────────────────────────────────
Research artifacts            3,937      —          —
Assigned (conf ≥ 0.65)        3,803      ≥ 3,544    ✅ PASS
Assignment rate               96.6%      ≥ 90.0%    ✅ PASS
Deferred (conf < 0.65)        0          ≤ 394      ✅ PASS
Frontier                      134        ≤ 394      ✅ PASS
OOS (excluded from gate)      766        —          —
```

**Gate: PASS.** Phase 1 is open for all tracks. LRC is the primary Phase 1 focus per project charter.

---

## Priority Queue (Phase 1 seed candidates)

### LRC — High Priority
These files are highest-priority candidates for Catalog Agent ingestion:

| Priority | Filename | Type | Reason |
|----------|----------|------|--------|
| P1 | A Formal Proof of the Lonely Runner Conjecture (Draft with Explanations).docx | docx | Primary proof artifact |
| P1 | A Structural Reduction of the Lonely Runner Conjecture v4.txt | txt | Latest structural reduction |
| P1 | A Structural Reduction of the Lonely Runner Conjecture v3.txt | txt | Prior version for comparison |
| P2 | A Structural Reduction of the Lonely Runner Conjecture.pdf | pdf | Published-format draft |
| P2 | A Structural Reduction of the Lonely Runner Conjecture.md | md | Annotated markdown version |
| P3 | 09_k_moment_sweep.csv | csv | Empirical sweep data |
| P3 | Alignment_Hypothesis___Evidence__3_configs___5_runners_.csv | csv | Evidence table |

### Kaprekar — Watchlist
See `portfolio/watchlist_kaprekar.md`

### Algebra Candidates — Watchlist
See `portfolio/watchlist_algebra_candidates.md`

---

## Phase 0.5 Plan (Completed)

To resolve 2,000 frontier files and reach the ≥ 90% gate:

| Step | Action | Expected yield |
|------|--------|---------------|
| 1 | First-500-char sampling of text-readable frontier (.md, .txt, .html, .py, .csv) | ~900 files → resolved |
| 2 | First-500-char sampling of .pdf, .docx (if extractable) | ~500 files → resolved |
| 3 | ZIP manifest inspection (list archive members) | ~100 files → resolved |
| 4 | Residual images/binaries remain in frontier | ~500 files → acceptable |

Post-Phase-0.5 assignment rate achieved: **96.6%** (gate PASS achieved).

---

## Claim Status Legend

| Code | Meaning |
|------|---------|
| A-Validated | Passed all 9 rubric dimensions + two-model quorum |
| B-Promising | Passed formal + empirical; reproducibility pending |
| C-Underspecified | Assumptions unclear; needs tightening |
| D-Refuted | Counterexample found or logical flaw confirmed |
| U-Unresolved | Frontier — insufficient evidence to score |

---

## Changelog

| Date | Event |
|------|-------|
| 2026-02-25 | Phase 0 classifier v4 run; 4,703 files processed; initial gate PARTIAL (54.0%) |
| 2026-02-25 | Registry CSVs written: corpus_manifest, track_map, frontier_queue, deferred_queue, out_of_scope, claim_seed_queue |
| 2026-02-25 | Phase 0.5 content-sampling pass (6 iterations): HTML stripping, DOCX extraction, RTF via textutil, Unicode symbols, filename rescue |
| 2026-02-25 | Phase 0.5 complete: 96.6% assigned, 134 frontier (3.4%) — gate PASS ✅ |
| 2026-02-25 | Phase 1 opened: LRC primary focus; all 6 tracks ready for Catalog Agent ingestion |
