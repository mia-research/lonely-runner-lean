# Phase 0 Portfolio Summary
**Generated:** 2026-02-25
**Classifier version:** phase0_final.py (v4) + Phase 0.5 content-sampling (6 passes)
**Gate status:** PASS ✅ — 96.6% assigned, frontier 3.4%

---

## 1. Corpus Overview

| Metric | Count |
|--------|-------|
| Total files scanned (Downloads/) | 4,703 |
| Out-of-scope (personal/business) | 766 |
| Research artifacts (in-scope) | 3,937 |
| Assigned to track (conf ≥ 0.65) | 3,803 |
| Frontier (unclassified) | 134 |
| Deferred (conf < 0.65, non-frontier) | 0 |

**Assignment rate:** 3,803 / 3,937 = **96.6%**
**Phase 0 gate threshold:** ≥ 90% assigned at conf ≥ 0.65
**Deferred + frontier threshold:** ≤ 10%
**Gate result:** ✅ PASS

---

## 2. Track Distribution (In Scope)

| Track | Artifacts | % of Research | Queue |
|-------|-----------|---------------|-------|
| Cross_Domain_Methods | 1,023 | 26.0% | track_assigned |
| RH_LFunctions | 886 | 22.5% | track_assigned |
| LRC | 692 | 17.6% | track_assigned |
| Prime_Systems | 490 | 12.4% | track_assigned |
| Algebra_Candidates | 479 | 12.2% | track_assigned |
| Integer_Dynamics_Kaprekar | 233 | 5.9% | track_assigned |
| Frontier_Unclassified | 134 | 3.4% | frontier_queue |

---

## 3. Registry Output Check

| File | Rows (excl. header) | Status |
|------|----------------------|--------|
| `corpus_manifest.csv` | 4,703 | ✅ |
| `track_map.csv` | 4,703 | ✅ |
| `frontier_queue.csv` | 134 | ✅ |
| `deferred_queue.csv` | 0 | ✅ |
| `out_of_scope.csv` | 766 | ✅ |
| `claim_seed_queue.csv` | 80 | ✅ |

---

## 4. Phase 1 Status

Phase 1 is **OPEN and STARTED (Cycle 002 kickoff complete)**.

Primary execution order:
1. Catalog Agent extraction on seeded LRC queue.
2. Notation and Measurement audits on seeded claims.
3. Proof Structurer pass on top P1 seeds.
4. Refuter handoff for promoted claims.

---

## 5. Notes

- This summary is aligned to the current registry files and supersedes earlier partial-gate draft text.
- Historical Phase 0.5 details remain in `portfolio/board.md` changelog entries.
