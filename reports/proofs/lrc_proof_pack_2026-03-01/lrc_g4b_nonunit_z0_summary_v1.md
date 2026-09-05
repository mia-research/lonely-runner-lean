# NZ0 Finite-Window Certification Report
## v2 — Corrected ELDC (Leave_e), All Candidates, Full Exit Classification

**Date:** 2026-03-05  
**Script:** lrc_g4b_nonunit_z0_certifier_v1.py (v2)  
**Scope:** composite n ∈ [6, 8], L > 2n,
exhaustive distinct sorted templates within L_max bounds below  
**Artifact:** lrc_g4b_nonunit_z0_rows_v1.csv (328 rows total)

---

## Scope Precision

| n | max_e | L_max | Templates scanned | Templates with exits | Interior exits | nu_only_pos exits | Candidate pairs |
|---|-------|-------|-------------------|----------------------|----------------|-------------------|-----------------|
| 6 | 10 | 500 | 536 | 138 | 249 | 178 | 187 |
| 8 | 8 | 400 | 1372 | 34 | 70 | 56 | 56 |

---

## Exit Classification (all interior run exits)

| Category | Distinct exits | ELDC applicable? |
|----------|---------------|-----------------|
| unit_only | 85 | No |
| nu_only_pos | 234 | **Yes — all candidates tested** |
| nu_only_empty | 0 | No |
| mixed | 0 | No |
| other | 0 | No |
| **Total** | **319** | |

---

## NZ0.C1–C8 Checklist

| ID | Description | Result |
|----|-------------|--------|
| C1 | Maximal obstruction runs extracted; each exit fully classified | **PASS** |
| C2 | Filter: nu_only_pos exits only; 234 distinct exits, 243 candidate pairs | **PASS** |
| C3 | Leave_e non-empty for all 243 tested candidates | **PASS** |
| C4 | U_{-e}(b_exit) computed exactly (no inverse, no approximation) | **PASS** |
| C5 | ELDC witness r ∈ Leave_e \ U_{-e} exists for all candidates | **PASS** |
| C6 | ELDC ⟹ D(b_exit) ≥ 1 per candidate | **PASS** |
| C7 | at_B_div_end exits excluded (handled by separate proved sub-lemma) | **PASS** |
| C8 | CSV + markdown artifacts produced | **PASS** |

---

## Counts

- Templates: **1908**
- nu_only_pos distinct exits: **234**
- (exit, candidate_e) pairs in denominator: **243**
- PASS: **243**  FAIL: **0**

## Verdict: **CERTIFIED-FINITE-WINDOW**

All nu_only_pos candidate pairs satisfy corrected ELDC-NZ0.
Zero failures; no counterexample in tested scope.

**What is certified:**
- Composite n ∈ [6, 8]
- All Case-2 tuples: gcd(E)=1, L > 2n, within L_max bounds
- Exhaustive distinct sorted templates; all candidates per exit tested

**What is NOT certified:**
- nu_only_empty exits (0 found; distinct mechanism, outside NZ0 scope)
- n > 8 composite
- Theorem-grade analytic proof (OPEN — requires analytic §5 with Leave_e)

---

## Recommended Tracker Updates

**lrc_proof_checklist_v1.md — row NZ0:**
```
| NZ0 | Corrected ELDC-NZ0 (Leave_e, all candidates per exit) |
| 243 (exit,e) pairs tested; all pass | no failure | CERTIFIED-FINITE-WINDOW |
| scope: n∈{6,8}, exhaustive, L>2n |
```

**lrc_claim_status_table_v1.csv — G4B-NONUNIT-Z0:**
  status: CERTIFIED-FINITE-WINDOW
  evidence: lrc_g4b_nonunit_z0_rows_v1.csv (328 rows)
