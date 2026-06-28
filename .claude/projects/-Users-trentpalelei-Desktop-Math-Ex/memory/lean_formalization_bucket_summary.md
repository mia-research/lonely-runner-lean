---
name: lean-formalization-bucket-summary
description: Complete categorization of 19 remaining sorries (post-bucket-a clearance)
metadata: 
  type: project
  priority: high
  lastUpdated: 2026-05-22
  totalRemainingSorries: 19
---

# Lean 4 LRC Formalization — Remaining Sorries (19 total)

## Status Summary
- **Bucket (a) CLEARED**: 6 API lookups fixed and removed ✓
  - Defs.lean:52 (circDist.symm_neg)
  - Theorem61_BSR.lean:38, 41 (division inequalities)
  - Theorem61_BSR.lean:48, 49 (min arithmetic)
  - Theorem121_Main.lean:57 (lemma92_DI_partition)

- **Remaining: 19 sorries** = Bucket (b) + (c)
  - Bucket (b): ~10-11 straightforward math (5-20 lines each, ~2-4 hours)
  - Bucket (c): ~8-9 genuinely hard (20-60 lines each, depends on Theorem 5.2)

- **Build status**: ✓ Passing (0 errors, 20 warnings about sorries)

---

## Bucket (b): Straightforward Math (~55-90 lines, 2-4 hours)

These require clear proof arguments, are NOT load-bearing for main theorem, each ~5-20 lines.

| File | Line | Theorem | Issue | Est. LOC | Difficulty |
|------|------|---------|-------|---------|------------|
| Lemma21_FundamentalIdentity.lean | 24 | `fundamental_identity` | floor property ⌊x - n⌋ = ⌊x⌋ - n | 5-8 | Moderate |
| Lemma21_FundamentalIdentity.lean | 84 | `setA_measure` | measure of union of intervals | 20-40 | Medium |
| Lemma41_PositiveMeasure.lean | 29 | (Lipschitz continuity) | circDist composition is Lipschitz | 5-10 | Moderate |
| Lemma41_PositiveMeasure.lean | 47 | (division inequality) | 1/(n-1) > 1/n | 2-5 | Easy |
| Lemma41_PositiveMeasure.lean | 97 | (measure of interval) | μ(∩) > 0 from interval containment | 3-5 | Easy |
| Theorem71_LargeSR.lean | 28 | `bad_intervals_off_I` | bad set structure + covering | 8-12 | Medium |
| Theorem71_LargeSR.lean | 41 | `theorem71_largeSR` | bad set covers interval | 10-15 | Medium |
| Theorem71_LargeSR.lean | 60 | (corollary) | non-empty from ¬badSet | 2-3 | Easy |

**Reclassifications possible**: Could move Defs.lean:78 (goodSet_measurable) here if `measurable_fract` exists in Mathlib.

---

## Bucket (c): Genuinely Hard (~265-440 lines, 5-10 hours)

These are load-bearing; many depend on Theorem 5.2. Require substantial proof work.

### Tier C1: Core Mathematical Blockers (the real work)

| File | Line | Theorem | Issue | Est. LOC | Dependency |
|------|------|---------|-------|---------|------------|
| Defs.lean | 78 | `goodSet_measurable` | Int.fract measurable + preimage | 5-10 | Mathlib API |
| Theorem52_Weyl.lean | 72 | `jointGoodSet_periodic` | periodicity from individual periods | 5-10 | Finset.lcm |
| Theorem52_Weyl.lean | 92 | `fract_equidistributed_one_period` | **CORE**: equidistribution via coprimality | 30-60 | **PRIMARY BLOCKER** |
| Theorem52_Weyl.lean | 120 | `theorem52_weyl` | **CORE**: combine periodicity + equidistribution | 20-40 | fract_equidist |
| Theorem101_DI.lean | 40 | `setA_DI_measure` | measure with divisor structure | 20-30 | setA_measure |
| Theorem101_DI.lean | 51 | `DI_goodSet_rewrite` | rewrite via circDist_fundamental | 10-20 | fundamental_id |
| Theorem101_DI.lean | 61 | `theorem101_DI` | apply Theorem 5.2 + rewrite | 20-30 | theorem52_weyl |

### Tier C2: Induction and Assembly

| File | Line | Theorem | Issue | Est. LOC | Dependency |
|------|------|---------|-------|---------|------------|
| Lemma41_PositiveMeasure.lean | 47 | (apply H(n-1)) | type-match induction hypothesis | 10-20 | intLRC |
| Theorem111_ModDI.lean | 44 | `modified_divisor_reduces_to` | cardinality + coprimality | 15-25 | custom |
| Theorem111_ModDI.lean | 66 | (apply H(r+2)) | induction wiring (smaller instance) | 10-15 | intLRC |
| Theorem111_ModDI.lean | 89 | `theorem111_ModDI` | 5-step proof with Theorem 5.2 | 30-50 | theorem52_weyl |
| Theorem121_Main.lean | 71 | `theorem121_LRC` | **MAIN ASSEMBLY**: strong induction + case exhaustion | 40-60 | All sub-theorems |
| Theorem121_Main.lean | 92 | `theorem121_LRC_real` | rational approximation + continuity | 30-50 | custom |

---

## Critical Path to Completion

### Phase 1: THEOREM 5.2 (Weyl/CRT measure lemma)
**Status**: Primary blocker for Tier 2 (hard case)
**Effort**: 50-100 lines total (equidistribution approach, NOT explicit bijection)
**Blocking**: Theorems 10.1, 11.1 (DI and ModDI cases)
**Implementation**:
1. Fix `jointGoodSet_periodic` (5-10 lines) — standard periodicity argument
2. Implement `fract_equidistributed_one_period` (30-60 lines) — core mathematical step via coprimality
3. Complete `theorem52_weyl` (20-40 lines) — Fubini-style integration over periods

**Pre-research needed** (before session):
- Check Mathlib for `Nat.Coprime.eq_of_modeq` (CRT factorization)
- Check for `Finset.sum_nbij` (finite-sum bijection argument)
- These avoid full product-measure machinery

### Phase 2: Downstream Assembly (after Theorem 5.2 ✓)
Once Theorem 5.2 is proved:
- Theorem101_DI.lean (DI case): ~50-70 lines
- Theorem111_ModDI.lean (ModDI case): ~60-90 lines
- Theorem121_Main.lean (main assembly): ~40-60 lines

### Phase 3: Cleanup (bucket b + remaining Mathlib APIs)
~55-90 lines of straightforward math across 8 theorems

---

## Session Workflow Recommendation

1. **Next session (Theorem 5.2 focused)**:
   - Search Mathlib for `Nat.Coprime.eq_of_modeq`, `Finset.sum_nbij`
   - Implement 3 core lemmas (periodicity, equidistribution, integration)
   - Verify compile with `lake build` after each step

2. **Following session (downstream)**:
   - Theorems 101, 111 proofs (depend on 5.2 ✓)
   - Main assembly (121)

3. **Final session (cleanup)**:
   - Bucket (b) straightforward proofs
   - Polish + full build verification

---

## Key Mathlib Gaps Identified

| Lemma | Status | Workaround |
|-------|--------|-----------|
| `measurable_fract` | Unknown (bucket a API) | Check Mathlib.MeasureTheory.Measurable |
| `Int.fract_add_int` / `Int.floor_sub_int` | Present in 4.29.1 | Use for Lemma 2.1 |
| `Nat.Coprime.eq_of_modeq` | Unknown | Critical for Theorem 5.2 |
| `Finset.sum_nbij` | Present (v4.29.1) | Finite-sum bijection |
| CRT measure-preserving bijection | NOT direct lemma | Build from primitives |

---

## Build Metrics (post-bucket-a)
- **Total files**: 9 (all in LonelyRunner/LRC/)
- **Sorries remaining**: 19
- **Build status**: ✓ Passing (exit code 0)
- **Compilation time**: ~2 min (full rebuild)
- **Type-checking**: ✓ All files type-check correctly
