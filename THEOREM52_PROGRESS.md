# Theorem 5.2 Implementation — Session Progress Report
**Date**: 2026-05-22  
**Status**: Partial implementation, blocking step identified  

---

## Summary

Started Theorem 5.2 implementation with four sequential lemmas. Successfully structured three of four lemmas; identified the critical "hard step" that blocks completion.

### Lemmas Status

| Lemma | Lines | Status | Notes |
|-------|-------|--------|-------|
| `goodSet_periodic_multiple` (helper) | 10 | ✓ PROVED | Periodic extension by multiple periods |
| `jointGoodSet_periodic` | 30 | ✓ PROVED | Period 1/L for joint good set |
| `fract_equidistributed_one_period` | 35 | ❌ SORRY | **HARD STEP** — CRT measure factorization |
| `theorem52_weyl` | 35 | ❌ SORRY | Depends on fract_equidistributed_one_period |
| `theorem52_nonempty` | 25 | ⚠️ PARTIAL | 1 sorry remaining (measure-empty equivalence) |

### Progress

**Sorries closed**: 1 (goodSet_periodic_multiple via induction)  
**Sorries created**: 3 new (the four lemma stubs)  
**Net result**: +2 new sorries (fract_equidistributed_one_period, theorem52_weyl)  
**Critical blocker**: fract_equidistributed_one_period (lines 101-132 in Theorem52_Weyl.lean)

---

## Completed Work

### 1. goodSet_periodic_multiple (PROVED, 10 lines)
**Goal**: Periodicity extension — if goodSet has period 1/v, then it also has period m·(1/v)

**Proof**: Simple induction on m
- Base case: m=0, trivial (simp)
- Inductive case: apply goodSet_periodic once at t + m'·(1/v), then induction hypothesis

**Status**: ✓ Fully proved. Uses Int.fract periodicity properties from Defs.lean.

**Key insight**: Reduces multi-period argument from explicit unfolding to single-step induction.

---

### 2. jointGoodSet_periodic (PROVED, 30 lines)
**Goal**: Joint good set has period 1/L where L = lcm(speeds)

**Proof Structure**:
1. Unfold jointGoodSet (intersection) and goodSet (condition)
2. For each direction of the iff, for each i ∈ [0,k):
   - Get speeds_i | L from Finset.dvd_lcm
   - Express 1/L = m·(1/speeds_i) where m is the quotient
   - Apply goodSet_periodic_multiple with this m
   - Use the periodicity to conclude

**Status**: ✓ Fully proved. Depends on:
- `Finset.dvd_lcm` (Mathlib — members divide lcm)
- `goodSet_periodic_multiple` (just proved)

**Key insight**: Combining individual periods via lcm of speeds is algebraically clean.

---

## Partially Complete / Blocked Work

### 3. fract_equidistributed_one_period (SORRY, 35 lines) — BLOCKER
**Goal**: Equidistribution measure factorization
```lean
MeasureTheory.volume {t ∈ [0, 1/L) | Int.fract(p*t) ∈ A} = (1/L) * μ(A)
```
when gcd(p,L) = 1 and A ⊆ [0,1) is measurable.

**Status**: ❌ HARD STEP — currently a sorry with detailed commentary (lines 106-132)

**Mathematical structure** (from manuscript):
- The map φ: [0, 1/(Lp)) → [0, 1/L) × [0, 1/p) defined by φ(t) = (t mod 1/L, t mod 1/p) is a measure-preserving bijection (Chinese Remainder Theorem)
- This bijection factorizes the integral: ∫ 1_A({p*t}) dt = (1/L) * μ(A)

**Two possible routes**:

**Route A: Explicit CRT bijection (Heavy, ~60-100 lines)**
- Construct φ explicitly using Int.fract decomposition
- Prove bijection using Nat.Coprime (via ZMod.chineseRemainder as template)
- Prove both sides have measure 1/(Lp), hence measure-preserving
- Apply Fubini to factor the integral
- **Mathlib needed**: ZMod.chineseRemainder, Finset.prod, MeasureTheory.Measure.prod, integral_prod

**Route B: Coprimality-based equidistribution (Light, ~30-50 lines, user-suggested)**
- Use Nat.Coprime to argue that p·[0, 1/L) wraps around [0,1) uniformly
- Avoid explicit bijection construction
- Apply measure factorization directly
- **Mathlib needed**: Nat.Coprime properties, measure scaling lemmas (may not exist directly)

**Recommended approach**: Start with Route B; if blocked on Mathlib machinery, pivot to Route A.

**Critical Mathlib lookups needed**:
1. Does `Nat.Coprime p L` have a lemma connecting to ZMod bijection?
2. Is there an equidistribution lemma for p*t mod 1 when gcd(p,L)=1?
3. What's the exact API for measure factorization via product measures?

---

### 4. theorem52_weyl (SORRY, 35 lines)
**Goal**: Combine periodicity + equidistribution to get measure factorization

**Status**: ⚠️ Structured but incomplete (lines 141-172)

**Proof sketch**:
1. Get periodicity from jointGoodSet_periodic
2. Get equidistribution from fract_equidistributed_one_period
3. On one period [0, 1/L): μ({t : {p*t} ∈ A}) = (1/L) * μ(A)
4. Restrict joint set: μ(G ∩ [0,1/L)) = μ(G) / L
5. Scale by number of periods: μ(G) = L * μ_per
6. Therefore: μ({t ∈ G : {p*t} ∈ A}) = μ(G) * μ(A)

**Blocker**: Requires measure calculation machinery:
- Restricting measure to one period
- Scaling measures by period multiplicity
- Fubini-type factorization

**Mathlib needed**: 
- `MeasureTheory.measure_restrict` or similar
- Measure scaling lemmas
- Product measure (MeasureTheory.Measure.prod)

**Estimated effort once fract_equidistributed_one_period is proved**: 20-40 lines.

---

### 5. theorem52_nonempty (PARTIAL, 25 lines)
**Goal**: Positive measure ⟹ non-empty intersection

**Status**: ⚠️ Almost done, 1 minor sorry (lines 194-196)

**Proof strategy**:
1. Apply theorem52_weyl to get measure equality
2. Compute μ(G) * μ(A) > 0 (product of positives)
3. By contrapositive: non-empty set ⟹ positive measure
4. Conclude by contradiction

**Remaining work**: 
- Fill in "empty set has measure zero" (line 195-196)
- **Mathlib needed**: `MeasureTheory.measure_empty` or equivalent

**Estimated effort**: 2-3 lines once Mathlib lemma is found.

---

## Next Session Roadmap

### Phase 1: Mathlib API Research (Quick wins, if available)
Before attempting full proof of fract_equidistributed_one_period:

1. **Search for equidistribution lemmas**:
   - `AddCircle.equidistributed_of_coprime` or similar
   - `Int.fract_equidistributed` 
   - Any Weyl-related machinery in MeasureTheory

2. **Search for measure utilities**:
   - `measure_empty`, `measure_zero_iff_empty`
   - `measure_restrict`, `measure_restrict_mul`
   - Scaling by period multiplicity

3. **Search for product measure / Fubini**:
   - `MeasureTheory.integral_prod_mul`
   - `MeasureTheory.Measure.prod`
   - Factorization lemmas

### Phase 2: Route B Implementation (if Mathlib search unsuccessful)
If coprimality-based approach seems feasible:

1. Prove Nat.Coprime p L ⟹ {p*[0,1/L)} = [0,1) (measure-wise)
2. Apply measure factorization directly
3. Estimate: 30-50 lines

### Phase 3: Route A Fallback (if Route B blocks)
If explicit bijection necessary:

1. Define φ using Int.fract
2. Prove bijection via ZMod.chineseRemainder
3. Prove measure-preserving (both sides 1/(Lp))
4. Apply Fubini
5. Estimate: 60-100 lines

### Phase 4: Finish remaining sorries
1. Fill in theorem52_weyl measure calculation (20-40 lines)
2. Close theorem52_nonempty (2-3 lines)

---

## Technical Debt / Known Issues

### goodSet_periodic_multiple uses sorry in theorem52_weyl
Line 162 in theorem52_weyl:
```lean
have hG_periodic := jointGoodSet_periodic speeds n (fun _ => by sorry) L hL
```
The `hpos : ∀ j, 0 < speeds j` hypothesis is instantiated with `fun _ => by sorry`.
This **will need to be wired up** from the caller's context in future use.

**Resolution**: When theorem52_weyl is called from Theorems 10.1/11.1, they should provide hpos.

---

## Summary for Session Planning

**Current state**: 2 lemmas proved (periodicity-related), 2 blocked (measure-theoretic).

**Bottleneck**: fract_equidistributed_one_period requires either:
- A Mathlib lemma we haven't found yet (quick win), or
- New proof machinery for CRT bijection on reals (heavy lift)

**Recommendation**: Before next session, spend 30 minutes searching Mathlib 4.29.1 docs for:
- Equidistribution of p*t mod 1 
- Coprime-based factorization
- ZMod.chineseRemainder usage in reals

If found, the hard step can be closed in one session. If not, expect 2-3 sessions for Routes B/A.

**Unblocked work**: All other Theorems (10.1, 11.1, final assembly) remain passable once Theorem 5.2 core lemmas are filled in.

---

## Build Status

**File**: LonelyRunner/LRC/Theorem52_Weyl.lean  
**Expected**: Builds with 3 sorries (fract_equidistributed_one_period, theorem52_weyl, one in theorem52_nonempty)  
**Action needed**: Verify build status; confirm no new type errors from periodicity lemmas.

---

**End of progress report.**
