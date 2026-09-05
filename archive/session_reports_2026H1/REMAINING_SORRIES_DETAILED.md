# Remaining Sorries — Detailed Inventory

**File**: `Theorem52_Weyl.lean`  
**Total sorries**: 14 (down from 50+ at session start)  
**Session progress**: ~72% complete (structure done, 72% of proofs filled)

---

## Sorted by Line Number

### SORRY #1 (Line 159)
**Location**: `crt_map_injective` lemma  
**Context**: Proving injectivity of CRT map via coprimality  
**What needs to be shown**:
```
By CRT: k_p = k_L = 0 (since gcd(p,L)=1 forces t₁ = t₂)
```
**Difficulty**: 🟡 Medium  
**Key insight**: Use Bézout identity: since gcd(p,L)=1, there exist u,v such that u*p + v*L = 1  
**Estimated time**: 15-20 mins  
**Mathlib lemmas needed**: `Nat.gcdA_eq_gcd_a`, `Int.mod_eq_iff_lt` or similar  

---

### SORRY #2 (Line 207)
**Location**: `crt_index_bijection` lemma, surjectivity  
**Context**: Constructing m given (a,b) residues via CRT  
**What needs to be shown**:
```
∃ m ∈ {0,...,Lp-1} such that m ≡ a (mod L) and m ≡ b (mod p)
```
**Difficulty**: 🟡 Medium  
**Key insight**: Use `ZMod.chineseRemainder` to construct witness, then lift back to Nat  
**Estimated time**: 10-15 mins  
**Mathlib lemmas needed**: `ZMod.chineseRemainder`, `Fin.mk`  

---

### SORRY #3 (Line 208)
**Location**: `crt_index_bijection` lemma, surjectivity  
**Context**: Proving constructed m has correct residues  
**What needs to be shown**:
```
The m from ZMod.chineseRemainder satisfies m ≡ a (mod L) and m ≡ b (mod p)
```
**Difficulty**: 🟡 Medium  
**Key insight**: Properties of `ZMod.chineseRemainder` guarantee this  
**Estimated time**: 5-10 mins  
**Mathlib lemmas needed**: `ZMod.chineseRemainder_left_mk`, `ZMod.chineseRemainder_right_mk`  

---

### SORRY #4 (Line 256)
**Location**: `cell_fract_props`, first branch  
**Context**: Showing {p*t} ∈ [(m mod L)/L, (m mod L + 1)/L)  
**What needs to be shown**:
```
From bounds: (m%L)/L + (m/L) ≤ p*t < ((m%L)+1)/L + (m/L)
Conclude: {p*t} = p*t - ⌊p*t⌋ ∈ [(m%L)/L, ((m%L)+1)/L)
```
**Difficulty**: 🟡 Medium  
**Key insight**: ⌊p*t⌋ = ⌊(m%L)/L + (m/L)⌋ = m/L (since (m%L)/L < 1)  
**Estimated time**: 15-20 mins  
**Mathlib lemmas needed**: `Nat.floor_add`, `Int.fract_eq_iff_lt`  

---

### SORRY #5 (Line 257)
**Location**: `cell_fract_props`, first branch, closing brace  
**Context**: Second component of the conjunction  
**What needs to be shown**:
```
The {L*t} bound (second part of cell_fract_props)
```
**Difficulty**: ✓ Trivial  
**Key insight**: Should fall out automatically from constructing the first part  
**Estimated time**: 1 min  
**Mathlib lemmas needed**: None (structure)  

---

### SORRY #6 (Line 272)
**Location**: `cell_fract_props`, second branch  
**Context**: Showing {L*t} ∈ [(m mod p)/p, (m mod p + 1)/p)  
**What needs to be shown**:
```
From bounds: (m%p)/p + (m/p) ≤ L*t < ((m%p)+1)/p + (m/p)
Conclude: {L*t} ∈ [(m%p)/p, ((m%p)+1)/p)
```
**Difficulty**: 🟡 Medium  
**Key insight**: Mirror of SORRY #4, but with L and p roles swapped  
**Estimated time**: 15-20 mins  
**Mathlib lemmas needed**: Same as SORRY #4  

---

### SORRY #7 (Line 365)
**Location**: `measure_factored`, in union_period proof  
**Context**: Cell membership via floor function  
**What needs to be shown**:
```
t ∈ [m/(Lp), (m+1)/(Lp)) where m = ⌊t*(Lp)⌋
```
**Difficulty**: 🟡 Medium  
**Key insight**: Standard floor function property: ⌊x⌋ ≤ x < ⌊x⌋ + 1  
**Estimated time**: 10-15 mins  
**Mathlib lemmas needed**: `Nat.floor_le`, `Nat.lt_floor_add_one`  

---

### SORRY #8 (Line 381)
**Location**: `measure_factored`, union_period proof  
**Context**: Finding m with mod L = 0 constraint  
**What needs to be shown**:
```
For t ∈ [0, 1/L), there exists unique m with m ≡ 0 (mod L) and t ∈ cell m
```
**Difficulty**: 🔴 Hard  
**Key insight**: The cells {0, p, 2p, ..., (p-1)p} partition [0, 1/L); find which one contains t  
**Estimated time**: 20-30 mins  
**Mathlib lemmas needed**: Modular arithmetic, finset filtering  

---

### SORRY #9 (Line 393)
**Location**: `measure_factored`, intersection_dist proof  
**Context**: Finding m in set membership  
**What needs to be shown**:
```
From union_period, extract m such that t ∈ cell m and m ≡ 0 (mod L)
```
**Difficulty**: 🟡 Medium  
**Key insight**: Follows directly from union_period; just extract witness  
**Estimated time**: 5-10 mins  
**Mathlib lemmas needed**: Set operations (mem_iUnion)  

---

### SORRY #10 (Line 397)
**Location**: `measure_factored`, intersection_dist proof  
**Context**: Backward direction of set equality  
**What needs to be shown**:
```
If t ∈ cell m and m ≡ 0 (mod L), then t ∈ [0, 1/L)
```
**Difficulty**: ✓ Trivial  
**Key insight**: Cells with m ≡ 0 (mod L) are all in [0, 1/L) by union_period  
**Estimated time**: 2-5 mins  
**Mathlib lemmas needed**: None (structural)  

---

### SORRY #11 (Line 398)
**Location**: `measure_factored` main  
**Context**: Measure decomposition via Finset sum  
**What needs to be shown**:
```
μ({t ∈ [0,1/L) : {p*t} ∈ A}) = ∑_m μ(cell_m ∩ {t : {p*t} ∈ A})
```
**Difficulty**: 🔴 Hard  
**Key insight**: Measure additivity over disjoint union of cells  
**Estimated time**: 20-30 mins  
**Mathlib lemmas needed**: `MeasureTheory.measure_biUnion_finset`, measure additivity  

---

### SORRY #12 (Line 402)
**Location**: `sum_factorization`  
**Context**: CRT symmetry argument for measure sum  
**What needs to be shown**:
```
∑_m (1/(Lp)) * μ(A ∩ interval_m) = (1/L) * μ(A)
using CRT index bijection and equidistribution
```
**Difficulty**: 🔴 Hard  
**Key insight**: CRT bijection ensures symmetric distribution across the p cells  
**Estimated time**: 30-40 mins  
**Mathlib lemmas needed**: `crt_index_bijection`, finset sum properties  

---

### SORRY #13 (Line 443)
**Location**: `theorem52_weyl`  
**Context**: Speed positivity assumption  
**What needs to be shown**:
```
∀ j, 0 < speeds j
```
**Difficulty**: ✓ Trivial  
**Key insight**: By LRC definition, speeds are positive integers  
**Estimated time**: 1-2 mins  
**Mathlib lemmas needed**: Context assumption (should be available)  

---

### SORRY #14 (Line 458)
**Location**: `theorem52_weyl` main  
**Context**: Measure decomposition via periodicity  
**What needs to be shown**:
```
Decompose [0,1) into cosets modulo period 1/L
Apply equidistribution to each coset
Sum over L cosets to get μ(G) * μ(A)
```
**Difficulty**: 🔴 Hard  
**Key insight**: Periodicity allows factoring out the period; equidistribution applies uniformly  
**Estimated time**: 30-45 mins  
**Mathlib lemmas needed**: Period structure, measure scaling  

---

## Summary by Difficulty

| Difficulty | Count | Est. Total Time |
|------------|-------|-----------------|
| ✓ Trivial (1-2 mins) | 3 | ~5 mins |
| 🟡 Medium (10-25 mins) | 6 | ~90 mins |
| 🔴 Hard (20-45 mins) | 5 | ~160 mins |
| **TOTAL** | **14** | **~255 mins ≈ 4.25 hours** |

---

## Recommended Completion Order

1. **Quick wins** (10 mins): Sorries #13, #5, #10 (trivial context/structure)
2. **Medium arithmetic** (90 mins): Sorries #4, #6, #7, #9, #2, #3 (floor functions, modular)
3. **Hard theory** (160 mins): Sorries #1, #8, #11, #12, #14 (CRT, measure, periodicity)

---

## Key Mathlib Lemmas to Investigate

| Lemma | Purpose |
|-------|---------|
| `Nat.floor_le` | Lower bound for floor: ⌊x⌋ ≤ x |
| `Nat.lt_floor_add_one` | Upper bound: x < ⌊x⌋ + 1 |
| `Int.fract_eq_iff_lt` | Characterizing fractional part |
| `ZMod.chineseRemainder` | Explicit CRT witness construction |
| `MeasureTheory.measure_biUnion_finset` | Finset-indexed measure unions |
| `Nat.Coprime.eq_mod_of_eq_mod_left` | CRT injectivity |
| `Set.iUnion_ite` or similar | Union of conditional sets |

---

## Next Session Quick-Start Checklist

- [ ] **Fill Sorries #13, #5, #10** (5-10 mins, warm-up)
- [ ] **Research Mathlib floor/fractional lemmas** (10 mins)
- [ ] **Fill Sorries #4, #6** (floor arithmetic, 30-40 mins)
- [ ] **Fill Sorries #7, #9** (floor membership, 15-25 mins)
- [ ] **Fill Sorries #2, #3** (ZMod.chineseRemainder, 15-20 mins)
- [ ] **Fill Sorry #1** (Bézout + bounds, 15-20 mins)
- [ ] **Fill Sorries #8, #11, #12, #14** (Hard theory, 120-160 mins)

**Target**: 2-3 focused hours to completion

---

## Checkpoint Files Generated This Session

- `ROUTE_B_COMPLETION_STATUS.md` — Sorry-by-sorry assessment
- `ROUTE_B_SESSION_SUMMARY.md` — High-level progress overview
- `REMAINING_SORRIES_DETAILED.md` — This file (detailed inventory)

---

## Status

✅ **Architecture**: 100% complete  
✅ **Proof structure**: 90% complete  
⏳ **Proof details**: 60-70% complete  
⏳ **Sorries remaining**: 14 (bounded, well-understood)  

**Confidence**: High — remaining work is standard technique, not novel mathematics.
