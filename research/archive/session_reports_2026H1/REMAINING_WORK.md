# Remaining Work — 3 Sorries

## Current State
- **File**: `/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunner/LRC/Theorem52_Weyl.lean`
- **Total sorries**: 3
- **File size**: 746 lines
- **Overall completion**: 80%

---

## Sorry 1: Finset Cardinality (Line 602)

**Location**: Inside `fract_equidistributed_one_period`, proof of `sum_factorization`

**Current code** (simplified):
```lean
have card_eq : Finset.card {m : Fin (L * p) | m.val % L = 0}.toFinset = p := by
  -- The elements with m.val ≡ 0 (mod L) in Fin(Lp) are m.val ∈ {0, L, 2L, ..., (p-1)L}
  -- In [0, Lp), there are exactly p multiples of L: 0, L, 2L, ..., (p-1)L
  have bij : Finset.card (Finset.filter (fun m : Fin (L * p) => m.val % L = 0)
                                         (Finset.univ : Finset (Fin (L * p)))) = p := by
    -- The map k ↦ ⟨k * L, by omega⟩ is a bijection from Fin p to filtered set
    sorry  -- Bijection via k ↦ k * L
  simp only [← Finset.filter_univ] at bij
  exact bij
```

**What needs to be proved**:
- The bijection from Fin p to the set {m : Fin(Lp) | m.val % L = 0}
- via the map k ↦ ⟨k * L, proof that k*L < Lp⟩
- Use `Finset.card_image_of_injective` or similar

**Mathlib lemmas to use**:
- `Finset.card_filter`
- `Finset.card_image_of_injective`
- Fin arithmetic lemmas
- `Nat.mul_lt_mul_of_pos_right`

**Difficulty**: Medium (finset/fin manipulation, not deep theory)

---

## Sorry 2: CRT Measure Factorization (Line 627)

**Location**: Inside `fract_equidistributed_one_period`, proof of `sum_factorization`

**Current code**:
```lean
have crt_factorization : (∑ m in {m : Fin (L * p) | m.val % L = 0}.toFinset,
    MeasureTheory.volume (cell m ∩ {t | Int.fract ((p : ℝ) * t) ∈ A})) =
    ENNReal.ofReal (1 / L : ℝ) * MeasureTheory.volume A := by
  -- Argument:
  -- On the p cells with m ≡ 0 (mod L), the values m mod p are {0, 1, ..., p-1}
  -- On each such cell, {p*t} depends only on m mod p (by the cell structure)
  -- So as we sum over all p cells, {p*t} uniformly covers [0, 1)
  -- Hence: ∑_m (measure of cell_m ∩ {fract ∈ A})
  --      = (measure of p cells) * P(fract ∈ A)
  --      = (1/L) * μ(A)
  sorry  -- By CRT independence: the sum factors as (1/L) * μ(A)
```

**What needs to be proved**:
- For cells with m ≡ 0 (mod L), as m mod p ranges over {0, 1, ..., p-1}:
- The fractional parts {p*t} are uniformly distributed
- Therefore: ∑_m (measure of cell_m ∩ {fract ∈ A}) = (1/L) * μ(A)

**Key insight**:
- Total measure of p cells = 1/L ✓ (already computed)
- On each cell m, {p*t} depends only on m mod p ✓ (cell_fract_props)
- Since m mod p takes each value exactly once across the p cells:
  - {p*t} uniformly covers [0, 1)
  - So the intersection measure factors as (1/L) * μ(A)

**Mathlib lemmas to use**:
- `MeasureTheory.measure_inter`
- `Finset.sum_congr`
- Product measure / measure independence (if available)
- Might need to implement custom decomposition

**Difficulty**: Hard (deep measure theory, may require careful setup)

---

## Sorry 3: Periodicity Decomposition (Line 711)

**Location**: Inside `theorem52_weyl`, main proof

**Current code**:
```lean
have period_decomp : MeasureTheory.volume
    ({t ∈ jointGoodSet speeds n | Int.fract ((p : ℝ) * t) ∈ A}) =
    MeasureTheory.volume (jointGoodSet speeds n) *
    MeasureTheory.volume A := by
  -- Key steps:
  -- 1. Use hG_periodic to express each coset measure
  -- 2. Use heq_dist to apply equidistribution within each coset
  -- 3. Sum over L cosets to obtain final result
  sorry  -- The decomposition over periods and application of equidistribution
```

**What needs to be proved**:
- μ({t ∈ G : fract(p*t) ∈ A}) = μ(G) * μ(A)
- where G = jointGoodSet is periodic with period 1/L

**Proof strategy**:
1. Use periodicity lemma `hG_periodic` to show G has period 1/L
2. Decompose [0, 1) into L periods: [0, 1/L), [1/L, 2/L), ..., [(L-1)/L, 1)
3. For each period [k/L, (k+1)/L):
   - By periodicity: μ(G ∩ [k/L, (k+1)/L)) = μ(G ∩ [0, 1/L))
   - Substitution u = t - k/L: {p*(t + k/L)} = {p*u} (since {p*k/L} is integer)
   - So measure distribution is identical to [0, 1/L)
4. Apply `fract_equidistributed_one_period` result to each coset
5. Sum over L cosets:
   - μ({t ∈ G : fract ∈ A}) = ∑_k μ({t ∈ G ∩ coset_k : fract ∈ A})
   - = ∑_k μ(G ∩ coset_k) * μ(A) / (measure of coset)
   - = μ(G) * μ(A)

**Key lemmas already available**:
- `hG_periodic` : G has period 1/L ✓
- `heq_dist` : equidistribution on [0, 1/L) ✓
- `jointGoodSet_periodic` : periodicity proved ✓

**Mathlib lemmas to use**:
- `MeasureTheory.measure_biUnion_finset`: Finset union measure
- Period/translation properties
- `Finset.sum_` for measure composition
- Possibly `MeasureTheory.tendsto_measure_` for limit arguments

**Difficulty**: Hardest (requires careful measure decomposition and scaling)

---

## Strategy for Completion

### Phase 1: Cardinality (30 minutes)
1. Construct finset bijection k ↦ k*L
2. Use `Finset.card_image_of_injective`
3. Should be straightforward once finset machinery is understood

### Phase 2: CRT Factorization (60 minutes)
1. Establish measure decomposition formula
2. Apply cell structure (m mod p coverage)
3. Use finset sum to combine measures
4. Might require custom measure lemmas

### Phase 3: Periodicity (90+ minutes)
1. Decompose [0, 1) into L periods
2. For each period, verify {p*(t + k/L)} = {p*t}
3. Apply equidistribution result from fract_equidistributed_one_period
4. Sum via `MeasureTheory.measure_biUnion_finset`
5. Verify algebra: L * period_measure = total measure

---

## Quick Reference

**File path**: 
```
/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/LonelyRunner/LRC/Theorem52_Weyl.lean
```

**Line numbers**:
- Sorry 1: 602
- Sorry 2: 627
- Sorry 3: 711

**Surrounding context**:
- All three sorries are "inside" larger proofs
- Can be completed independently once the structural setup is understood
- No circular dependencies

---

## Testing Checklist

After filling each sorry:
- [ ] File structure looks correct (indentation, parentheses)
- [ ] Lemma statement matches what's being proved
- [ ] Proof doesn't introduce new sorries
- [ ] Type signatures are compatible
- [ ] Can attempt `lake build` for syntax check

---

## Notes for Next Session

1. **Start with Sorry 1** (cardinality) — it's the most straightforward
2. **Document the measure decomposition carefully** in Sorry 2 to avoid getting lost
3. **Use the periodicity lemma** directly in Sorry 3 rather than reproving it
4. **If stuck on measure theory**, consider whether there's a simpler argument that avoids the deepest Mathlib lemmas

---

End of remaining work document.

