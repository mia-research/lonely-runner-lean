# Implementation Paths for 3 Remaining Sorries

## Sorry 1: Finset Cardinality (Line 602)

**Complexity**: Low (~20 lines)  
**Status**: Most immediately closeable

### Approach 1: Via `Finset.card_product` (Recommended)
```lean
have card_eq : Finset.card {m : Fin (L * p) | m.val % L = 0}.toFinset = p := by
  -- The filtered set is bijective to Fin(p) via k ↦ k * L
  -- Use: |L ×ˢ p| = L * p (Finset.card_product)
  -- Then: bijectivity establishes |domain| = |codomain|
  
  -- Step 1: Establish product cardinality
  have prod_card : (Finset.range L ×ˢ Finset.range p).card = L * p := 
    Finset.card_product _ _
  
  -- Step 2: Build bijection from CRT
  have bij : Function.Bijective (fun m : Fin (L * p) => (m.val % L, m.val % p)) := by
    exact crt_index_bijection L p hL hp hcop  -- Already proved earlier
  
  -- Step 3: Count via bijection
  have : Finset.card {m : Fin (L * p) | m.val % L = 0}.toFinset = 
          (Finset.range p).card := by
    apply Finset.card_bij  -- Maps filtered set to Fin p
    sorry  -- The actual bijection k ↦ ⟨k * L, ...⟩
  
  simp only [Finset.card_range]; exact this
```

### Approach 2: Via `Finset.card_bij` with `ZMod.chineseRemainder`
```lean
have card_eq : Finset.card {m : Fin (L * p) | m.val % L = 0}.toFinset = p := by
  -- Direct bijection: k ↦ ZMod.chineseRemainder (of 0 and k)
  have bij : Function.Bijective (fun k : Fin p => 
    ⟨(ZMod.chineseRemainder hcop ⟨0, by omega⟩ ⟨k.val, by omega⟩), by omega⟩) := by
    sorry  -- Use Nat.Coprime to establish bijection
  apply Finset.card_bij bij
```

**Key lemmas**:
- `Finset.card_product`: |A ×ˢ B| = |A| * |B|
- `Finset.card_bij`: Bijection implies equal cardinality
- `Nat.Coprime.eq_mod_of_eq_mod_left`: CRT injectivity
- `ZMod.chineseRemainder`: CRT construction

---

## Sorry 2: CRT Measure Factorization (Line 627)

**Complexity**: High (~50-80 lines)  
**Status**: Core measure-theoretic work, unlocks Sorry 3

### Setup (Already In Place ✓)
```lean
have total_measure : (∑ m in {m : Fin (L * p) | m.val % L = 0}.toFinset,
    MeasureTheory.volume (cell m)) = ENNReal.ofReal (1 / L : ℝ) := by
  -- Already computed above
  sorry
```

### Direct Cell Decomposition Proof
```lean
have crt_factorization : (∑ m in {m : Fin (L * p) | m.val % L = 0}.toFinset,
    MeasureTheory.volume (cell m ∩ {t | Int.fract ((p : ℝ) * t) ∈ A})) =
    ENNReal.ofReal (1 / L : ℝ) * MeasureTheory.volume A := by
  
  -- Key observation: On each cell m with m ≡ 0 (mod L),
  -- fract(L*t) depends only on m mod L = 0 (constant)
  -- fract(p*t) depends only on m mod p (varying from 0 to p-1)
  
  -- Step 1: Rewrite sum as product over L × p values
  have cell_eq : ∀ m : Fin (L * p), m.val % L = 0 →
      (m.val % L : ℝ) = 0 := fun m h => by norm_num [Nat.mod_eq_of_lt (by omega : m.val % L < L)]
  
  -- Step 2: Apply cell_fract_props to extract fract(p*t) dependence on m mod p
  have fract_on_cell : ∀ m : Fin (L * p), m.val % L = 0 →
      ∀ t ∈ cell m, Int.fract ((p : ℝ) * t) ∈ Set.Ico ((m.val % p : ℝ) / p) (((m.val % p + 1 : ℕ) : ℝ) / p) := by
    intro m hm t ht
    exact (cell_fract_props m t ht).2
  
  -- Step 3: Recognize that as m ranges over cells with m ≡ 0 (mod L),
  -- the values m mod p cover {0, 1, ..., p-1} exactly once
  -- So fract(p*t) uniformly covers [0, 1)
  
  -- Step 4: Use Finset.sum_product' to decompose the sum
  have sum_eq : (∑ m in {m : Fin (L * p) | m.val % L = 0}.toFinset,
      MeasureTheory.volume (cell m ∩ {t | Int.fract ((p : ℝ) * t) ∈ A})) =
      (∑ k : Fin p, MeasureTheory.volume (cell ⟨k.val * L, by omega⟩ ∩ {t | Int.fract ((p : ℝ) * t) ∈ A})) := by
    sorry  -- Reindex the finset sum by k ↦ k*L
  
  rw [sum_eq]
  
  -- Step 5: For each k, the cell ⟨k*L, ...⟩ has measure 1/(Lp)
  --        and on it, fract(p*t) ∈ [(k/p), (k+1)/p)
  --        Integrate over A to get (1/(Lp)) * μ(A ∩ [k/p, (k+1)/p))
  
  -- Step 6: Sum over all k ∈ [0, p):
  --        ∑_k (1/(Lp)) * μ(A ∩ [k/p, (k+1)/p))
  --      = (1/(Lp)) * ∑_k μ(A ∩ [k/p, (k+1)/p))
  --      = (1/(Lp)) * μ(A)  [since the intervals partition [0,1)]
  --      = (1/(Lp)) * p * μ(A) / p
  --      = (1/L) * μ(A)
  
  have factored : (∑ k : Fin p, MeasureTheory.volume (cell ⟨k.val * L, by omega⟩ ∩ {t | Int.fract ((p : ℝ) * t) ∈ A})) =
                  ENNReal.ofReal (1 / L : ℝ) * MeasureTheory.volume A := by
    -- Use MeasureTheory.measure_restrict_apply for cell intersections
    -- Use Finset.sum_product' to reorganize sums
    sorry  -- Direct calculation using above structure
  
  exact factored
```

**Key lemmas**:
- `MeasureTheory.measure_restrict_apply`: Restrict measure to measurable set
- `Finset.sum_product'`: Reindex product sums
- `Finset.sum_bij`: Sum equality via bijection
- `MeasureTheory.volume_Ico_eq_sub`: Lebesgue measure of [a, b)
- `ENNReal.mul_eq_mul_left`: Cancel operations on ENNReal

**Critical insight**: Avoid `MeasureTheory.Measure.prod` entirely. The direct calculation via cells and finset products is cleaner.

---

## Sorry 3: Periodicity Decomposition (Line 711)

**Complexity**: Medium-High (~20-40 lines after Sorry 2)  
**Status**: Cleanest once Sorry 2 is available  
**Dependency**: Requires Sorry 2 to be filled first

### Proof Structure
```lean
sorry  -- The decomposition over periods and application of equidistribution
       -- requires measure-theoretic infrastructure (decompose into cosets,
       -- apply equidistribution to each, sum over finitely many cosets).

-- Once Sorry 2 is available, the proof is:

have period_decomp : MeasureTheory.volume
    ({t ∈ jointGoodSet speeds n | Int.fract ((p : ℝ) * t) ∈ A}) =
    MeasureTheory.volume (jointGoodSet speeds n) *
    MeasureTheory.volume A := by
  
  -- Step 1: Decompose [0, 1) into L periods
  have period_union : Set.Ico (0 : ℝ) 1 = ⋃ k : Fin L, 
    Set.Ico ((k.val : ℝ) / L) (((k.val + 1 : ℕ) : ℝ) / L) := by
    sorry  -- Standard period decomposition
  
  -- Step 2: Use periodicity of G
  have period_measure : ∀ k : Fin L,
    MeasureTheory.volume (jointGoodSet speeds n ∩ Set.Ico ((k.val : ℝ) / L) (((k.val + 1 : ℕ) : ℝ) / L)) =
    MeasureTheory.volume (jointGoodSet speeds n ∩ Set.Ico (0 : ℝ) (1 / L)) := by
    intro k
    -- Apply hG_periodic with translate t ↦ t + k/L
    apply MeasureTheory.measure_image_of_measurable
    sorry  -- Periodicity gives measure invariance
  
  -- Step 3: On each period, fract distribution is identical
  have fract_on_period : ∀ k : Fin L,
    MeasureTheory.volume ({t ∈ jointGoodSet speeds n ∩ Set.Ico ((k.val : ℝ) / L) (((k.val + 1 : ℕ) : ℝ) / L) | 
                           Int.fract ((p : ℝ) * t) ∈ A}) =
    MeasureTheory.volume (jointGoodSet speeds n ∩ Set.Ico (0 : ℝ) (1 / L)) * 
    MeasureTheory.volume A := by
    intro k
    -- On [k/L, (k+1)/L), the substitution u = t - k/L gives:
    -- fract(p*(u + k/L)) = fract(p*u + p*k/L) = fract(p*u) (since frac(p*k/L) is integer)
    -- So the equidistribution result heq_dist applies identically
    sorry  -- Use heq_dist with period shifted
  
  -- Step 4: Sum over all L periods
  have full_sum : MeasureTheory.volume
      ({t ∈ jointGoodSet speeds n | Int.fract ((p : ℝ) * t) ∈ A}) =
      ∑ k : Fin L, MeasureTheory.volume ({t ∈ jointGoodSet speeds n ∩ Set.Ico ((k.val : ℝ) / L) (((k.val + 1 : ℕ) : ℝ) / L) | 
                                         Int.fract ((p : ℝ) * t) ∈ A}) := by
    rw [← period_union]
    apply MeasureTheory.measure_iUnion
    sorry  -- Disjoint union measure decomposition
  
  rw [full_sum]
  
  -- Step 5: Apply fract_on_period to each term
  have term_eq : ∀ k : Fin L,
    MeasureTheory.volume ({t ∈ jointGoodSet speeds n ∩ Set.Ico ((k.val : ℝ) / L) (((k.val + 1 : ℕ) : ℝ) / L) | 
                           Int.fract ((p : ℝ) * t) ∈ A}) =
    MeasureTheory.volume (jointGoodSet speeds n ∩ Set.Ico (0 : ℝ) (1 / L)) * 
    MeasureTheory.volume A := fract_on_period
  
  -- Step 6: Sum factorization
  simp only [Finset.sum_congr rfl term_eq]
  rw [Finset.sum_mul]
  
  -- Step 7: Card(Fin L) = L
  simp only [Finset.sum_const, Finset.card_fin]
  ring_nf
  
  -- Step 8: Relate back to total μ(G)
  have total_measure : MeasureTheory.volume (jointGoodSet speeds n) =
    L * MeasureTheory.volume (jointGoodSet speeds n ∩ Set.Ico (0 : ℝ) (1 / L)) := by
    sorry  -- Sum of period measures equals total (by periodicity)
  
  rw [total_measure]
  ring
```

**Key lemmas**:
- `hG_periodic`: G has period 1/L (already available)
- `heq_dist`: Equidistribution on [0, 1/L) (already available)
- `MeasureTheory.measure_iUnion`: Disjoint union measure
- `MeasureTheory.measure_image_of_measurable`: Measure under measurable maps
- `Set.Ico`: Half-open intervals
- `Finset.sum_mul`, `ring`: Arithmetic on measure sums

**Critical insight**: The key step is showing that on each period [k/L, (k+1)/L), the substitution u = t - k/L gives {p*(u + k/L)} = {p*u} (since {p*k/L} is an integer), making the distribution identical to [0, 1/L).

---

## Priority & Dependencies

| Sorry | Difficulty | Prerequisites | Estimated lines | Can start immediately? |
|-------|-----------|---------------|-----------------|----------------------|
| 1 (Line 602) | Low | None | ~20 | YES |
| 2 (Line 627) | High | None (but builds on setup) | ~50-80 | YES (after 1) |
| 3 (Line 711) | Medium | Uses Sorry 2's result | ~20-40 | YES (after 2) |

**Recommended order**: 1 → 2 → 3 (sequential)

---

## Common Pitfalls to Avoid

1. **Sorry 1**: Don't compute cardinality manually; use finset/Fin lemmas
2. **Sorry 2**: Don't attempt `MeasureTheory.Measure.prod`; direct cell computation is simpler
3. **Sorry 3**: Ensure substitution u = t - k/L is handled correctly; `fract(p*u)` must match the equidistribution form

