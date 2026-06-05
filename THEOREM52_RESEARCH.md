# Theorem 5.2 — Research & Implementation Strategy
**Date**: 2026-05-22  
**Status**: Pre-implementation research phase  
**Mathlib Version**: 4.29.1  

---

## Executive Summary

Theorem 5.2 (Integer-Speed Equidistribution / CRT Measure Lemma) is the critical dependency for Theorems 10.1 and 11.1. The proof requires three sequential lemmas:

1. **jointGoodSet_periodic** (5-10 lines) — G has period 1/L
2. **fract_equidistributed_one_period** (30-60 lines) — core CRT step [HARD]
3. **theorem52_weyl** (20-40 lines) — measure factorization via Fubini
4. **theorem52_nonempty** (2-5 lines) — positive measure → non-empty

This document captures the mathematical structure and Mathlib lookup strategy.

---

## Mathematical Content (from manuscript §5.2)

### Theorem 5.2 Statement
Given:
- Positive integers v₁, ..., v_k with lcm L
- G = {t ≥ 0 : ‖v_i * t‖ ≥ 1/n for all i} with μ(G) > 0
- Positive integer p with gcd(p, L) = 1
- Measurable set A ⊆ [0,1) with μ(A) > 0

Conclude: μ({t ∈ G : {p*t} ∈ A}) = μ(G) · μ(A) > 0

### Proof Structure (Manuscript)

**Step 1: Periodicity**
- Each goodSet v_i has period 1/v_i (Lipschitz argument or direct)
- Joint set G has period lcm(1/v₁, ..., 1/v_k) = 1/L
- Algebraic: lcm of divisors = 1/gcd of base numbers

**Step 2: CRT Bijection (KEY)**
The function φ: [0, 1/(Lp)) → [0, 1/L) × [0, 1/p) defined by
```
φ(t) = (t mod 1/L, t mod 1/p) = (Int.fract(L*t)/L, Int.fract(p*t)/p)
```
is a **measure-preserving bijection** when gcd(p,L)=1.

This is the Chinese Remainder Theorem for real intervals:
- For any (s, u) ∈ [0,1/L) × [0,1/p), the system t≡s (mod 1/L), t≡u (mod 1/p) has unique solution t ∈ [0, 1/(Lp))
- Both sides have measure 1/(Lp), so the bijection preserves measure

**Step 3: Factorization via Fubini**
- 1_G(t) depends only on t mod 1/L (periodicity of G)
- 1_A({p*t}) depends only on t mod 1/p (periodic condition on {p*t})
- Therefore:
  ```
  ∫₀^(1/(Lp)) 1_G(t) · 1_A({p*t}) dt 
  = ∫₀^(1/L) ∫₀^(1/p) 1_G(s) · 1_A({p*u}) ds du   [by φ]
  = [∫₀^(1/L) 1_G(s) ds] · [∫₀^(1/p) 1_A({p*u}) du]  [by Fubini]
  = [μ(G)/L] · [μ(A)/p]
  ```
- Scaling back: μ(G ∩ {p*t ∈ A}) = μ(G) · μ(A) > 0

---

## Mathlib 4.29.1 — Available Components

### 1. Nat.Coprime (AVAILABLE)
**Location**: Mathlib.Data.Nat.GCD.Basic
**Key lemmas**:
- `Nat.Coprime p L` — already used in project
- `Nat.Coprime.symm` — commutativity
- `Nat.coprime_iff_gcd_eq_one` — equivalence to gcd

**Usage in project**: Already imported and used in Theorem52_Weyl.lean lines 72-77

### 2. Int.fract Periodicity (AVAILABLE)
**Location**: Mathlib.Algebra.Order.Floor.Defs
**Key lemmas**:
- `Int.fract_add_one : Int.fract (x + 1) = Int.fract x`
- `Int.fract_nonneg : 0 ≤ Int.fract x`
- `Int.fract_lt_one : Int.fract x < 1`

**Usage in project**: goodSet_periodic (Defs.lean:87-95) uses `Int.fract_add_one`

### 3. Periodicity Combination (LIKELY AVAILABLE)
**Location**: Mathlib.Data.Finset.Lattice or Mathlib.Algebra.Lattice
**Key lemmas**:
- `Finset.lcm` — lcm of a finite set
- Periodicity composition lemma (if 1/v₁ and 1/v₂ periods, then 1/lcm(v₁,v₂) is period)

**Strategy**: Build recursively using lcm of two periods, extend via Finset.lcm

### 4. Measure Theory (AVAILABLE)
**Location**: Mathlib.MeasureTheory.Measure.Lebesgue.Basic, Mathlib.MeasureTheory.Integral.Bochner.Basic
**Key lemmas**:
- `MeasureTheory.volume : Measure ℝ` — Lebesgue measure
- `MeasureTheory.Measure.prod : Measure (α × β)` — product measure
- `Real.volume_Icc : volume (Icc a b) = ofReal (max 0 (b - a))`
- `MeasureTheory.integral_prod_mul` — Fubini's theorem (or similar)

**Assessment**: Product measure and Fubini **likely exist but need API verification**

### 5. CRT / Chinese Remainder Theorem (PARTIAL)
**Location**: Mathlib.Data.ZMod.Basic
**Key lemmas**:
- `ZMod.chineseRemainder` — algebraic CRT bijection
- `ZMod.modEq_iff_dvd` — modular congruence

**Assessment**: 
- **Algebraic CRT**: ZMod.chineseRemainder provides the bijection on ZMod
- **Lifting to reals**: Requires custom work to lift φ : [0, 1/(Lp)) → ℝ × ℝ using Int.fract
- **Measure-preserving**: Not directly in Mathlib; must prove via Lebesgue measure properties

---

## Implementation Plan: Four Lemmas in Sequence

### Lemma 1: jointGoodSet_periodic (5-10 lines)
**Goal**: Prove G has period 1/L

**Approach**:
```lean
theorem jointGoodSet_periodic {k : ℕ} (speeds : Fin k → ℕ) (n : ℕ) 
    (hpos : ∀ j, 0 < speeds j) (L : ℕ) (hL : L = Finset.lcm Finset.univ speeds) :
    ∀ t : ℝ, jointGoodSet speeds n t ↔ jointGoodSet speeds n (t + 1 / L) := by
  intro t
  -- unfold jointGoodSet and goodSet
  simp only [jointGoodSet, goodSet, Set.mem_iInter, Set.mem_setOf_eq]
  -- For each i, apply goodSet_periodic, which says each has period 1/speeds_i
  -- L = lcm(speeds), so 1/L is lcm of all individual periods
  -- Therefore, t + 1/L is in each goodSet iff t is
  constructor <;> intro h
  · intro i
    have : speeds i ∣ L := Finset.dvd_lcm (Finset.mem_univ i)
    -- 1/(speeds i) is a multiple of 1/L, so if t has period 1/L, it has period 1/(speeds i)
    sorry
  · intro i
    sorry
```

**Mathlib needed**: 
- `Finset.dvd_lcm` — lcm divides all members
- Periodicity composition (if period τ and 1/v | τ, then t + 1/v ∈ set iff t ∈ set)

---

### Lemma 2: fract_equidistributed_one_period (30-60 lines) [CRITICAL]
**Goal**: Prove equidistribution of p*t mod 1 when gcd(p,L)=1

**Approach (Implicit, via measure-theoretic properties)**:
```lean
theorem fract_equidistributed_one_period
    (L p : ℕ) (hcop : Nat.Coprime p L) (hL_pos : 0 < L) (hp_pos : 0 < p)
    (A : Set ℝ) (hA_meas : MeasurableSet A) :
    MeasureTheory.volume {t ∈ Set.Icc (0 : ℝ) (1 / L) | Int.fract ((p : ℝ) * t) ∈ A} =
    ENNReal.ofReal (1 / L : ℝ) * MeasureTheory.volume A := by
  -- STRATEGY: Use the CRT bijection φ : [0, 1/(Lp)) → [0, 1/L) × [0, 1/p)
  -- Define φ(t) = (Int.fract(L*t) / L, Int.fract(p*t) / p)
  -- Show it's a measure-preserving bijection via Nat.Coprime
  -- Then integral = ∫ 1_A({p*u}) du over [0, 1/p) by Fubini
  -- and ∫ 1_A({p*u}) du = μ(A) by substitution u' = p*u
  sorry
```

**This is the hard step.** Two possible routes:

**Route A: Explicit bijection (heavier but rigorous)**
- Construct φ explicitly using Int.fract
- Prove it's bijective via Nat.Coprime (using ZMod.chineseRemainder as template)
- Prove measure-preserving (both sides have measure 1/(Lp))
- Apply Fubini to factor the integral
- **Estimate**: 60-100 lines

**Route B: Implicit via coprimality (lighter, user-suggested)**
- Use Nat.Coprime to argue that p · [0, 1/L) wraps around [0, 1) uniformly
- Directly apply measure factorization property without explicit bijection
- **Estimate**: 30-50 lines

**Recommendation**: Start with Route B (user's suggestion). If blocked on Mathlib machinery, fall back to Route A.

---

### Lemma 3: theorem52_weyl (20-40 lines)
**Goal**: Combine periodicity + equidistribution to get the main measure factorization

**Approach**:
```lean
theorem theorem52_weyl {k : ℕ} (speeds : Fin k → ℕ) (n L p : ℕ)
    (hL : L = lcmSpeeds speeds)
    (hcop : Nat.Coprime p L) (hp : 0 < p) (hL_pos : 0 < L)
    (A : Set ℝ) (hA_meas : MeasurableSet A) (hA_pos : 0 < MeasureTheory.volume A)
    (hG_pos : 0 < MeasureTheory.volume (jointGoodSet speeds n)) :
    MeasureTheory.volume {t ∈ jointGoodSet speeds n | Int.fract ((p : ℝ) * t) ∈ A} =
    MeasureTheory.volume (jointGoodSet speeds n) * MeasureTheory.volume A := by
  -- Use periodicity to reduce to one period [0, 1/L)
  have hG_periodic := jointGoodSet_periodic speeds n (by sorry) L hL
  -- Use equidistribution on the period
  have heq_dist := fract_equidistributed_one_period L p hcop hL_pos hp A hA_meas
  -- Combine: scale equidistribution result by number of periods in [0, ∞)
  sorry
```

**Mathlib needed**:
- `Set.mulRestrict` or similar for restriction to periods
- Measure scaling lemmas for periodic functions

---

### Lemma 4: theorem52_nonempty (2-5 lines)
**Goal**: Positive measure implies non-empty

**Approach**:
```lean
theorem theorem52_nonempty {k : ℕ} (speeds : Fin k → ℕ) (n L p : ℕ)
    (hL : L = lcmSpeeds speeds)
    (hcop : Nat.Coprime p L) (hp : 0 < p) (hL_pos : 0 < L)
    (A : Set ℝ) (hA_meas : MeasurableSet A) (hA_pos : 0 < MeasureTheory.volume A)
    (hG_pos : 0 < MeasureTheory.volume (jointGoodSet speeds n)) :
    ∃ t₀ ∈ jointGoodSet speeds n, Int.fract ((p : ℝ) * t₀) ∈ A := by
  have h := theorem52_weyl speeds n L p hL hcop hp hL_pos A hA_meas hA_pos hG_pos
  -- Positive measure ⟹ set is non-empty
  by_contra hempty
  push_neg at hempty
  simp [Set.eq_empty_iff_forall_not_mem] at hempty
  -- Measure of empty set is zero, contradiction
  sorry
```

**Mathlib needed**:
- `MeasureTheory.measure_empty : volume ∅ = 0`
- Contrapositive of volume 0 ⟹ empty (or empty ⟹ volume 0)

---

## Critical Questions for Mathlib Lookup (Next Session)

Before implementation, search Mathlib 4.29.1 for:

1. **Periodicity composition**: If f has period τ and 1/v | τ, what's the name of "∀ t, f(t) = f(t + 1/v)"?
   - Check: `Set.periodic` or `Function.Periodic`
   - Need: composition of periodic functions

2. **Product measure and Fubini**: What's the exact name/signature?
   - Search: `MeasureTheory.integral_prod_mul` or variant
   - Check if it applies to our 1_G · 1_A setup

3. **Measure scaling by period**: If f has period τ and ∫₀^τ f = C, what's ∫₀^(nτ) f?
   - This is needed to scale from one period to all of ℝ₊

4. **Coprimality and modular bijection**: Can ZMod.chineseRemainder be lifted to reals?
   - Check documentation / examples in Mathlib

5. **Volume of empty set**: What's the exact lemma for "μ(∅) = 0"?
   - Search: `measure_empty` or `volume_empty`

---

## Risk Assessment & Mitigation

| Risk | Likelihood | Mitigation |
|------|------------|-----------|
| Periodicity composition lemma not named as expected | Medium | Search Mathlib docs; may need to prove manually (5-10 lines) |
| Product measure / Fubini requires non-standard setup | Medium | Use simpler substitution-based argument if Fubini is awkward |
| CRT bijection lift-to-reals is harder than expected | Medium | Fall back to Route A (explicit construct) if Route B stalls |
| Measure scaling lemma missing | Low | Prove by induction on number of periods |
| Volume zero ⟹ empty set is not directly available | Low | Use contrapositive or definitional expansion |

---

## Summary: Implementation Roadmap

**Session Start**:
1. Prove `jointGoodSet_periodic` (straightforward, depends on periodicity composition lemma)
2. Implement `fract_equidistributed_one_period` via Route B (coprimality + factorization)
3. Combine into `theorem52_weyl` (measure scaling + period union)
4. Conclude with `theorem52_nonempty` (measure > 0 ⟹ non-empty)

**If blocked**: 
- Route B fails → pivot to Route A (explicit bijection) 
- Missing periodicity composition → prove manually
- Fubini setup awkward → use direct substitution argument

**Expected outcome**: All 4 sorries closed, Theorem 5.2 fully proved, unblocking Theorems 10.1 and 11.1.

---

## Notes for Next Session

- Start with grep/search for exact Mathlib lemma names (especially Fubini variant, periodicity composition, measure scaling)
- Lean 4 type errors will guide which lemmas exist vs. need custom proofs
- Build incrementally: each lemma tested before moving to next
- Keep 10 remaining sorries (Theorems 10.1, 11.1, measurability) as-is until Theorem 5.2 proven
