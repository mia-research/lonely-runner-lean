# Theorem 5.2 — Decision Point: Path Forward

**Date**: 2026-05-22  
**Status**: Mathlib research complete; critical hard step identified; decision point reached  

---

## Current State

### What We've Built (✓ Complete)

1. **goodSet_periodic_multiple** — helper for multi-period periodicity
2. **jointGoodSet_periodic** — joint good set has period 1/L (lcm of speeds)
3. **theorem52_nonempty** — structure in place, 1 minor sorry remains

### The Blocker: fract_equidistributed_one_period

**Mathematical content**: Prove that when gcd(p,L)=1, the measure factorizes as:
```
μ({t ∈ [0,1/L) : {p*t} ∈ A}) = (1/L) * μ(A)
```

**Status**: Mathlib research complete. Two viable implementation paths identified.

---

## Mathlib Research Findings

✓ **Exists in Mathlib 4.29.1:**
- `ZMod.chineseRemainder` — algebraic CRT
- `integral_prod_mul` — Fubini's theorem for product measures
- `MeasureTheory.MeasurePreserving` — framework for measure-preserving maps
- `Nat.Coprime` properties — coprimality in number theory

⚠️ **Partial / Limited:**
- `AddCircle.equidistributed_of_irrational` — equidistribution for irrational rotations only
  (Our case is rational p/L, so doesn't directly apply)

---

## Implementation Options

### Option A: Explicit CRT Bijection (Heavy, Rigorous)

**Approach**: 
1. Define bijection φ: [0, 1/(Lp)) → [0,1/L) × [0,1/p) using Int.fract
2. Prove it's a bijection using Nat.Coprime + ZMod.chineseRemainder pattern
3. Prove measure-preserving (both sides have measure 1/(Lp))
4. Apply integral_prod_mul (Fubini) to factor the integral
5. Conclude measure equality

**Estimated effort**: 80-120 lines  
**Risk**: Medium (requires sustained focus on CRT lifting)  
**Timeline**: 2-3 focused sessions  

---

### Option B: Direct Coprimality Argument (Medium, Conceptual)

**Approach**:
1. Use Nat.Coprime for uniform distribution argument
2. Apply periodicity of Int.fract directly
3. Use measure scaling without explicit bijection

**Estimated effort**: 40-60 lines  
**Risk**: High (unclear if Mathlib has right lemmas)  
**Timeline**: 1-2 sessions (or blocked quickly)  

---

### Option C: Look for Existing Mathlib Lemma (Quick Win)

**Approach**: Search for lemmas handling equidistribution with coprimality

**Estimated effort**: 30 min search + 5-10 lines if found  
**Risk**: Low (if it exists, huge win)  
**Timeline**: Immediate  

---

## Recommendation

**Spend 30 minutes on Option C first**, searching for:
- `Int.fract_equidistributed_coprime` or similar
- Product measure lemmas lifting CRT to reals
- Recent Mathlib PRs on measure + number theory

If nothing found after 30 min: **commit to Option A** (explicit bijection) for certainty of completion.

---

## Impact on Timeline

- **Option C succeeds** → Complete this session, unblock Theorems 10.1 & 11.1
- **Option A** → 2-3 sessions for Theorem 5.2
- **Option B succeeds** → 1-2 sessions

---

## After Theorem 5.2

Once `fract_equidistributed_one_period` is closed:
- **theorem52_weyl** (20-40 lines)
- **theorem52_nonempty** (2-3 lines)
- **Theorems 10.1 & 11.1** available

---

**Recommendation: Try Option C for 30 minutes, then commit to Option A if unsuccessful.**
