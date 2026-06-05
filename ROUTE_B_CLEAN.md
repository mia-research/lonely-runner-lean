# Route B — Discrete CRT Partition Approach

**Status**: Cleaner approach identified  
**Why this works**: Plays to Lean's strengths (finite combinatorics) instead of continuous measure theory  

---

## The Insight

Instead of continuous CRT bijection Φ: [0, 1/(Lp)) → [0,1/L) × [0,1/p), use:

**Discrete partition + CRT bijectivity on indices**

Partition [0,1) into **Lp cells** of equal width 1/(Lp):
- Cell I_m = [m/(Lp), (m+1)/(Lp)) for m ∈ {0, 1, ..., Lp-1}

On each cell I_m:
- Int.fract(L*T) depends **only on m mod L** (constant across the cell)
- Int.fract(p*T) depends **only on m mod p** (constant across the cell)

**The key**: By CRT (gcd(L,p)=1), the map m ↦ (m mod L, m mod p) is a **bijection** from {0,...,Lp-1} to {0,...,L-1} × {0,...,p-1}.

This bijection makes the fractional parts independent, yielding the measure factorization.

---

## Proof Outline (Finite Combinatorics)

**Step 1: Cell structure**
```lean
For each m ∈ {0,...,Lp-1}, cell I_m has width 1/(Lp)
On I_m: {L*T} ∈ [a_m/L, (a_m+1)/L) where a_m = m mod L
On I_m: {p*T} ∈ [b_m/p, (b_m+1)/p) where b_m = m mod p
```

**Step 2: Compute measure on one cell**
```lean
μ(I_m ∩ {p*T ∈ A}) = μ(I_m) * (measure of A intersected with [b_m/p, (b_m+1)/p))
                   = (1/(Lp)) * (measure of this intersection)
```

**Step 3: Sum over all cells**
```lean
Sum over m = 0 to Lp-1:
  μ(I_m ∩ {p*T ∈ A})

By Nat.Coprime: as m ranges {0,...,Lp-1} and (m mod L, m mod p) ranges all pairs,
the intersection of A with the cells corresponding to each (a,b) pair is:
  
  Total = Σ_a Σ_b [μ(all cells with m mod L = a, m mod p = b) ∩ {p*T ∈ A}]
        = Σ_a Σ_b [μ(I_m with index (a,b)) * indicator(b_m = b)]
        = Σ_a [μ(cells with m mod L = a)] * [μ(A intersected with its interval)]
```

**Step 4: Restrict to [0, 1/L)**
- This is the subset of cells with m mod L = 0
- These are cells I_0, I_p, I_{2p}, ..., I_{(L-1)p}
- Total width: L cells × (1/(Lp) per cell) = 1/L
- Measure of intersection with A: (1/L) * μ(A)

---

## Why This Is Better for Lean

| Aspect | Route A (Continuous) | Route B (Discrete) |
|--------|---|---|
| **Bijection** | Continuous on ℝ intervals | Discrete on {0,...,Lp-1} |
| **Measure** | Product measures + Fubini (complex API) | Finset sums (straightforward) |
| **CRT** | Lift ZMod.chineseRemainder to ℝ (hard) | Use directly on ℤ/Lℤ × ℤ/pℤ (built-in) |
| **Injectivity proof** | Lifting Nat.Coprime to ℝ (tricky) | CRT bijection on indices (direct) |
| **Mathlib tooling** | Weak (product measures underdeveloped) | Strong (Finset sums, Nat.Coprime) |
| **Estimated Lean code** | 80-120 lines | 50-80 lines |
| **Risk of API friction** | High (continuous measure theory) | Low (discrete algebra) |

---

## Lean Implementation Steps

```lean
theorem fract_equidistributed_one_period (...) : ... := by
  -- Step 1: Define cells
  let cells : Fin (L * p) → Set ℝ := fun m =>
    Set.Ico ((m.val : ℝ) / (L * p)) (((m.val + 1 : ℕ) : ℝ) / (L * p))

  -- Step 2: Partition [0,1) = ⋃ cells
  have partition : Set.Ico (0 : ℝ) 1 = ⋃ m : Fin (L * p), cells m := by sorry

  -- Step 3: On each cell, fractional parts depend only on (m mod L, m mod p)
  have cell_deps : ∀ m : Fin (L * p), ∀ T ∈ cells m,
    (Int.fract (L * T), Int.fract (p * T)) ∈
      Set.Ico ((m.val % L : ℝ) / L) (((m.val % L + 1 : ℕ) : ℝ) / L) ×
      Set.Ico ((m.val % p : ℝ) / p) (((m.val % p + 1 : ℕ) : ℝ) / p) := by sorry

  -- Step 4: CRT bijectivity of indices
  have crt_bijection : Function.Bijective (fun m : Fin (L * p) => (m.val % L, m.val % p)) := by
    -- Use Nat.Coprime.modeq_iff or ZMod.chineseRemainder
    sorry

  -- Step 5: Measure calculation via Finset sum
  have measure_eq : MeasureTheory.volume (↑(Set.Ico (0 : ℝ) 1) ∩ {T | Int.fract (p * T) ∈ A}) =
    (∑ m : Fin (L * p), 
      MeasureTheory.volume (cells m ∩ {T | Int.fract (p * T) ∈ A})) := by
    -- From partition
    sorry

  -- Step 6: Factor the sum using CRT bijectivity
  -- ... (combinatorial factorization)
  sorry
```

---

## Decision for You

**Given the discrete approach is much cleaner:**

1. **Option: Commit to Route B (Recommended)**
   - Clean, Lean-friendly, 50-80 lines
   - Play to Mathlib's strengths (finite algebra, Nat.Coprime)
   - Avoid continuous measure-theoretic complexity
   - Should complete in 1-2 hours of focused work

2. **Option: Keep current state**
   - Leave hard step as sorry with clear blueprint
   - Unblock Theorems 10.1, 11.1 immediately
   - Return to hard step with fresh perspective later

**Recommendation: Go for Route B** — it's the right tool for the job in Lean, and the discrete partition idea is mathematically elegant.

---

**Ready to attempt Route B with finite Finset sums and Nat.Coprime bijectivity?**
