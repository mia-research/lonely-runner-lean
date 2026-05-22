# Formalization Plan — Lonely Runner Conjecture (v11 draft)
# Lean 4 + Mathlib

**Generated:** 2026-05-22  
**Source:** `../../lrc_proof_v11_draft.md` (version 11.3)

---

## Executive Summary

The v11 manuscript proves the Lonely Runner Conjecture for all n ≥ 3 via strong induction,
partitioning parameter space into four exhaustive cases. The critical new contribution is
Theorem 11.1 (Modified Divisor Induction), which closes the "highly smooth" sub-case.

**Formalization difficulty**: HIGH overall. The biggest single blocker is Theorem 5.2
(CRT measure independence lemma). Arithmetic lemmas are routine; measure-theoretic
lemmas are moderate; Theorems 10.1 and 11.1 depend on the Weyl engine and are hard.

---

## Definitions Needed

### circDist
```lean
noncomputable def circDist (x : ℝ) : ℝ := min (Int.fract x) (1 - Int.fract x)
```
**Mathlib:** `Int.fract` in `Mathlib.Algebra.Order.Floor.Defs`  
**Difficulty:** ROUTINE

### goodSet, jointGoodSet
```lean
noncomputable def goodSet (v n : ℕ) : Set ℝ := { t | circDist (v * t) ≥ 1/n }
noncomputable def jointGoodSet {k} (speeds : Fin k → ℕ) (n : ℕ) : Set ℝ := ⋂ i, goodSet (speeds i) n
```
**Difficulty:** ROUTINE

### LRC predicate / intLRC / H
Defined in `Defs.lean`. **Difficulty:** ROUTINE to state, hard to prove.

---

## Lemmas in Dependency Order

| Item | File | Difficulty | sorry ok? |
|------|------|-----------|----------|
| Lemma 2.1 Fundamental Identity | Lemma21 | ROUTINE | No |
| Corollary 2.2 | Lemma21 | ROUTINE | No |
| Lemma 4.1 Positive Measure | Lemma41 | MODERATE | Lipschitz step |
| **Theorem 5.2 CRT Measure** | **Theorem52** | **HARD — BLOCKER** | **YES** |
| Theorem 6.1 BSR | Theorem61 | ROUTINE | No |
| Theorem 7.1 Large SR | Theorem71 | MODERATE | Interval case split |
| Lemma 9.1 Case Exhaustion | Theorem121 | ROUTINE | No |
| Lemma 9.2 Hard-Case Partition | Theorem121 | ROUTINE | No |
| Lemma 9.3 r ≤ n-3 | Theorem111 | ROUTINE | No |
| Theorem 10.1 DI | Theorem101 | HARD | Depends on 5.2 |
| Theorem 11.1 Mod DI | Theorem111 | HARD | Depends on 5.2 |
| Theorem 12.1 Main | Theorem121 | MODERATE | Assembly |

---

## Critical Dependency: Theorem 5.2

**Key insight:** Theorem 5.2 is NOT classical Weyl equidistribution. It is a finite
CRT measure factorisation:

> If G has period 1/L and gcd(p, L) = 1, then over [0, 1/(Lp)):
>   μ({t ∈ G | {pt} ∈ A}) = μ(G) · μ(A)

This follows from the bijection φ : [0, 1/(Lp)) → [0,1/L) × [0,1/p) being
measure-preserving (by CRT), then Fubini factorises the product.

**Mathlib status:** NO direct named match. Must be proved from:
- `MeasureTheory.Measure.prod` (Fubini) — EXISTS
- `ZMod.chineseRemainder` (integer CRT) — EXISTS  
- Real-interval CRT bijection — MUST BUILD from scratch

**Estimated effort:** 200–400 lines for a complete proof.

---

## Mathlib Naming Reference (v4.29.1)

| Concept | Mathlib name |
|---------|-------------|
| Fractional part | `Int.fract` in `Mathlib.Algebra.Order.Floor.Defs` |
| `Int.fract_add_int` | EXISTS |
| `Int.fract_nonneg`, `Int.fract_lt_one` | EXISTS |
| Lebesgue measure | `MeasureTheory.volume` |
| Product measure | `MeasureTheory.Measure.prod` |
| Fubini | `MeasureTheory.integral_prod` |
| `Nat.Coprime` | EXISTS |
| `Nat.Prime.two_le` | EXISTS |
| `Finset.lcm` | EXISTS |
| `Nat.dvd_or_coprime` | EXISTS — use for Lemma 9.2 |

## Notes from Build Attempt

- `import Mathlib.Algebra.Order.Floor` is WRONG (it's a directory in v4.29.1)
- Use `import Mathlib.Algebra.Order.Floor.Defs` for `Int.fract`
- `import Mathlib.MeasureTheory.Integral.Bochner` → use `.Basic` suffix
- For exploratory work: `import Mathlib` avoids all path issues
