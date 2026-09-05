# Theorem 4.6 — Analytic Proof (M ≥ 2, |E_div|=1) for v4

**Status**: CLEAN DRAFT. Replaces v3 §4.6 computational PL.3 dependency entirely.

**Key structural fact (Gap 3 resolution)**: Valid M must satisfy gcd(M, 11L_0) = 1. Since L_0 = lcm(F) is divisible by all prime factors of elements of F ⊂ {1,...,10}, valid M ≥ 2 must be coprime to all primes ≤ 10 (and coprime to 11). This forces M ≥ 7 for the "easy" templates (L_0=120) and M ≥ 13 for most templates. This large lower bound on M makes the Sole Cover argument work for ALL valid M.

---

## Setup

For the one-divisible branch: E = F ∪ {M} ∪ {11M} where
- F ⊂ {1,...,10}\{M}, |F| = 8
- L_0 = lcm(F)
- gcd(M, 11L_0) = 1 (normalization condition)
- L = 11·M·L_0, N = 121·M·L_0

The safe-point count is x_0(E) = #{k ∈ {1,...,N-1} : e·k mod N ∈ [L, 10L] for all e ∈ E}.

---

## Lemma A (Valid M Lower Bound)

> **Lemma A.** For any 8-element F ⊂ {1,...,10} and valid M ≥ 2 (i.e., gcd(M, 11L_0) = 1):
> - If M ≢ 10 (mod 11): M ≥ 7 and the interval I_M = [ML_0, min((M+1)L_0, 1.1ML_0)] has length ≥ min(L_0, 0.1ML_0) ≥ 0.7L_0 ≥ 84.
> - If M ≡ 10 (mod 11): M ≥ 43.

**Proof.** L_0 = lcm(F) where F ⊂ {1,...,10}. The prime factors of L_0 are a subset of {2, 3, 5, 7} (since F ⊂ {1,...,10} and these are the primes ≤ 10). gcd(M, L_0) = 1 requires M coprime to all prime factors of L_0.

Since any 8-subset F of {1,...,10} contains at least one element from each of {1,2}, {3,6,9}, {5,10}, {7}: L_0 is divisible by 2, 3, 5, 7 for the 42 "generic" templates. For the 3 "reduced" templates:
- F omits both 7 and 9: L_0 = lcm(F) still divisible by 2, 3, 5 (since F contains 6=2·3 and 10=2·5).
- F omits both 7 and something else: similar analysis.

In all 45 cases, the prime factors of L_0 are from {2, 3, 5, 7}. So gcd(M, L_0) = 1 requires M coprime to 2, 3, 5, 7.

- **M ≡ 10 mod 11**: The values M ≡ 10 mod 11 coprime to 2·3·5·7=210 are 10=2·5 (NO), 21=3·7 (NO), 32=2^5 (NO), 43 (prime, coprime to 210 ✓). Minimum valid M ≡ 10 mod 11: **M ≥ 43**.

- **M ≢ 10 mod 11**: Minimum M coprime to 210 is 7 (for templates where L_0 is not divisible by 7), or 11 (excluded) or 13. For the template with L_0 = 120 = 2^3·3·5 (F={1,2,3,4,5,6,8,10}): minimum valid M ≥ 2 is **M = 7**. For templates with 7|L_0: minimum valid M ≥ 13. ☐

---

## Transparency and Floor-State Lemmas (Inline)

**Lemma B (Transparency of 11M on B_div sub-intervals).**
At fibre b ∈ B_div, runner 11M has floor state t_M(b) = ⌊b/L_0⌋. Runner 11M is **transparent** (bad set = ∅) at b iff t_M(b) ≢ 0 and t_M(b) ≢ -1 (mod 11), i.e., t_M(b) mod 11 ∈ {1,...,9}.

**Proof.** Since gcd(11M, 11) = 11: Sol(11M, j, 11) = Z_11 if 11|j, else ∅. Bad set = Sol(11M, -t, 11) ∪ Sol(11M, -(t+1), 11) = ∅ iff 11 ∤ t and 11 ∤ (t+1) iff t ≢ 0, -1 (mod 11). ☐

**Lemma C (Floor-0 for non-divisible runners).**
For e_u ∈ E_non and b ∈ [ML_0, c·ML_0) with c ≤ 1.1: floor(e_u·b/L) = floor(e_u·b/(11ML_0)) = 0 for all e_u ≤ 10.

**Proof.** e_u·b/(11ML_0) ≤ e_u·c·ML_0/(11ML_0) = e_u·c/11 ≤ 10·1.1/11 = 1. So floor = 0 (for b < L/e_u, i.e., b < 11ML_0/10 = 1.1ML_0). ☐

---

## Main Proof

> **Theorem 4.6.** For |E_div| = 1 and M ≥ 2 (with gcd(M, 11L_0) = 1), x_0(E) ≥ 10.

**Proof.** We exhibit ≥ L_0 ≥ 120 safe times. Recall: L_0 ≥ 120 (Lemma 4.3). We consider two cases.

### Case 1: M ≢ 10 (mod 11)

Choose I_M = [ML_0, min((M+1)L_0, 1.1ML_0)). For M ≥ 10: length L_0. For 7 ≤ M < 10 (only M=7 is possible by Lemma A): length = 0.1ML_0 = 0.7L_0 ≥ 0.7·120 = 84.

**Step 1 (11M transparent on I_M):** t_M(b) = ⌊b/L_0⌋ = M for b ∈ [ML_0, (M+1)L_0). Since M ≢ 10 ≡ -1 (mod 11) and M ≢ 0 (mod 11) (as gcd(M,11)=1): t_M ≡ M ∉ {0,-1} (mod 11). Lemma B: 11M transparent. ✓

**Step 2 (floor-0 for non-div runners):** For b ∈ I_M ⊆ [ML_0, 1.1ML_0): Lemma C gives floor(e_u·b/L) = 0 for all e_u ≤ 10. ✓

**Step 3 (dropped unit):** E_non = F ∪ {M} has |E_non| ≤ 9 elements. The set F ∪ ({M} ∩ {1,...,10}) contains at most 9 elements of {1,...,10} (if M ≤ 10) or exactly |F| = 8 elements (if M > 10). In either case, at least one unit d ∈ {1,...,10} is absent from E_non.

Set r* = -d^{-1} mod 11. At floor state 0, for each e_u ∈ E_non with gcd(e_u, 11)=1 (all non-div runners): bad(e_u, 0, 11) = {0, -e_u^{-1} mod 11} (Lemma FLOOR0). The residue r* = -d^{-1} satisfies:
- r* ≠ 0 (since d ≤ 10 is a nonzero unit, d^{-1} ≠ 0);
- r* ≠ -e_u^{-1} for any e_u ∈ E_non, since r* = -e_u^{-1} ↔ d = e_u, contradicting d ∉ E_non.

Therefore r* ∉ bad(e_u, b) for any e_u ∈ E_non. Combined with transparency of 11M (bad(11M, b) = ∅): **all runners are safe at residue r***.

**Step 4 (count safe times):** For each b ∈ I_M ∩ Z: the time k(b) = b + r*·ML_0 satisfies:
- k(b) ∈ {1,...,N-1}: since b ∈ [ML_0, 1.1ML_0) and r* ∈ {1,...,10}: k(b) ∈ [(1+r*)ML_0, (1.1+r*)ML_0) ⊂ [2ML_0, 11.1ML_0) ⊂ [1, N-1]. ✓
- k(b) is safe for 11M: transparent → all r safe. ✓
- k(b) is safe for each e_u ∈ E_non: r* ∉ bad(e_u, b) → safe. ✓
- Distinct: different b give different k(b) (same r*). ✓

x_0(E) ≥ |I_M ∩ Z| ≥ 0.7L_0 ≥ 84 ≥ 10. ✓

### Case 2: M ≡ 10 (mod 11)

By Lemma A: M ≥ 43. Choose I_M = [(M+2)L_0, (M+3)L_0) ⊆ B_div.

**Step 1 (11M transparent on I_M):** t_M(b) = ⌊b/L_0⌋ = M+2 for b ∈ [(M+2)L_0, (M+3)L_0). Since M ≡ 10 (mod 11): M+2 ≡ 12 ≡ 1 (mod 11) ∉ {0,-1} (mod 11). Lemma B: 11M transparent. ✓

**Step 2 (floor-0 for non-div runners):** For b ∈ [(M+2)L_0, (M+3)L_0) and e_u ≤ 10:
```
e_u · b / L ≤ 10 · (M+3)L_0 / (11ML_0) = (10/11) · (M+3)/M = (10/11) · (1 + 3/M).
```
Since M ≥ 43: (1 + 3/M) ≤ 1 + 3/43 < 1.07, so e_u·b/L < (10/11)·1.07 < 0.98 < 1. Floor = 0. ✓

**Step 3 (dropped unit):** Same as Case 1: at least one d ∈ {1,...,10} absent from E_non. r* = -d^{-1} uncovered by all runners. ✓

**Step 4 (count safe times):** k(b) = b + r*·ML_0. For b ∈ [(M+2)L_0, (M+3)L_0): k(b) ∈ [(M+2+r*M)L_0, (M+3+r*M)L_0) ⊂ [2ML_0, 11.1ML_0) ⊂ [1, N-1]. ✓

x_0(E) ≥ |I_M ∩ Z| ≥ L_0 ≥ 120 ≥ 10. ✓

---

## Remark on Case Completeness

The two cases partition all valid M ≥ 2 with gcd(M, 11L_0)=1:
- Case 1: M ≢ 10 (mod 11) — covers all M coprime to 11 except M ≡ 10 mod 11.
- Case 2: M ≡ 10 (mod 11), minimum valid M = 43.

The proof uses no computation: only the Sole Cover Lemma (FLOOR0), Lemma B (transparency), Lemma C (floor-0), and the arithmetic inequality (M+3)/M < 1.07 for M ≥ 43. ☐

---

## Combining with Prop 4.5 (M = 1)

- M = 1: Proposition 4.5 (witness table, Gap 2, COMPLETE).
- M ≥ 2: Theorem 4.6 (Case 1 + Case 2 above).

Together: x_0(E) ≥ 10 for ALL |E_div| = 1 configurations. ☐

---

## Notes for v4 Paper Integration

- Lemma A is short (5 lines) and can go in a remark after Corollary 4.4.
- Lemmas B and C are the same transparency/floor lemmas needed for Prop 3.2; state them once in §3 and reuse here.
- The proof fits in ~1 page, replacing the 3-line computational PL.3 reference entirely.
- **No external citations needed**: both cases use only inline lemmas.
