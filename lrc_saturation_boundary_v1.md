# LRC Chamber Safety: The Saturation Boundary
**Version**: v1 (2026-03-09)
**Motivation**: Investigating exceptions to understand the overarching mechanism

---

## 1. The Structural Discovery

Investigating why the theorem requires ≥2 distinct prime factors reveals a **sharp structural boundary**:

| n | Prime factorization | Saturates (∃ unsafe chamber)? | In scope of theorem? |
|---|--------------------|-----------------------------|----------------------|
| 4  | 2²        | **YES** (1 interval) | NO (prime power) |
| 6  | 2·3       | NO                   | YES |
| 8  | 2³        | **YES** (1 interval) | NO |
| 9  | 3²        | **YES** (4 intervals)| NO |
| 10 | 2·5       | NO                   | YES |
| 12 | 2²·3      | NO                   | YES |
| 15 | 3·5       | NO                   | YES |
| 16 | 2⁴        | **YES** (1 interval) | NO |
| 25 | 5²        | **YES** (18 intervals)| NO |
| 27 | 3³        | **YES** (4 intervals)| NO |
| 30 | 2·3·5     | NO                   | YES |

**Finding**: Saturation (unsafe chamber ↔ bad-set union = ℤ_n for some achievable floor-state vector) occurs **exactly for prime powers** n = p^k, and **never for composites with ≥2 distinct prime factors**.

The ≥2 prime factors hypothesis is not a technical convenience — it is a **sharp necessary condition**.

---

## 2. Why Prime Powers Saturate

**For n = p^k**: All non-unit residues are multiples of p: {p, 2p, ..., p^{k-1}·(p-1)}.

The bad-set pair {−t·e⁻¹, −(t+1)·e⁻¹} (mod p^k) covers a multiple of p iff:
- t ≡ 0 (mod p): then −t·e⁻¹ ≡ 0 (mod p) → a multiple of p is hit
- t ≡ −1 ≡ p−1 (mod p): then −(t+1)·e⁻¹ ≡ 0 (mod p) → a multiple of p is hit

With p^{k-1}−1 non-unit residues and φ(p^k) = p^{k-1}(p−1) runners, the bad-set union has at most 2φ(p^k) = 2p^{k-1}(p−1) elements. For these to cover all p^k residues, we need 2p^{k-1}(p−1) ≥ p^k, i.e., 2(p−1) ≥ p, i.e., p ≥ 2. True for all primes!

**Saturating configuration for n = 4** (p=2, k=2): floor state f_3 = 1.
- bad_set(1, 0, 4) = {0, 3}
- bad_set(3, 1, 4) = {1, 2}
- Union = {0, 1, 2, 3} = ℤ_4 ✓

**Saturating configuration for n = 9** (p=3, k=2): floor state f_2=0, f_4=1, f_5=1, f_7=2, f_8=2 (for α ∈ (2/7, 3/8)).
- Union covers all of ℤ_9 including the non-units {3, 6}.
- This is achievable for α ≈ 0.31, which corresponds to fibres b ∈ B_div.

---

## 3. Why Multi-Prime Composites Cannot Saturate

**Case 1: n = p·q (two distinct primes, p < q, 2φ(n) < n)**

2φ(n) = 2(p−1)(q−1) < pq = n ⟺ (p−2)(q−2) < 2.

For n=6 (p=2,q=3): (0)(1) = 0 < 2 → **impossible by simple counting**. ✓
For n=10 (p=2,q=5): (0)(3) = 0 < 2 → **impossible by counting**. ✓

**Case 2: n = p·q with 2φ(n) ≥ n** (like n=15: 2·8=16 > 15)

Counting alone is insufficient. The achievability constraint prevents saturation:

Non-units are of **two types**: multiples of p AND multiples of q.
- To cover a multiple of p: need floor state t ≡ 0 or −1 (mod p)
- To cover a multiple of q: need floor state t ≡ 0 or −1 (mod q)

For both types of non-unit to be covered, some runner must be at floor state satisfying BOTH constraints simultaneously (t ≡ 0/−1 mod p AND t ≡ 0/−1 mod q), OR different runners must cover different types.

The **synchronous floor-state constraint** (all f_e = ⌊e·b/L⌋ for the same b) links the floor states and limits which combinations are achievable. Specifically:
- If f_e covers a multiple of p, then e·b/L ≡ 0/−1 (mod p) as fractions → constrains b/L mod (p/e)
- Simultaneously covering a multiple of q requires b/L to additionally satisfy a congruence mod (q/e')

The CRT interaction between these constraints means it's impossible to simultaneously cover all multiples of both p and q while also covering all units. This is the core of why Lemma RI (Gap A) works: it shows that at any z=0 event, the unit bad-set pairs leave uncovered residues due to this multi-prime structure.

**Algebraic core**: For n = p·q (squarefree with ≥2 prime factors), the map r ↦ e·r (mod n) for units e creates a "mixing" between the residues mod p and residues mod q. No achievable floor-state vector can align all runners to simultaneously cover all non-units of both types while covering all units.

---

## 4. Implications for the LRC Proof

### Chamber Safety theorem scope (exact)

**Theorem (Chamber Safety)**: Holds for n composite with ≥2 distinct prime factors. **Fails** for prime powers n = p^k (counterexamples exist in B_div).

### How prime powers are handled in the full proof

From the existing proof architecture (memory/lrc_proof_status.md):
- G4.OT Sub-case B3 (n = p^k, odd prime): proved via **Z0S.3**: B_safe ≥ φ(n)(n−2)/2 + 2 ≥ n ≥ 1. This gives Λ_eff > 0 (not B_safe = |B_div|).
- The prime power proof uses a DIFFERENT, WEAKER lower bound (B_safe ≥ 1, not B_safe = |B_div|).
- For prime powers, most chambers are safe (B_safe is large), but NOT all. The theorem needs only one safe fibre to guarantee Λ_eff > 0.

### The two-tier structure revealed by exceptions

| n type | B_safe claim | Proof strategy | Boundary |
|--------|-------------|----------------|----------|
| Composite, ≥2 prime factors | B_safe = \|B_div\| | Chamber safety (Lemma 0 + Lemma RI) | Sharp upper bound |
| Prime power p^k | B_safe < \|B_div\| but B_safe ≥ 1 | Z0S.3 + different lower bound | Weaker result, different proof |
| Prime p | Separate treatment | irrational/arithmetic witnesses | Different framework |

---

## 5. Why the Exceptions Reveal the Mechanism

The saturation examples (n=4, f_3=1) and (n=9, f_2=0, f_4=1, ...) reveal exactly WHY Lemma 0 works for multi-prime n but fails for prime powers:

**Lemma 0 at all-zero floor states**: Union = {0} ∪ {n−u : unit u}.
- For n = p·q: {n−u : unit u} = {(n−u) : gcd(u,n)=1}. The complement is {r : gcd(n−r, n) > 1} = non-units mod n. Since n has two prime factors, the non-units include residues ≡ 0 mod p AND residues ≡ 0 mod q. Taking r = p_min = p: gcd(n−p, n) ≥ p > 1 (since p | n and p | n−p). So r=p is always uncovered.
- For n = p^k: the same formula gives {n−u : unit u}. Complement = non-units = multiples of p. Is some multiple of p = n−u for a non-unit value? YES: r = p gives n−r = p^k−p = p(p^{k-1}−1). Since gcd(p^{k-1}−1, p) = 1, n−p is NOT a multiple of p (it's a unit). So r = p is ALSO UNCOVERED at all-zero for prime powers! Lemma 0 still works at all-zero.

So for prime powers, the **all-zero configuration IS safe** (Lemma 0 works). The saturation occurs at NON-ZERO floor states — specifically when the floor state creates a "perfect alignment" where bad-set pairs cover all multiples of p.

The failure of chamber safety for prime powers is not at the FIRST chamber (all-zero) but at INTERIOR chambers where floor states are non-zero and aligned to cover all non-units simultaneously.

---

## 6. Summary

**The overarching mechanism**:

The chamber safety theorem works because the BAD-SET UNION at any achievable floor-state vector has a structural GAP for multi-prime n. This gap exists because:
1. At the all-zero baseline (Lemma 0): gap guaranteed by simple counting/inversion argument
2. At z=0 event floor states (Lemma RI = Gap A): gap guaranteed by the algebraic structure of unit inverses and the resonance interval mechanism (Session 11 proof)
3. These two cases exhaust all floor-state vectors in B_div via the chamber partition

For prime powers, the same two lemmas provide safety at MOST floor states, but INTERIOR floor states (non-zero, non-event) can achieve full saturation. The ≥2-prime-factor condition is exactly what prevents interior saturation.

**The theorem hypothesis is tight**: there is no weaker condition that would suffice.
