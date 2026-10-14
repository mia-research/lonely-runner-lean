# Gap A Investigation Findings v2
**Date:** 2026-03-07
**Scripts:** `gap_a_investigation_v1.py`, `gap_a_investigation_v2.py`, `gap_a_odd_composite_v1.py`, `gap_a_odd_composite_v2.py`

---

## The Exceptional Structure: Zero Isolated Events ↔ n is Prime

**The central finding:** Zero isolated m≥2 z=0 events occur **if and only if n is prime**.

| n type | Isolated count | Reason |
|---|---|---|
| Prime n | 0 (always) | Dense unit set {1,...,n-1} → complete Cond1/Cond2 relay |
| Even composite n | ≥1 (always) | n-2 is non-unit → Cond2 partner blocked for (n-1, 2) |
| Odd composite n | ≥1 (always) | Cond2 partner e'* lands on non-unit for specific (eu, m) |

**Verified:** All prime n up to 113 have zero isolated events. All composite n up to 200 have positive isolated count. No counterexample found.

---

## The Corrected Cond2 Partner Formula

For event (e_u, m=2) and unit e_u ≥ 3, the Cond2 partner e'* is the unique element in **[n-e_u, n-1]** (not [n-e_u, n-2] as incorrectly stated in v1) satisfying e'* ≡ -n (mod e_u):

Let a = n mod e_u (1 ≤ a ≤ e_u - 1).

| Condition | Formula | Name |
|---|---|---|
| 2a ≤ e_u | e'* = n - 2a | Case 1 |
| 2a > e_u | e'* = n + e_u - 2a | Case 2 |

**Special sub-case:** When 2a = e_u + 1, e'* = n - 1. Since gcd(n-1, n) = 1 always, Cond2 fires unconditionally. These events are **never isolated** — n-1 acts as a universal relay sentinel.

**(e_u, 2) is isolated if and only if gcd(e'*, n) > 1.**

**Verified:** Zero mismatches across all 922 (e_u, m=2) events for odd composite n in [9, 100].

---

## Theorem: Gap A for Even Composite n (PROVED)

**Theorem (Gap A — even composite n).** *For any even composite n ≥ 6, the event (e_u = n−1, m = 2) is isolated. In particular, B_safe ≥ 1.*

**Proof.**
- Cond1 fails: 2e' ≡ e' (mod n-1) → e' ≡ 0 (mod n-1), impossible for e' < n-1.
- Cond2 unique partner: a = n mod (n-1) = 1. e'* = n-2. gcd(n-2, n) = gcd(2, n) = 2 for even n → non-unit. Cond2 fails. □

**Verified:** 0 errors across n=4..79 (even composites). □

---

## Theorem: Gap A for Odd Prime Power n=p² (PROVED)

**Theorem (Gap A — n=p²).** *For any odd prime p, the event (e_u = 2p−1, m = 2) is isolated.*

**Proof.**

Let n = p², e_u = 2p-1.

**Step 1** (unit): gcd(2p-1, p²) = gcd(2p-1, p)² = gcd(-1, p)² = 1. So e_u is a unit. ✓

**Step 2** (partner formula): a = p² mod (2p-1). Since p² = (2p-1)·(p-1)/2 + (3p-1)/2, we get a = (3p-1)/2.

**Step 3** (Case 2): 2a = 3p-1 > 2p-1 = e_u for p ≥ 1. Also 2a ≠ e_u+1 (that would require p=1). So Case 2 applies. e'* = n + e_u - 2a = p² + (2p-1) - (3p-1) = p² - p = p(p-1).

**Step 4** (non-unit): gcd(p(p-1), p²) = p · gcd(p-1, p) = p · 1 = p > 1. □

**Verified:** All primes p in {3, 5, 7, 11, 13, 17, 19, 23, 29, 31}.

---

## Theorem: Gap A for Odd Prime Power n=p^k, k≥3 (PROVED)

**Theorem (Gap A — n=p^k, k≥3).** *For any odd prime p and k ≥ 3, the event (e_u = p^{k-1}−1, m = 2) is isolated.*

**Proof.**

Let n = p^k, e_u = p^{k-1} - 1.

**Step 1** (unit): gcd(p^{k-1}-1, p^k) = gcd(-1, p^k) = 1. Unit. ✓

**Step 2** (partner formula): p^k = p·(p^{k-1}-1) + p, so a = p. ✓

**Step 3** (Case 1): 2a = 2p < p^{k-1}-1 = e_u iff p^{k-1} > 2p+1. For k ≥ 3 and p ≥ 3: p^{k-1} ≥ p² = 9 > 7 = 2·3+1. ✓ Case 1 applies.
e'* = n - 2a = p^k - 2p = p(p^{k-1} - 2).

**Step 4** (non-unit): gcd(p(p^{k-1}-2), p^k) = p · gcd(p^{k-1}-2, p^{k-1}) = p · gcd(-2, p^{k-1}) = p (since p is odd, gcd(2, p^k-1)=1). gcd = p > 1. □

**Verified:** All (p, k) with p ∈ {3, 5, 7} and k ∈ {3, 4, 5}.

---

## Gap A for All Odd Prime Powers: PROVED

Combining the three theorems:

| n type | Constructive witness (e_u, m=2) | e'* | gcd(e'*, n) |
|---|---|---|---|
| Even composite | e_u = n-1 | n-2 | gcd(2, n) = 2 |
| n = p² | e_u = 2p-1 | p(p-1) | p |
| n = p^k, k≥3 | e_u = p^{k-1}-1 | p(p^{k-1}-2) | p |

**Corollary:** For every composite prime power n = p^k (any prime p, k ≥ 2), B_safe ≥ 1. □

---

## Structural Insight: The Isolation Condition

For (e_u, m=2), isolation reduces to gcd(e'*, n) > 1, which depends on whether p | e'*:

**Case 1** (2a < e_u): e'* = n-2a. Isolated iff p | 2a iff **p | a** (p odd). Since a = n mod e_u and p | n: p | a iff p | e_u·q where q = floor(n/e_u), i.e., **p | floor(n/e_u)** (since gcd(e_u, p) = 1).

**Case 2** (2a > e_u, 2a ≠ e_u+1): e'* = n+e_u-2a. Isolated iff p | (e_u-2a). Since p | n: equivalently **p | e_u·(1+2q)** iff **p | (1+2q)** (gcd(e_u,p)=1) iff **q ≡ (p-1)/2 (mod p)** where q = floor(n/e_u).

**Never isolated** (2a = e_u+1): e'* = n-1, gcd(n-1,n)=1. Cond2 always fires. Arises when q = floor(n/e_u)·e_u = n - (e_u+1)/2 (no integers have this property generically).

**Unified isolation criterion:**
> **(e_u, m=2) is isolated iff floor(n/e_u) ≡ 0 (mod p) [Case 1] or ≡ (p-1)/2 (mod p) [Case 2] for some prime p | n.**

The two special values {0, (p-1)/2} mod p are the "isolation resonances" for prime p.

---

## Why Primes Have Zero Isolated Events

For prime n: e'* = n-2 is always a unit (gcd(n-2, n) = gcd(2, n) = 1 for odd prime n). Cond2 always fires for (n-1, 2). More generally, the full unit set {1,...,n-1} means every relay partner exists.

---

## m ≡ 1 (mod p) Pattern (Structural Insight)

For n = p^k and events (e_u, m) with **m ≡ 1 (mod p)**:
- **Always covered** — 0 isolated events in this class (verified for n=9, 25, 49)

**Why:** r_dep = −(m−1)·e_u^{−1} mod n ≡ 0 (mod p) — a non-unit residue. Non-unit residues are covered because unit runners at t=0 cover {−e'^{-1} mod n : e' unit} = all units, and non-unit residues are reached via Cond2 with suitable e'.

**Consequence:** Only events with m ≢ 1 (mod p) can be isolated (a positive fraction).

---

## The n-1 Sentinel: Never-Isolated Cases

When 2a = e_u+1 (e_u odd, a=(e_u+1)/2): the Cond2 partner e'* = n-1. Since gcd(n-1, n) = 1 always (n-1 is the largest unit), Cond2 fires unconditionally. These (e_u, m=2) events are structurally never isolated.

This "n-1 sentinel" arises from the universal unit property of n-1 and explains why the formula doesn't immediately give unlimited isolated events — n-1 is always available as a relay partner.

---

## Odd Composite n with Multiple Prime Factors

**Theorem candidate (from Part C verification):** Every odd composite n with smallest prime p has at least one unit e_u ≥ 3 such that (e_u, m=2) is isolated.

**Verified:** 0 counterexamples for all odd composite n ≤ 200.

**Key cases for non-prime-power n:**

| n type | Isolation path | Example |
|---|---|---|
| p=3 (any n): eu ∈ (n/2, 2n/3) | Case 2, e'*=3e_u-2n, p=3|e'* | n=15: eu=8, e'*=9=3² |
| n=p·q: floor(n/eu)=(q-1)/2 (mod q) | Case 2 via q | n=35: eu=9, e'*=28=4·7 |
| n=p·m, m≥2p+2: eu=m-1 (if unit) | Case 1, floor=p, a=p | n=45: eu=14, ... |

**For p=3:** Any unit eu in (n/2, 2n/3) gives e'* = 3eu-2n with gcd(3eu-2n, n) divisible by 3 (since 3|3eu always). This interval has length n/6 and always contains a unit for n ≥ 9.

**Analytic proof for general non-prime-power n:** Remaining open. Empirically closed (n ≤ 200, zero counterexamples).

---

## Current Gap A Status

| Case | Status |
|---|---|
| Prime n | **Gap A vacuous** — Sole Cover handles prime n |
| Even composite n | **PROVED** — constructive event (n-1, 2) |
| Odd n = p² | **PROVED** — constructive event (2p-1, 2), e'* = p(p-1) |
| Odd n = p^k, k≥3 | **PROVED** — constructive event (p^{k-1}-1, 2), e'* = p(p^{k-1}-2) |
| Odd composite n, multiple prime factors | **Empirically closed** (n ≤ 200) — analytic proof remaining |

**Gap A is proved for ALL prime powers (even and odd).**

Remaining analytic work: odd composite n with at least two distinct prime factors. The isolation resonance condition (floor(n/eu) ≡ 0 or (p-1)/2 mod p for some prime p|n) always produces a unit eu — this needs a number-theoretic witness argument.

---

## Impact on the Proof Document

**B_safe ≥ 1 for the Z0S bound:** Confirmed for all prime powers (analytically) and all composite n ≤ 200 (empirically). The Z0S master bound applies.

**Next step:** Prove for n with ≥2 distinct prime factors that the isolation resonance intervals always contain a unit. For p=3 this follows from the (n/2, 2n/3) density argument. For p≥5, a Chinese Remainder Theorem argument on the residue conditions may close the gap.
