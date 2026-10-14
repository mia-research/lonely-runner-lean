# Gap A Investigation Findings v3 — COMPLETE PROOF
**Date:** 2026-03-08
**Scripts:** `gap_a_investigation_v1.py`, `gap_a_investigation_v2.py`, `gap_a_odd_composite_v1.py`, `gap_a_odd_composite_v2.py`, `gap_a_multiprime_v1.py`
**Extends:** `lrc_gap_a_findings_v2.md`

---

## Summary

Gap A is now **proved for ALL composite n** (odd and even). The remaining case from v2 — odd n with ≥2 distinct prime factors — is closed by two new theorems proved in this session.

| Case | Status |
|---|---|
| Prime n | Gap A vacuous — Sole Cover handles prime n |
| Even composite n | ✅ PROVED — constructive witness eu = n-1 |
| Odd n = p² | ✅ PROVED — witness eu = 2p-1, e* = p(p-1) |
| Odd n = p^k, k≥3 | ✅ PROVED — witness eu = p^{k-1}-1, e* = p(p^{k-1}-2) |
| Odd n, ≥2 distinct prime factors | ✅ **NOW PROVED** — universal witnesses 2n/p_min − 1 and 2n/p_min − 2 |

**GAP A IS PROVED FOR ALL COMPOSITE n.**

---

## Review: The e* Formula and Isolation Criterion

For a unit eu ∈ {2, ..., n-2}, define a = n mod eu and:
- **Case 1** (2a ≤ eu): e* = n − 2a
- **Case 2** (2a > eu): e* = n + eu − 2a

The event (eu, m=2) is isolated iff **gcd(e*, n) > 1**.

---

## New Theorem I: Closed-Form e* Near the Largest Prime Factor

Let n be odd with ≥2 distinct prime factors and r = largest prime factor, m = n/r (odd, m ≥ 3).

**Theorem I(a): eu = 2r−1 gives e* = m(r−1).**

*Proof.* Write m = 2j+1 (m odd). Then n = mr = (2j+1)r = 2jr + r.
- 2jr mod (2r−1): since 2jr = j(2r−1) + j, the remainder is j.
- So a = n mod (2r−1) = j + r = (m−1)/2 + r.
- Check 2a ≤ eu: (m−1)+2r ≤ 2r−1 iff m ≤ 0. Impossible. Case 2 applies.
- e* = n + eu − 2a = mr + (2r−1) − ((m−1)+2r) = mr − m = **m(r−1)**.
- gcd(e*, n) = gcd(m(r−1), mr) = m · gcd(r−1, r) = **m > 1**. □

**Theorem I(b): eu = 2r−2 gives e* = m(r−2).**

*Proof.* n = mr = m(r−1) + m. Now eu = 2(r−1).
- m(r−1) mod 2(r−1): m = 2j+1, so m(r−1) = 2j(r−1)+(r−1), giving remainder r−1.
- a = (r−1) + m.
- Check 2a ≤ eu: 2(r−1+m) ≤ 2(r−1) iff m ≤ 0. Impossible. Case 2.
- e* = mr + 2(r−1) − 2(r−1+m) = mr − 2m = **m(r−2)**.
- gcd(e*, n) = gcd(m(r−2), mr) = m · gcd(r−2, r) = m · gcd(r−2, 2) = **m** (since r is an odd prime, r−2 is odd). □

**Corollary:** For any odd n with ≥2 distinct prime factors and largest prime r, both eu = 2r−1 and eu = 2r−2 give gcd(e*, n) = n/r > 1 when they are units of n. (These are the witnesses used for semiprimes n = pq.)

---

## New Theorem II: The Resonance Interval

For any unit eu with floor(n/eu) = k: if 2k+1 ≡ 0 (mod p) for some prime p | n, then e* = (2k+1)eu − n is divisible by p, hence gcd(e*, n) ≥ p > 1.

**Simplest resonance (k = (p_min−1)/2):** Setting p = p_min (smallest prime factor of n) and k = (p_min−1)/2, we get 2k+1 = p_min and:

> For any unit eu in the **resonance interval** (2n/(p_min+1), 2n/p_min):
> - floor(n/eu) = k = (p_min−1)/2 (exact, since n/(k+1) = 2n/(p_min+1) < eu < 2n/p_min = n/k)
> - e* = p_min · eu − n
> - gcd(e*, n) is divisible by p_min > 1

*Proof.* With floor(n/eu) = k, the remainder a = n − k·eu satisfies 2a > eu (since eu < 2n/(2k+1) = 2n/p_min requires checking: 2a = 2n−2keu > eu iff 2n > (2k+1)eu = p_min · eu, i.e., eu < 2n/p_min ✓). So Case 2 gives e* = n + eu − 2a = n + eu − 2(n−keu) = (2k+1)eu − n = p_min · eu − n. Since p_min | n: p_min | p_min·eu − n = e*. □

**Verified:** 43,653 (n, eu) pairs across all odd n ≤ 2000 with 2+ distinct prime factors. Zero violations.

---

## New Theorem III: Universal Witness Pairs (Complete Proof)

**Theorem III.** *For any odd n with ≥2 distinct prime factors and smallest prime factor p_min, setting m = n/p_min:*

*(A) Both 2m−1 and 2m−2 lie in the resonance interval (2n/(p_min+1), 2n/p_min).*

*(B) gcd(2m−1, n) = gcd(2m−1, p_min). [Since gcd(2m−1, m) = 1 always.]*

*(C) gcd(2m−2, n) = gcd(m−1, p_min). [Since gcd(2, n) = 1 (n odd) and gcd(m−1, m) = 1.]*

*(D) At most one of {2m−1, 2m−2} is a non-unit of n.*

*(E) The unit one gives an isolated event via Theorem II.*

**Proofs.**

**(A)** Upper bounds: 2m−1 < 2m and 2m−2 < 2m trivially. Lower bound for 2m−2: 2m−2 > 2n/(p_min+1) = 2mp_min/(p_min+1) iff (p_min+1)(m−1) > mp_min iff m(p_min+1−p_min) > p_min+1 iff m > 1. Since m = n/p_min ≥ p_2 ≥ p_min+2 > 1. ✓

**(B)** gcd(2m−1, n) = gcd(2m−1, p_min · m). gcd(2m−1, m): since 2m−1 ≡ −1 (mod m), gcd = gcd(−1, m) = 1. So gcd(2m−1, n) = gcd(2m−1, p_min).

**(C)** gcd(2m−2, n) = gcd(2(m−1), p_min · m). gcd(2, p_min · m) = 1 (n odd). gcd(m−1, m) = 1. So gcd(2m−2, n) = gcd(m−1, p_min).

**(D)** Suppose both are non-units:
- 2m−1 non-unit: gcd(2m−1, p_min) > 1 ⟹ p_min | 2m−1 ⟹ 2m ≡ 1 (mod p_min) ⟹ m ≡ (p_min+1)/2 (mod p_min).
- 2m−2 non-unit: gcd(m−1, p_min) > 1 ⟹ p_min | m−1 ⟹ m ≡ 1 (mod p_min).
- Both: (p_min+1)/2 ≡ 1 (mod p_min) ⟹ p_min+1 ≡ 2 (mod p_min) ⟹ 1 ≡ 0 (mod p_min). **Impossible.** □

**(E)** By (A), the unit one lies in the resonance interval. By Theorem II, any unit in the resonance interval gives gcd(e*, n) divisible by p_min > 1. □

**Verified:** 1,800 odd n with 2+ distinct prime factors tested, n ≤ 5000. Zero failures.

---

## Why Even the "Both-Blocked" Cases Work

When both 2r−1 and 2r−2 (near the largest prime r) are non-units (requiring two DIFFERENT small prime factors to block them simultaneously), the witnesses 2n/p_min − 1 and 2n/p_min − 2 (near n/p_min, the resonance interval top) provide the fallback. These witnesses do NOT depend on the largest prime factor at all.

Example (n=165=[3,5,11]):
- 2r−1=21 blocked by 3 (gcd=3); 2r−2=20 blocked by 5 (gcd=5).
- Resonance interval = (2·165/4, 2·165/3) = (82.5, 110). p_min=3, m=55.
- Candidates: 2m−1=109 (gcd(109,165)=1 ✓), 2m−2=108 (gcd=3).
- Witness: eu=109, e*=3·109−165=162=2·3⁴, gcd(162,165)=3 > 1. ✓

---

## Complete Gap A Case Table

| n type | Constructive witness eu | e* | gcd(e*, n) |
|---|---|---|---|
| Even composite | n−1 | n−2 | gcd(2, n) = 2 |
| n = p² | 2p−1 | p(p−1) | p |
| n = p^k, k≥3 | p^{k-1}−1 | p(p^{k-1}−2) | p |
| Odd semiprime n=pq (p<q) | 2q−2 or 2q−1 (whichever is a unit) | p(q−2) or p(q−1) | p |
| Odd n, general (≥2 distinct primes) | 2n/p_min − 1 or 2n/p_min − 2 | p_min · eu − n | ≥ p_min |

---

## Key Structural Insight: The Mirror Symmetry of Blockage

The "at-most-one-non-unit" argument (Parts B, D, C of Theorem III) and the semiprime proof share the same skeleton:

- Two candidates a, b near a threshold.
- If a is non-unit: some prime condition on m.
- If b is non-unit: a DIFFERENT prime condition on m.
- Both simultaneously: forces p ≡ 1 (mod p) or 0 ≡ 1 (mod p). Impossible.

This "mutual exclusion via modular contradiction" is the universal mechanism behind Gap A witnesses existing in all cases.

---

## Skills Update: Exception and Outlier Investigation Protocol

*Added to `/Users/trentpalelei/.claude/projects/-Users-trentpalelei-Desktop-Math-Ex/memory/skills.md`*

Every time exceptions/mismatches are found during verification:
1. **Investigate the exceptions first** before assuming counterexamples.
2. Formula bugs consistently found (e.g., range [n-eu, n-2] vs [n-eu, n-1]).
3. Restriction artifacts resolved by widening search domain (e.g., eu < n/2 → all units).
4. "Failed" cases often reveal richer structure (e.g., n-1 sentinel, resonance intervals).

---

## Current Proof Status

**Gap A: PROVED for ALL composite n.**

The five-line summary of the proof:
1. Even composite: eu = n−1 gives e* = n−2, gcd = 2.
2. Odd prime power p^k: explicit eu gives e* with factor p.
3. Odd n with ≥2 distinct primes: candidates 2n/p_min − 1 and 2n/p_min − 2 both lie in the resonance interval (2n/(p_min+1), 2n/p_min) where any unit eu gives e* = p_min·eu − n ≡ 0 (mod p_min), gcd > 1. At most one candidate is a non-unit (proved by modular contradiction). So at least one is always a valid witness.
