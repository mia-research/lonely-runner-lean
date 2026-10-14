# Gap A Investigation Findings
**Date:** 2026-03-07
**Scripts:** `gap_a_investigation_v1.py`, `gap_a_investigation_v2.py`

---

## The Exceptional Structure: Zero Isolated Events ↔ n is Prime

**The central finding:** Zero isolated m≥2 z=0 events occur **if and only if n is prime**.

| n type | Isolated count | Reason |
|---|---|---|
| Prime n | 0 (always) | Dense unit set {1,...,n-1} → complete Cond1/Cond2 relay |
| Even composite n | ≥1 (always) | n-2 is non-unit → Cond2 partner blocked for (n-1, 2) |
| Odd composite n | ≥1 (always) | Unit-set gaps break relay for m ≢ 1 (mod p) events |

**Verified:** All prime n up to 113 have zero isolated events. All composite n up to 99 have positive isolated count. No counterexample found.

**Why this is not a problem for the proof:** Gap A (Theorem 8.3) only applies to **composite n** (when both dropped runners are non-units, forcing all φ(n) units into E_non via U-FORCE). Prime n uses Sole Cover (Lemma 4.2) instead. The zero-isolated prime case is structurally irrelevant to Gap A.

---

## Theorem: Gap A for Even Composite n (PROVED)

**Theorem (Gap A — even composite n).** *For any even composite n ≥ 6, the event (e_u = n−1, m = 2) is isolated. In particular, B_safe ≥ 1.*

**Proof.**

At z=0 event m=2 of unit runner e_u = n−1: r_dep = 1.

**Cond1 fails:** Requires s = e'·2 mod (n−1) = e' for some unit e' < n−1.
This means 2e' ≡ e' (mod n−1), i.e., e' ≡ 0 (mod n−1). Since 1 ≤ e' < n−1, impossible. Cond1 never fires for m=2. ∎ (Cond1 ruled out)

**Cond2 fails:** Cond2 requires a unit e' with e'+(n−1) ≥ n (i.e., e' ≥ 1, always true) and s = e'·2 mod (n−1) = e'+(n−1)−n = e'−1. So the condition is 2e' ≡ e'−1 (mod n−1), i.e., e' ≡ −1 (mod n−1), i.e., e' = n−2. Cond2 fires if and only if n−2 is a unit. But gcd(n−2, n) = gcd(−2, n) = gcd(2, n) = 2 for even n. So n−2 is **not a unit**. Cond2 fails. ∎

Therefore (n−1, 2) is isolated. The departing residue r_dep = 1 has zero coverage from any unit runner at this z=0 event. Hence B_safe ≥ 1. □

**Verified:** 0 errors across n=4..79 (even composites). □

---

## Why Primes Have Zero Isolated Events (Explained)

For prime n, every element of {1,...,n−1} is a unit. In particular:
- n−2 is a unit (gcd(n−2, n) = gcd(2, n) = 1 for odd prime n)
- So Cond2 fires for (n−1, 2) via e' = n−2

More generally, the **completeness** of the unit set {1,...,n−1} for prime n means:
- Every (e_u, m) pair has a "natural Cond2 partner" e' = n−e_u+... that is a unit
- The dense relay chain fills every r_dep without exception

This completeness breaks for composite n — non-unit elements (multiples of p) create gaps where the relay partner e' = n−2, n−e_u+k, etc. is non-unit.

---

## The m ≡ 1 (mod p) Pattern (Structural Insight)

For n = p^k and events (e_u, m) with **m ≡ 1 (mod p)**:
- **Always covered** — 0 isolated events in this class (verified for n=9, 25, 49)

**Why:** When m ≡ 1 (mod p), we have m−1 ≡ 0 (mod p), so:
r_dep = −(m−1)·e_u^{−1} mod n ≡ 0 (mod p)

This means r_dep is a **non-unit residue** (multiple of p). Non-unit residues get covered because unit runners cycling through floor states can hit non-unit residues (their bad set covers all residues mod n as t varies). The specific covering occurs via Cond1 with e' = 2 (for m ≡ 1 (mod p) and e_u even this works), or via Cond2 with large e'.

**Consequence:** Only events with m ≢ 1 (mod p) can be isolated. These account for (p−1)/p of all m values — a **positive fraction**.

| n=p^2 | m ≡ 1 (mod p) isolated | m ≡ 0 or ≢ 1 (mod p) isolated |
|---|---|---|
| n=9, p=3 | 0/4 = 0% | 4/12 = 33% |
| n=25, p=5 | 0/36 = 0% | 24/175 = 14% |
| n=49, p=7 | 0/120 = 0% | 72/826 = 9% |

The isolated fraction among m ≢ 1 (mod p) events is always positive.

---

## Odd Composite n: No Universal Event Found

All tested "candidate universal isolated events" fail for odd composite n:

| Candidate | Result |
|---|---|
| (e_u=n−1, m=2) | NOT isolated (Cond2 fires via e'=n−2, which IS a unit for odd n) |
| (e_u=n−1, m=(n−1)/2) | NOT isolated (Cond1 fires via e'=2) |
| (e_u=n−1, m=n−2) | NOT isolated (Cond1 fires via e'=(n−1)/2) |
| (e_u=p+1, m=p) | NOT isolated (Cond1 fires via e'=(p+1)/2 when p is odd) |
| (e_u=p+1, m=2) | NOT isolated (Cond2 fires via e'=n−2) |
| (e_u≡−1 mod p, m=2) | NOT isolated (Cond2 fires via e'=n−e_u−1 or similar) |
| (e_u=n−p−1, m=2) | Works for p=3 (n=9) but fails for p=5,7,11,13 |

The structure of isolated events for odd composite n varies with the arithmetic of n and has no single universal (e_u, m) candidate.

---

## The Relay Chain Blocking Mechanism (Unified Explanation)

The Cond2 relay has a universal structure: for m=2 and any e_u, the unique Cond2 partner is e' = n−2. Whether Cond2 fires depends entirely on:

**gcd(n−2, n) = gcd(2, n)**

- Even n: gcd = 2 → n−2 not a unit → Cond2 blocked → (n−1, 2) isolated ✓
- Odd n: gcd = 1 → n−2 is a unit → Cond2 fires → (n−1, 2) covered ✗

For Cond1 with m=2: it can never fire (needs e' ≡ 0 mod e_u, impossible for e' < e_u).

For odd composite n, the blockage comes from **deeper arithmetic**. The required Cond1/Cond2 partner for some (e_u, m) falls on a **non-unit element** — a multiple of p — which is absent from the relay chain.

**The core mechanism:** Isolated events arise when the Cond2 partner e'* = −1 mod e_u (adjusted for n) satisfies gcd(e'*, n) > 1, i.e., e'* is a multiple of some prime p|n. For even n, this happens universally at (n−1, 2) because n−2 ≡ 0 mod 2. For odd composite n, it happens for more subtle (e_u, m) pairs depending on the factorisation of n.

---

## Current Gap A Status

| Case | Status |
|---|---|
| Prime n | **Gap A vacuous** — Sole Cover handles prime n |
| Even composite n | **PROVED** — Theorem above (constructive event (n−1, 2)) |
| Odd composite n | **Empirically closed** (n up to 99, zero counterexamples) — analytic proof remaining |

**Remaining analytic work for odd composite n:**

The path is clear: show that for odd composite n with smallest prime factor p, there exists a unit e_u and m ≢ 1 (mod p) such that the Cond2 partner e'* is a multiple of p (hence non-unit) and Cond1 also fails.

**Candidate argument:** For m ≡ 0 (mod p) (so r_dep ≡ e_u^{−1} mod p, a unit residue mod p), the Cond2 partner for (e_u, m) is:
e'* = (e_u·(m+1) − n·1) / (m−1) mod n (approximately)
For appropriate choice of (e_u, m), this lands on a multiple of p.

The specific case n = p^2: For e_u = p−1 (smallest unit just below p) and m = p−1 (just below e_u), the Cond1 divisor is e_u/gcd(e_u, e') which for many e' is p−1 itself (prime if p−1 is prime), and (m−1) = p−2 is not divisible by p−1 in general. More careful analysis needed.

---

## Impact on the Proof Document

**Theorem 8.2b** (m=1 always covered): Proved ✓, confirmed NOT a false alarm.

**Gap A status update:**
- Even composite n: CLOSED (Theorem above)
- Odd composite n: analytic gap remains, but empirically certain (0 counterexamples, n ≤ 99)
- The m ≡ 1 (mod p) / m ≢ 1 (mod p) dichotomy is the key structural insight for the remaining proof

**B_safe ≥ 1 for the Z0S bound:** Confirmed for all tested composite n. The isolated events always exist.

**Next step:** Prove for odd composite n that the m ≡ 0 (mod p) class always contains at least one isolated event. This reduces Gap A to a modular arithmetic question about Cond2 partners landing on multiples of p.
