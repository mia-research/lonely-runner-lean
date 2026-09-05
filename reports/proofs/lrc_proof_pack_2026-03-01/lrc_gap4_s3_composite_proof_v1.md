# Gap 4 / S3 Composite-n Structural Analysis (v1)
**Date:** 2026-03-03
**Status:** OPEN (partial analytic results + empirical characterisation)

---

## Overview

**Target (S3 universal):** For every gcd-1 Case-2 tuple E with |E|=n−1 and E_div≠∅:
```
|B_safe(E)| ≥ n−1
```
Equivalently: x_0(E) = Σ_{b∈B_div} δ(b) ≥ n−1.

This document records:
1. What is **proved analytically** (summarising prior results)
2. Key **new structural findings** from the Phase-1 diagnostic
3. **Failure analysis** of candidate routes (A, z=0 lemma, band coverage, anchor sum)
4. **Remaining open core**

---

## 1. Proved Sub-cases (Prior Work)

### 1.1 L = n (canonical, C2-CANON — PROVED)
For the smallest possible LCM (L=n, achieved iff all non-divisible speeds = 1 and single divisible speed n):
- B_div = {1,...,n-1}, |B_div| = n-1.
- For all b ∈ B_div: t_e(b) = 0, z_e(b) = 0 for all e ∈ E_div, and union bad_a over E_non = ∅.
- C_bad = 0, B_safe = n-1 = φ(n) for n prime; B_safe = n-1 ≥ φ(n) for composite n.

### 1.2 L = 2n (second-canonical, C2-2ND — PROVED)
For the second-smallest LCM regime L=2n:
- B_div has fibers: for k_div=1, E_div={n}: B_div = {b: L/n ≤ b ≤ (n-1)L/n} = {2,...,2(n-1)}.
  |B_div| = 2(n-2)+1 = 2n-3 for prime-style; exact count depends on E_non structure.
- C_bad = 0 (proved analytically): the lower and top band fibers are exactly B_div, and each is safe.
- B_safe = B_div ≥ 2(n-2) ≥ n-1 for all n ≥ 3.

**Empirical confirmation (Phase-1 data):** For all L=2n tuples in the diagnostic:
- n=4: 18 tuples, B_safe = B_div ∈ {4,6}, min B_safe = 4 = n. ✓
- n=5: 50 tuples, B_safe = B_div = 7. ✓
- n=6: 1140 tuples, B_safe = B_div = 9. ✓
- n=7: 602 tuples, B_safe = B_div = 11. ✓
- Zero violations (C_bad = 0 universally for L=2n). ✓

### 1.3 Degree-bound branch (C2-DEG — PROVED)
If |E_non| ≤ ⌊(n-1)/2⌋: C_bad = 0 (union bad_a has < n elements everywhere in B_div).

---

## 2. New Structural Findings (Phase-1 Diagnostic)

### 2.1 Biconditional: Tight Cases ↔ Canonical Regime

**Finding:** Across 88,626 tuples (exhaustive n∈{4,5,6,7}, stress n∈{8,9,10,12}):
```
B_safe = n-1  ⟺  L = n
```
- Zero tight cases for any L>n.
- For L>n: min B_safe = n (strictly greater than n-1).

Specific values at the minimum (all occur at L=2n, C_bad=0):

| n | min B_safe (L>n) | at L |
|---|---|---|
| 4 | 4 = n | L=8=2n |
| 5 | 7 > n | L=10=2n |
| 6 | 9 > n | L=12=2n |
| 7 | 11 > n | L=14=2n |

The biconditional analytically reduces S3 to two cases:
- **Case A (L=n):** B_safe = n-1. ← PROVED (C2-CANON)
- **Case B (L>n):** B_safe ≥ n ≥ n-1. ← OPEN (zero empirical violations)

### 2.2 Tightest L>n Case: n=4, L=12=3n

The only case in the diagnostic data with B_safe = n = 4 and C_bad > 0 is
**E = permutations of {1,3,4}** (6 tuples), all with L=12, B_div=7, B_safe=4, C_bad=3.

Fiber-by-fiber analysis:
- B_div = {3,4,5,6,7,8,9}
- Obstructed: {5,6,7} (length 3 = n-1, one contiguous block)
- Safe: {3,4,8,9} (two runs of length 2)

The obstruction mechanism:
- E_non = {1,3}. bad_a(1,b) = {0,3} for all b ∈ (0,L) (constant — runner 1 always contributes {0,3}).
- bad_a(3,b) = {1,2} for b ∈ {5,6,7} (complementary pair).
- Union = {0,3}∪{1,2} = Z_4 for those b. ← OBSTRUCTED.

The safe extra fiber:
- b=4 is safe because z_3(4)=0 (3·4=12≡0 mod L=12).
- At z_e=0 for e=3 (gcd(3,4)=1): bad_a(3,4) = {1} only (one congruence, strict inequality x>(n-1)L fails at boundary). Union = {0,3}∪{1} = {0,1,3} ≠ Z_4. SAFE.

This is the **z=0 boundary safe-fiber mechanism** for n=4.

### 2.3 Obstruction Block Structure

Key metric: max_obstr_run (longest consecutive obstructed block in B_div).

Empirical universal bound (zero violations):
```
max_obstr_run < (n-1) · B_div / n
```
Equivalently: B_safe/B_div ≥ 1/n always.

This means a single obstructed block can remove at most a (1-1/n) fraction of B_div.

### 2.4 Bad_a Formula at z=0 (Key Structural Lemma)

**Lemma (z=0 bad_a reduction):**
For any e ∈ E_non and any b ∈ B_div with e·b ≡ 0 (mod L) (i.e., z_e(b)=0):
```
bad_a(e,b) = {a ∈ Z_n : e·a ≡ -t_e(b) (mod n)}
```
This set has exactly gcd(e,n) elements.

In particular, for gcd(e,n)=1: **bad_a(e,b) has exactly 1 element at z=0 fibers**.

**Proof:** At z=0: e·(a·L+b) mod N = q_a·L where q_a = (e·a+t_e) mod n.
Bad iff q_a·L < L (since q_a·L > (n-1)·L requires q_a > n-1, impossible).
So bad iff q_a = 0 iff e·a ≡ -t_e (mod n). □

**Corollary (n=4, gcd(e,n)=1):**
For any Case-2 tuple with n=4 and k_non = |E_non| = 2 runners (both coprime to 4):
At any z=0 fiber of either runner, the union bad_a has ≤ 1+2 = 3 < 4 = n elements → SAFE.

This proves: every z=0 event boundary of a coprime-to-4 runner in B_div is safe, giving ≥ 1 additional safe fiber beyond the two bands.

---

## 3. Failed Routes

### Route A: Good Anchors

**Hypothesis:** The good non-trivial anchors (b_j = jL/n with z_e(b_j)=1 for all e ∈ E_non, j≥1) always provide ≥ n-1 safe mass.

**Status: DISPROVED.**
858 tuples in the data have good_nontrivial_safe = 0 (no good nontrivial anchor is safe) yet have large B_safe.
Example: n=4, E=(1,7,8), B_safe=16 ≫ n-1=3, but all good anchors are obstructed.

### Route B: z=0 Fibers Always Safe

**Hypothesis:** Every z=0 fiber in B_div is safe.

**Status: FALSE for n≥6.**
Counter-example: n=6, E=[1,1,4,5,6], b=30 (z_4(30)=0), union={0,1,2,3,4,5}=Z_6. OBSTRUCTED.
Mechanism: even though bad_a(4,30) is small (2 elements, gcd(4,6)=2), the other 3 runners together cover the rest of Z_6.
**The lemma holds for n=4 (gcd constraint forces union < 4)**, but fails for n≥6 where more runners can cover the complement.

### Route C: Band Coverage (|I_lo|+|I_hi| ≥ n-1)

**Hypothesis:** The lower and top bands always provide ≥ n-1 safe fibers.

**Status: FALSE.**
35,320 out of 87,818 L>n tuples have |I_lo|+|I_hi| < n-1.
Failure mode: when e_max > n (non-divisible speed exceeds n), the band formula gives empty bands.
Example: n=4, E=[1,4,5]: e_max=5 > n=4, I_lo and I_hi both empty.

The C2-BANDS result (proved) guarantees lower and top bands ARE safe, but their size relative to n-1 varies.

### Route D: Anchor Sum (∑_j δ(b_j) ≥ n-1)

**Hypothesis:** The sum of δ(b_j) over all n-1 non-trivial anchors is ≥ n-1.

**Status: FALSE.**
Counter-examples:
- n=4, E=[1,3,4]: anchor delta sum = 2 < n-1=3. (B_safe=4 via non-anchor fibers.)
- n=7, E=[1,2,3,4,5,7]: anchor delta sum = 2 < n-1=6.

The **per-runner** anchor sum satisfies:
```
∑_{j=1}^{n-1} |bad_a(e,b_j)| = 2(n-1) for gcd(e,n)=1
```
(not n-1 as hoped). This is 2× too large for the inclusion-exclusion bound to give ≥ n-1.

---

## 4. Correct Formula: bad_a at Anchors

For anchor b_j = j·L/n (j ∈ {1,...,n-1}) and e ∈ E_non:
- Let t_e^j = floor(e·j/n), r_e^j = (e·j mod n)·(L/n).
- z_e(b_j) = 1 iff n ∤ e·j.

**When z_e=1:**
bad_a(e,b_j) = {a: e·a ≡ -t_e^j (mod n)} ∪ {a: e·a ≡ -t_e^j-1 (mod n)}.
(Only the first class has solutions if gcd(e,n) ∤ t_e^j, etc.)

**When z_e=0:**
bad_a(e,b_j) = {a: e·a ≡ -t_e^j (mod n)}.
Size = gcd(e,n) if gcd(e,n)|t_e^j, else 0.

The total anchor coverage ∑_j |∪ bad_a| can be close to n(n-1), leaving little room for ∑_j δ(b_j) ≥ n-1. The anchor-based proof route requires taking differences (inclusion-exclusion), not just the first-order bound.

---

## 5. Key Empirical Evidence Summary

From lrc_gap4_s3_composite_diag_v1.py (88,626 tuples, composite n∈{4,6} exhaustive + prime n∈{5,7} + stress n∈{8,9,10,12}):

| Claim | Violations | Total tested |
|---|---|---|
| B_safe ≥ n-1 | 0 | 88,626 |
| B_safe ≥ n (L>n) | 0 | 87,818 |
| B_safe = n-1 ↔ L=n | 0 | 88,626 |
| max_obstr_run < (n-1)·B_div/n | 0 | 88,626 |
| B_safe/B_div ≥ 1/n | 0 | 88,626 |

The biconditional and the stronger B_safe ≥ n bound for L>n are robustly established.

---

## 6. Proof of n=4 Partial Case

**Theorem (S3 for n=4, all valid Case-2 tuples):**
For any gcd-1 Case-2 tuple E with n=4 (|E|=3, some e divisible by 4): B_safe ≥ 3 = n-1.

**Proof sketch:**
- L=n=4: canonical case, B_safe=3=n-1. (C2-CANON, proved.)
- L=2n=8: C2-2ND gives B_safe=B_div≥4=n>3. ✓
- L≥3n: By case analysis on k_div:
  - k_div≥2: k_non≤1. Single non-div runner contributes ≤2 bad a-values at each b → union ≤2 < 4=n → C_bad=0, B_safe=B_div≥n-1. ✓
  - k_div=1 (one divisible speed 4): k_non=2 (two non-div runners, both coprime to 4).
    - The lower and top bands (I_lo, I_hi) provide |I_lo|+|I_hi| safe fibers (C2-BANDS).
    - Even when |I_lo|+|I_hi| = n-1=3: there exist z=0 event boundaries of the non-div runners within B_div that are not in the bands. By the z=0 bad_a reduction lemma (gcd(e,4)=1 → bad_a has 1 element at z=0), any such fiber has union ≤ 1+2 = 3 < 4 and is safe. This adds ≥1 extra safe fiber, giving B_safe ≥ n=4 ≥ n-1=3. ✓
    - Rigorous verification: all 330 n=4 tuples exhaustively checked, 0 violations.

**Remark:** The key step "there exist z=0 boundaries outside the bands" requires showing the two bands don't exhaust all z=0 event boundaries of the non-div runners. This holds for L≥3n (verified, but formal proof of the geometry needs further work).

---

## 7. Open Core

**What remains to prove for full S3 closure:**

For n≥6 composite and L > 2n: need to show B_safe ≥ n-1.

The key difficulty: the z=0 boundary lemma fails (n=6 counter-example), the band argument fails (e_max > n cases), and anchor sums are too large.

**Most promising remaining approach:** Show that for the event-cell structure (Lemma S2), the product of bad-a signatures across runners cannot achieve full Z_n coverage for more than (B_div - n+1) consecutive cells. This would follow from:

**Conjecture (Complementarity Bound):** For any gcd-1 Case-2 tuple E with L>n and any consecutive run of B_div fibers {b, b+1,...,b+k-1} where |∪ bad_a(e,b')| = n for all b' in the run: k ≤ B_div - n.

This conjecture is supported by the max_obstr_run empirical data (zero violations of max_obstr_run ≥ B_div-n+1). A proof via the event-cell transition structure (each transition changes bad_a by ≤ gcd(e,n) elements for the transitioning runner) is the next analytic target.

**Partial progress:** The single-run bound (C_bad ≤ max_obstr_run when n_obstr_runs=1) gives B_safe ≥ n when the max_obstr_run < B_div-n. This covers all single-block cases. Multi-block cases require additional analysis.

---

## 8. Status Assessment

| Sub-case | Status | Evidence |
|---|---|---|
| L=n | PROVED | C2-CANON analytical |
| L=2n | PROVED | C2-2ND analytical |
| n=4, all L | OPEN-PROGRESS (sketch) | n=4 partial proof + 330 exhaustive checks; z=0 boundary existence step not yet formalised |
| n prime, one-div all-distinct | PROVED | G1 closure theorem (§17.20) — scoped to prime one-divisible all-distinct family |
| n=6, L>2n | OPEN | Zero violations, no analytic proof |
| n≥8 composite, L>2n | OPEN | Stress-tested, no analytic proof |
| Universal (all n, all L) | OPEN | 88,626 empirical checks, zero violations |

---

## References

- `lrc_case2_structural_necessity_chain_v1.md` — S1/S2/S3 formal chain
- `lrc_s3_proof_prime_n_v1.md` — Prime-n proof (anchor z-property)
- `lrc_gap4_s3_composite_diag_v1.py` — Phase-1 diagnostic script
- `lrc_gap4_s3_composite_diag_rows_v1.csv` — 88,626-row numerical evidence
- `lrc_gap4_s3_composite_diag_summary_v1.md` — Aggregate summary
- `lrc_claim_status_table_v1.csv` — Canonical claim tracking
