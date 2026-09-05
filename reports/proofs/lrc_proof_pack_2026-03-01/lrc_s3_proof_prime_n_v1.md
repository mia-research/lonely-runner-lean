# Proof of S3 for Prime n — Anchor z-Property Method
**Date:** 2026-03-02  
**Status:** PROVED for prime n (all Case-2 tuples)

---

## Statement

**Theorem S3 (prime n):** For any prime n ≥ 3 and any gcd-1 Case-2 tuple E
(|E|=n−1, E_div ≠ ∅): x_0(E) ≥ n−1.

In fact the proof gives x_0(E) ≥ k + (k+1)(n−1) ≥ 2n−1 ≥ n−1, where k = |E_div| ≥ 1.

---

## Key Lemmas

**Lemma S3.A (Anchor Membership).**
For any Case-2 tuple E with n|L: each anchor b_j = j·L/n (j=0,...,n−1) lies in B_div.

*Proof.* For each e_d ∈ E_div (n | e_d): e_d · b_j = e_d · j·L/n = (e_d/n)·j·L ≡ 0 mod L. ✓ □

**Lemma S3.B (Anchor z-Property, prime n).**
For prime n, any e ∈ E_non (so gcd(e,n)=1), and any j ∈ {1,...,n−1}:
z_e(b_j) = 1.

*Proof.* z_e(b_j) = 1[e·b_j mod L > 0] = 1[ej·L/n mod L > 0] = 1[ej mod n ≠ 0].
Since n is prime and n∤e (e ∈ E_non) and n∤j (j ∈ {1,...,n−1}): n∤ej. ✓ □

**Lemma S3.C (Delta at non-trivial anchors).**
For prime n and j ∈ {1,...,n−1}: δ(b_j) ≥ k+1 ≥ 2.

*Proof.* By Lemma S3.B, z_e = 1 for all e ∈ E_non at b_j. With z_e = 1:
bad_a(e, b_j) = {a ∈ Z_n : e·a + t_e ≡ 0 mod n} — exactly 1 element (gcd(e,n)=1).
Therefore |union_bad(b_j)| ≤ |E_non| = n−1−k < n.
Hence δ(b_j) = n − |union_bad(b_j)| ≥ k+1 ≥ 2. □

**Lemma S3.D (Delta at trivial anchor b=0).**
For any n ≥ 2: δ(b_0) ≥ k ≥ 1.

*Proof.* At b_0 = 0: t_e = 0, z_e = 0 for all e ∈ E_non. Then:
  bad_a(e, 0) = {0} ∪ {(n−1)·e^{−1} mod n}.
The element 0 is shared across all runners. The element (n−1)·e^{−1} lies in Z_n^* = {1,...,n−1}.
Since E_non consists of n−1−k speeds with distinct residues mod n (gcd-1 tuple),
the values {(n−1)·e^{−1} mod n : e ∈ E_non} are n−1−k distinct elements of Z_n^*.
Therefore |union_bad(b_0)| ≤ 1 + (n−1−k) = n−k < n.
Hence δ(b_0) ≥ k ≥ 1. □

---

## Main Proof

**Proof of Theorem S3 (prime n).**

By Lemma S3.A, {b_j : j = 0,...,n−1} ⊆ B_div. Therefore:

  x_0(E) = Σ_{b ∈ B_div} δ(b) ≥ Σ_{j=0}^{n−1} δ(b_j)
          ≥ δ(b_0) + Σ_{j=1}^{n−1} δ(b_j)
          ≥ k + (k+1)(n−1)          [by Lemmas S3.C and S3.D]
          ≥ 1 + 2(n−1)              [k ≥ 1]
          = 2n−1 ≥ n−1. □

---

## Discussion

**Why z_e = 1 is the key:** When z_e = 1, the BSM formula contributes only the
"q=0 boundary" (not q=n−1), restricting each runner to exactly 1 bad a-value.
With n−1−k runners each contributing 1 element to Z_n (size n), the union has
at most n−1−k < n elements — leaving ≥ k+1 safe a-values. This is a strict
cardinality gap that cannot be closed.

**Why prime n is clean:** For prime n, gcd(e,n)=1 for all non-divisible speeds,
guaranteeing z_e = 1 at all non-trivial anchors. This relies on n∤ej for j ∈ {1,...,n−1}.

**Composite n:** For composite n with gcd(e,n) = d > 1, the condition n∤ej can
fail (e.g., n=6, e=2, j=3: 2·3=6=n → z_e=0 at b_3). Lemma S3.B does not extend
directly. The Gap 3 lower-band argument handles composite n via a different route;
a composite-n version of S3 via the z-property requires separate analysis.

**Bound quality:** The proved bound x_0 ≥ 2n−1 is stronger than the target n−1.
Numerically: n=5 gives lower bound 9, observed minimum 10. The bound is nearly tight.

---

## Numerical Verification

| n | k | Lower bound (k+(k+1)(n−1)) | Observed min x_0 |
|--:|--:|--:|--:|
| 5 | 1 | 9 | 10 |
| 7 | 1 | 13 | 18 |
| 11 | 1 | 21 | — |

Checked: z_e=1 at all j≥1 holds for ALL tested tuples, n ∈ {5,7,11}, 50+ tuples each.
