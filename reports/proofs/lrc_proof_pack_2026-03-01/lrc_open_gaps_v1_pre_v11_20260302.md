# LRC Open Gaps — Current Frontier
**Date:** 2026-03-01 | **Source authority:** `lrc_ap_grid_extremizer_theorem_sequence_v10.md` §15–16

---

## What Is Closed

The following are **unconditionally proved or certified** (see `lrc_claim_status_table_v1.csv`):

- Lemma P, Lemma E Case 1, Irrational branch.
- Case-2 canonical (L=n, L=2n), degree-bound branch, lower/top band safety.
- Two-Miss Transition Mechanism (TM1/TM2/TM3) and band-density lemmas (D.1'/D.2').
- Template Certification Protocol (TCP) as a general proof schema.
- All 145 all-distinct one-divisible templates for **n ∈ {7, 8, 9, 10, 11}** certified
  via 5,514 exact finite checks, zero violations.
- **Gap 1 (TCP, all prime n ≥ 7):** Proved analytically via lcm(E_fixed) lower bound
  + TM3 density cap on lower band + quasi-lower band for M < n. (2026-03-02)
- **Gap 2 (multi-divisible, standard case):** Proved via anchor universality (n² ∤ e → all
  n−1 anchors in B_div) + anchor safety from Gap 1 argument. (2026-03-02)
- **Gap 3 (composite n, all-distinct Case-2):** Proved via Lemma G3.1 (lower-band safe set)
  + anchor b₁ = L/n. Key: gcd-conflict runners' bad_a ⊆ {a:gcd(a,n)>1} at t=0, so
  A_{b₁} ⊇ (Z_n)*, giving |A_{b₁}| ≥ φ(n). No modular inverse needed. (2026-03-02)
- **Gap 4 (S3, prime n):** Proved via Anchor z-Property. For prime n at anchors j=1,...,n−1:
  z_e=1 → each runner contributes only 1 bad a → |union_bad| ≤ n−1−k < n → δ ≥ k+1.
  Gives x_0 ≥ 2n−1 ≥ n−1 for all prime n, all Case-2 tuples. (2026-03-02)

---

## Open Items

### Gap 1 — TCP Extension to All Prime n  ✓ CLOSED (2026-03-02)

**Theorem G1:** For every prime n ≥ 7 and every all-distinct one-divisible template
family F: x_0(F, M) ≥ φ(n) for all admissible M.

**Status: PROVED analytically.** Full proof in `lrc_paper_draft_v1.md` §8 Theorem G1.

**Proof splits on M:**
1. M ≥ M_0(F): D.1'/D.2' asymptotic bound (proved for all prime n). ✓
2. M ∈ T(F), M ≥ n: Lower band |I_lo| ≥ L_0/(n−1); TM3 gives safe count ≥
   L_0/n = lcm(E_fixed) ≥ n−1 (key lemma below). ✓
3. M ∈ T(F), M < n: Quasi-lower band Q (all runners t=0) has size lcm(E_fixed)·(n−M)
   ≥ lcm(E_fixed) ≥ n−1; all fibers safe (union_bad = n−1, one missing). ✓

**Key lemma:** For n ≥ 7 prime, |E_fixed| = n−3 distinct values from {1,...,n−1}, so
lcm(E_fixed) ≥ lcm(1,...,n−3) ≥ 2^(n−3) ≥ n−1.

**Base cases n ≤ 6:** Covered by known LRC (Bohman–Holzman–Kleitman, 2001).
**Batch data:** n=7..11 provide independent computational confirmation (5,514 checks, 0 violations).

---

### Gap 2 — Multi-Divisible Templates (|E_div| ≥ 2)  ✓ STANDARD CASE CLOSED (2026-03-02)

**Theorem G2 (standard case):** For prime n ≥ 7 and any Case-2 tuple E with n² ∤ e
for all e ∈ E_div: x_0(E) ≥ φ(n).

**Status: PROVED for standard case.** Full proof in `lrc_paper_draft_v1.md` §8 Theorem G2.

**Proof sketch:**
1. **Anchor universality:** For prime n, gcd(j,n)=1 for j ∈ {1,...,n−1}, so b_j ∈ B_div
   iff n² ∤ e for all e ∈ E_div. Standard case → all n−1 anchors in B_div. ✓
2. **Anchor safety:** |A_{b_j}| ≥ 1 for each anchor, by the same quasi-lower-band /
   union_bad < n argument as Gap 1 (n−|E_non| ≥ 1 missing residue). ✓
3. B_safe ≥ n−1 → x_0 ≥ φ(n). □

**Residual open sub-case:** E_div contains a speed e with n² | e. Then all anchors are
excluded from B_div; B_safe ≥ n−1 requires a separate argument. Empirically zero
violations (n=3..12). B_div Bonferroni bound and degree-branch may cover this.

---

### Gap 3 — Composite n  ✓ ALL-DISTINCT CASE CLOSED (2026-03-02)

**Theorem G3:** For composite n ≥ 4 and any all-distinct gcd-1 Case-2 tuple E with all
non-divisible speeds in {1,...,n−1}: x_0(E) ≥ φ(n).

**Status: PROVED analytically.** Full proof in `lrc_paper_draft_v1.md` §8 Theorem G3.

**Proof sketch (Lemma G3.1 + Theorem G3):**
1. **Lower-band safe set (Lemma G3.1):** At fiber b > 0 with t_e(b)=0 (z=1):
   - gcd(e,n)=1 runner: bad_a = {0} ⊆ {a:gcd(a,n)>1}
   - gcd(e,n)=d>1 runner: bad_a = {k·(n/d): k=0,...,d−1} ⊆ {a:gcd(a,n)>1}
   - Therefore A_b ⊇ {a:gcd(a,n)=1} = (Z_n)*, giving |A_b| ≥ φ(n). ✓
2. **Anchor b₁ = L/n hits lower band:** Since all non-divisible speeds ≤ n−1 < n,
   t_e(b₁) = ⌊e/n⌋ = 0 for all e ∈ E_non. ✓
3. **b₁ ∈ B_div:** Each e_div = f·n ∈ E_div gives e_div·b₁ = f·L ≡ 0 mod L. ✓
4. **x_0 ≥ |A_{b₁}| ≥ φ(n).** □

**Key insight:** The old lemma "floor(e·j/n) mod d ∉ {0,d−1}" is FALSE (226 counterexamples
for n=4..19). The correct argument avoids this: we use the LOWER BAND (t=0 at b₁), not
general anchors. At t=0, gcd-conflict runners are active but their bad_a is confined to
multiples of n/d — all non-coprime to n. The coprime residues (Z_n)* survive. ✓

**Residual open (multi-speed-band):** Tuples with non-divisible speeds e > n (e.g., n+1, n+2).
These are not all-distinct Case-2 in the standard parameterization. Empirically 0 violations.

**Numerical verification:** n ∈ {4,6,8,9,10,12,15}: |A_{b₁}| = φ(n) exactly in each case.

---

### Gap 4 — Universal S3 (Full Structural Chain)  ✓ PRIME n PROVED (2026-03-02)

**Theorem S3 (prime n):** For any prime n ≥ 3 and any gcd-1 Case-2 tuple E (|E|=n−1,
k = |E_div| ≥ 1): x_0(E) ≥ k + (k+1)(n−1) ≥ 2n−1 ≥ n−1.

**Status: PROVED for all prime n.** Full proof in `lrc_s3_proof_prime_n_v1.md`.

**Proof sketch (Anchor z-Property Method):**
1. **Anchor membership (Lemma S3.A):** Each b_j = j·L/n (j=0,...,n−1) is in B_div. ✓
2. **Anchor z-property (Lemma S3.B, prime n):** For j ∈ {1,...,n−1} and any e ∈ E_non:
   z_e(b_j) = 1. Proof: z_e = 1 iff n∤ej; for prime n with gcd(e,n)=1 and j < n: n∤ej. ✓
3. **Delta at non-trivial anchors (Lemma S3.C):** z_e=1 → bad_a(e) = 1 element. So
   |union_bad(b_j)| ≤ |E_non| = n−1−k < n → δ(b_j) ≥ k+1. ✓
4. **Delta at b=0 (Lemma S3.D):** At t=0, z=0: bad_a ≤ n−k elements → δ(b_0) ≥ k. ✓
5. **Sum:** x_0 ≥ k + (k+1)(n−1) ≥ 2n−1 ≥ n−1. □

**Key insight:** For prime n, z_e = 1 at ALL n−1 non-trivial anchor fibers. This restricts
each non-divisible runner to a SINGLE bad a-value per fiber (not 2). With n−1−k runners
and n positions, the strict cardinality gap n − (n−1−k) = k+1 ≥ 2 guarantees safety.

**Composite n residual (still open):** For composite n with gcd(e,n)=d>1, Lemma S3.B
fails (z_e can be 0 at non-trivial anchors when d|j). A modified argument is needed.
Empirically: zero violations, n=3..12. The Gap 3 lower-band argument already gives
x_0 ≥ φ(n) for all-distinct composite-n Case-2; the S3-style proof (x_0 ≥ n−1) for
composite n requires separate treatment.

**Role:** S3 for prime n gives a single-theorem Case-2 closure not requiring template
enumeration, for all prime n ≥ 3 simultaneously.

---

## Current Frontier (one paragraph)

The proof machinery is complete and Gaps 1–3 (all-distinct Case-2) are now closed. TM1/TM2/TM3
reduce Case-2 badness to a 2-point matching density problem; D.1'/D.2' convert this to an
explicit linear safe-mass lower bound; TCP certifies each prime-n template family; and the
lower-band safe-set argument (Lemma G3.1) closes composite n analytically without any modular
inverse. The three closed gaps jointly cover all gcd-1 Case-2 tuples in the standard all-distinct
parameterization for every n ≥ 4.

The two remaining open items are: (a) **Gap 2 residual** (n²|e sub-case — all anchors
expelled from B_div; empirically zero violations); and (b) **Gap 4 composite-n residual**
— the S3 bound x_0 ≥ n−1 for composite n. The Anchor z-Property proof of S3 breaks for
composite n because z_e can be 0 at non-trivial anchors when gcd(e,n) = d and d|j. The
Gap 3 lower-band argument already gives x_0 ≥ φ(n) for composite all-distinct Case-2;
extending to x_0 ≥ n−1 (> φ(n) for composite n) requires new input. Empirically zero
violations (n=4..12 exhaustive and random).
