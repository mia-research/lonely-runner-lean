# Supplement to: Universal Extremality of Arithmetic Progressions in the LRC

**Draft v1 — 2026-03-01**
*Companion to `lrc_paper_draft_v1.md`*

All paths relative to: `/Users/trentpalelei/Desktop/Math Ex/reports/proofs/lrc_proof_pack_2026-03-01/`

---

## S.A  Script Registry

Each script is a self-contained Python file that implements one step of the proof protocol.
No script does analytic work — all analytic arguments are in the theorem files. Scripts
perform exact integer arithmetic; no floating-point approximation is used in certificate generation.

### S.A.1  Check-Set Builder

**File:** `lrc_case2_d3_checkset_builder_v1.py`

**Purpose:** Given a template family F = (n, E_fixed, L_0), computes the explicit finite
check set T(F) = {1 ≤ M < M_0(F) : gcd(M, n·L_0) = 1} using the analytic threshold
M_0(F) from D.3 (Section 16.10 of v10).

**Inputs:** n (prime), E_fixed (tuple of fixed speeds), L_0 (lcm of E_fixed ∪ E_div).

**Outputs:** Sorted list of M values in T(F) with their coprimality certificates.

**Artifact:** `lrc_case2_d3_checkset_smoke_v1.csv` (smoke test for F1234, n=7).

**Claim supported:** TCP §6.1 (construction of T(F)).

---

### S.A.2  Single-Template Certifier

**File:** `lrc_case2_d3_certifier_v1.py`

**Purpose:** For a single template family F, runs exact x_0 computation (via integer
inclusion-exclusion or direct safe-point enumeration) for each M ∈ T(F) and reports violations.

**Algorithm:** For each M ∈ T(F):
1. Construct E_F(M) = E_fixed ∪ {M} ∪ E_div.
2. Compute L = L_0 · M, N = n · L.
3. For each b ∈ B_div (enumerated from B_div formula):
   - Compute union_bad(b) via exact bad_a formula.
   - If union_bad(b) = Z_n, increment C_bad.
4. Report B_safe = B_div − C_bad, x_0, violation flag.

**Artifact:** `lrc_case2_d3_certifier_n7_F1234_v1.csv` (6 rows for F1234).

**Claim supported:** Theorem D.3-cert(F1234) §6.2.

---

### S.A.3  Parallel Batch Certifier (n=7, n=11)

**File:** `lrc_case2_d3_batch_certify_v2.py`

**Purpose:** Enumerates all C(n−1, n−3) all-distinct one-divisible templates at given n,
runs the single-template certifier on each, aggregates results.

**Template enumeration:** For each (n−3)-element subset F of {1,...,n−1}, the template is
E_F(M) = F ∪ {M} ∪ {n}, with L_0 = lcm(F ∪ {n}).

**Design note:** Uses modular inverse computation (assumes n prime) for speed; suitable for
prime n.

**Artifacts:**
- `lrc_case2_d3_batch_rows_n7n11_v2.csv` — one row per template: n, E_fixed, L_0, a_F, b_F,
  M_0, R, T_size, violations, worst_M, worst_x0, worst_Bsafe.
- `lrc_case2_d3_batch_checks_n7n11_v2.csv` — one row per (template, M) check.
- `lrc_case2_d3_batch_summary_n7n11_v2.md` — aggregate counts.

**Claim supported:** Theorem D.3-cert (n=7, n=11) §6.3.

---

### S.A.4  Composite-Safe Batch Certifier (n=8,9,10)

**File:** `lrc_case2_d3_batch_certify_composite_v1.py`

**Purpose:** Identical logic to S.A.3 but avoids modular inverse assumptions in the
enumeration and bad_a computation. Uses direct residue checks so that composite n and speeds
e with gcd(e,n) > 1 are handled correctly.

**Key difference from v2:** bad_a(e,b) is computed without requiring gcd(e,n) = 1; the
formula uses direct modular arithmetic on the linear constraints rather than the inverse formula.

**Artifacts:**
- `lrc_case2_d3_batch_rows_n8n9n10_v1.csv`
- `lrc_case2_d3_batch_checks_n8n9n10_v1.csv`
- `lrc_case2_d3_batch_summary_n8n9n10_v1.md`

**Claim supported:** Theorem D.3-cert (n=8,9,10) §6.3.

---

## S.B  Claim-to-Evidence Map

| Claim ID | Statement | Evidence Type | Evidence Source |
|---|---|---|---|
| LP | x_0(A_n)=φ(n) | Analytic proof | v10 §3; verified n=3..8 |
| LE-C1 | x_0(E)≥φ(n) (no n-divisible speed) | Analytic proof | v10 §4; verified n=3..8 |
| IRR | Irrational branch | Analytic (Weyl) | `lrc_irrational_branch_sketch_v1.md` |
| C2-CANON | L=n case | Analytic | `lrc_case2_partial_analytic_v1.md` |
| C2-2ND | L=2n case | Analytic | `lrc_case2_partial_analytic_v1.md` |
| C2-DEG | Degree-bound branch | Analytic | v10 §4; 6TF §T3(a) |
| C2-BANDS | Lower/top band safety | Analytic | 6TF §T3(b)(c) |
| TM1 | Badness = exact 2-point match | Analytic | v10 §14 TM1 |
| TM2 | Free-pair rotation by −M^{-1} | Analytic | v10 §14 TM2 |
| TM3 | Density ≤ 1/n on frozen band | Analytic | v10 §14 TM3 |
| D.1' | C_bad(I) ≤ |I|/n + (2L_0+|Z_I|) | Analytic proof | v10 §16.7 |
| D.2' | B_safe ≥ ((n-1)/n)|I_tot|−(4L_0+ζ) | Analytic proof | v10 §16.8 |
| BAND-CONST | I_lo/I_hi frozen & sized | Analytic proof | v10 §16.9 Claims A B C |
| TCP | Protocol schema | Analytic proof | v10 §16.13 |
| PL.1 | t_M M-independent | Analytic + 160 checks | `lrc_case2_n11_pl_validation_v1.md` |
| F1246689-CRT | B_safe≥16M≥φ(11) | Analytic CRT | 6TF Sub-theorem 4.F; v10 §16.4 Cor |
| F1234-CERT | F1234 all M certified | Analytic bound + 6 exact checks | v10 §16.11; `_n7_F1234_v1.csv` |
| D3-n7 | n=7 all 15 templates | Finite certification (300 checks) | batch_rows_n7n11_v2.csv |
| D3-n8 | n=8 all 21 templates | Finite certification (581 checks) | batch_rows_n8n9n10_v1.csv |
| D3-n9 | n=9 all 28 templates | Finite certification (989 checks) | batch_rows_n8n9n10_v1.csv |
| D3-n10 | n=10 all 36 templates | Finite certification (1529 checks) | batch_rows_n8n9n10_v1.csv |
| D3-n11 | n=11 all 45 templates | Finite certification (2115 checks) | batch_rows_n7n11_v2.csv |
| S1 | Structural obstruction equivalence | Proved (definitions) | `lrc_case2_structural_necessity_chain_v1.md` |
| S2 | Feasible-signature path lemma | Proved (event decomp.) | `lrc_case2_structural_necessity_chain_v1.md` |
| S3-GENERAL | Universal S3 ≥ n−1 | Empirical only | `lrc_case2_aggregate_deficit_summary_v1.md` |
| TCP-GEN-N | TCP for all prime n | Open (scaling only) | v10 §16.10 |
| MULTI-DIV | Multi-divisible case | Open | v10 §16; 6TF |
| COMPOSITE | Composite n | Open (analytic) | v10 §15; D3-n8,9,10 (partial) |

---

## S.C  Artifact Index

### Theorem Sequence Files

| File | Role | Lines |
|---|---|---|
| `lrc_ap_grid_extremizer_theorem_sequence_v10.md` | **Canonical theorem sequence (v10)** | 1277 |
| `lrc_case2_6theorem_framework_v1.md` | 6-theorem Case-2 framework + F1246689 | 265 |
| `lrc_case2_structural_necessity_chain_v1.md` | S1→S4 structural chain | 132 |
| `lrc_case2_partial_analytic_v1.md` | Canonical + 2nd-smallest proofs | — |
| `lrc_case2_bdiv_gap_structure_v1.md` | B_div gap formula | — |
| `lrc_irrational_branch_sketch_v1.md` | Irrational branch (Weyl) | — |
| `lrc_case2_n11_pl_validation_v1.md` | PL.1 proof + period-121 correction | — |

### Batch Certification Artifacts

| File | n | Templates | Rows/Checks | Violations |
|---|--:|--:|--:|--:|
| `lrc_case2_d3_batch_summary_n7n11_v2.md` | 7, 11 | 60 | summary | 0 |
| `lrc_case2_d3_batch_rows_n7n11_v2.csv` | 7, 11 | 60 | 60 row | 0 |
| `lrc_case2_d3_batch_checks_n7n11_v2.csv` | 7, 11 | 60 | 2415 checks | 0 |
| `lrc_case2_d3_batch_summary_n8n9n10_v1.md` | 8, 9, 10 | 85 | summary | 0 |
| `lrc_case2_d3_batch_rows_n8n9n10_v1.csv` | 8, 9, 10 | 85 | 85 rows | 0 |
| `lrc_case2_d3_batch_checks_n8n9n10_v1.csv` | 8, 9, 10 | 85 | 3099 checks | 0 |
| `lrc_case2_d3_certifier_n7_F1234_v1.csv` | 7 | 1 | 6 checks | 0 |
| `lrc_case2_d3_checkset_smoke_v1.csv` | 7 | smoke | — | — |
| `lrc_case2_d3_certifier_smoke_v1.csv` | — | smoke | — | — |

### Supporting Scan/Summary Files

| File | Content |
|---|---|
| `lrc_case2_bsafe_summary_v1.md` | B_safe scan: 158,626 tuples, 0 violations |
| `lrc_case2_aggregate_deficit_summary_v1.md` | S3 empirical evidence (n=3..12) |
| `lrc_case2_s3_lb5_stress_summary_v1.md` | LB5 counterexamples at n=13,14,15 |
| `lrc_case2_s3_order_ladder_summary_v1.md` | LB5/LB7 comparison table |
| `lrc_case2_n11_family_set_summary_v3.md` | F1/F12/F1246689 family summaries (n=11) |
| `lrc_case2_classwise_deficit_summary_v2.md` | Classwise deficit framework |

---

## S.D  Verification Protocol

A reader wishing to independently verify the batch certificates should:

1. **Install:** Python 3.8+, no external libraries needed (all arithmetic is built-in).

2. **Run smoke tests:**
   ```
   python lrc_case2_d3_checkset_builder_v1.py   # generates checkset_smoke_v1.csv
   python lrc_case2_d3_certifier_v1.py           # generates certifier_smoke_v1.csv
   ```

3. **Reproduce n=7 full batch:**
   ```
   python lrc_case2_d3_batch_certify_v2.py --n 7
   ```
   Expected: 15 templates, 300 checks, 0 violations.

4. **Reproduce n=8,9,10 composite batch:**
   ```
   python lrc_case2_d3_batch_certify_composite_v1.py --n 8
   python lrc_case2_d3_batch_certify_composite_v1.py --n 9
   python lrc_case2_d3_batch_certify_composite_v1.py --n 10
   ```

5. **Reproduce n=11 full batch:**
   ```
   python lrc_case2_d3_batch_certify_v2.py --n 11
   ```
   Expected: 45 templates, 2115 checks, 0 violations.

6. **Cross-check:** Compare output CSV row counts and violation counts with the `.md` summary files.

---

## S.E  Notation Reference

| Symbol | Meaning |
|---|---|
| n | Number of runners |
| E | Speed tuple (e_1,...,e_{n-1}), gcd-1 |
| A_n | AP-core (1,...,n-1) |
| L | lcm(E) |
| N | nL (period) |
| φ(n) | Euler totient = #{j<n : gcd(j,n)=1} |
| x_0(E) | Safe-point count |
| B_div | Divisible-safe fiber set |
| A_b | Safe a-values at fiber b |
| B_safe | Fibers with non-empty A_b |
| C_bad | Bad fibers = B_div − B_safe |
| t_e(b) | Floor quotient ⌊e·b/L⌋ |
| U_fix(b) | Fixed runners' bad-a union |
| R_fix(b) | Z_n \ U_fix(b) (miss set) |
| U_M(b) | Free runner's bad-a pair |
| E_fixed | Fixed non-divisible speeds |
| E_div | Divisible speeds (n | e) |
| L_0 | lcm(E_fixed ∪ E_div) |
| α | M^{-1} mod n (free runner inverse) |
| e_max | max(E_fixed) |
| I_lo, I_hi | Canonical lower/upper frozen bands |
| a_F, b_F | Asymptotic bound coefficients |
| M_0(F) | TCP asymptotic threshold |
| T(F) | TCP finite check set |
| TM1/TM2/TM3 | Two-Miss Transition Mechanism lemmas |
| D.1', D.2' | Band-density and two-band lemmas |
| TCP | Template Certification Protocol |
| S1–S4 | Structural necessity chain |
