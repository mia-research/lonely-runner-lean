# LRC Gap Status: n=all
**Date:** 2026-03-04 (updated session 8)
**Canonical tracker:** `lrc_claim_status_table_v1.csv`
**Purpose:** Holistic map of the current proof state vs. a complete n=all solution.

---

## Target Theorem

> For all n≥3 and gcd-1 integer tuples E of size n−1: x₀(E) ≥ φ(n).

Equivalently (via fiber split): B_safe ≥ n−1 for every valid (n, E, L, M).

---

## 1. What Is Proved — Unconditionally Analytic

| Component | Source | Notes |
|-----------|--------|-------|
| Irrational branch (Weyl equidistribution) | `lrc_irrational_branch_sketch_v1.md` | Full-rank + partial-rank covered |
| Case 1 (no e divisible by n): x₀(E)≥φ(n) | `theorem_seq_v2 §4` | Witness {jL:gcd(j,n)=1} |
| Lemma P: x₀(A_n)=φ(n), Safe(A_n) exact | `theorem_seq_v2 §3` | |
| TM1/TM2/TM3 (badness characterization) | `lrc_case2_6theorem_framework_v2.md` | |
| TCP protocol (finite-window methodology) | paper draft §5 | |
| T1 Encoding Invariance, PL.1 | `lrc_case2_6theorem_framework_v2.md` | M-independent floor |
| T3(a) degree bound, prime n | `lrc_case2_6theorem_framework_v2.md` | \|E_non\|≤⌊(n-1)/2⌋→C_bad=0 |
| T3(b,c) bottom/top bands safe | `lrc_case2_6theorem_framework_v2.md` | All n, all Case-2 |
| L=n canonical: B_safe=n−1 | `lrc_case2_partial_analytic_v1.md` | Tight minimum |
| L=2n second-smallest: B_safe=2(n−2)≥n−1 | `lrc_case2_partial_analytic_v1.md` | Prime + composite |
| B_div gap: {n,...,2n−5} unreachable | `lrc_case2_bdiv_gap_structure_v1.md` | 2nd smallest = 2(n−2) |
| F1246689 (n=11): B_safe(M)≥16M≥φ(n) | `lrc_case2_6theorem_framework_v2.md §T4.F` | T4→T1 via exact CRT |
| G4.A: transition Lipschitz bound | `lrc_gap4_complementarity_theorem_track_v1.md` | \|D(b+1)−D(b)\|≤4Σg_e |
| G4-LAMBDA-CASEA (Case-A, H1-H7) | `lrc_gap4_scope_lock_audit_v1.md` | G_tot≤d+2\|E_nu\|→proved |
| Case-B near-complete Cases i, ii, iiia | `lrc_g4open_near_complete_lemma_v1.md` | τ=0 witnesses, Claims A/B |
| n=4 complementarity bound | `lrc_gap4_s3_complementarity_proof_v1.md` | Exact case decomposition |

### Promoted Since Paper Draft v2
- **F1246689**: T4 (data-fit) → T1 (exact CRT, no fitted slopes)
- **Cases i/ii/iiia**: now proved (τ=0 direct witness)
- **Corrected discriminator**: S(F) = min|U_fix(τ)| bug fixed; 380 Case-B templates, 0 FAIL n=10..16

### Session 8 Promotions (2026-03-04)
- **G4-LAMBDA-CASEB CLOSED**: Lemma B (Sole Cover Witness) proves SL-1 for all Case-iiib templates.
  - E_div Transparency (PROVED): kn runner with k∈{1,...,n-2} contributes ∅ to coverage at initial window α∈(1/n, 1/(n-1)).
  - Unit Residue Isolation at t=0 (PROVED): non-unit runners cannot cover unit residues at t=0.
  - Sole Cover bijection + Lemma C chain → Miss_E(r_d) ⊇ (1/n, 1/(n-1)), meas ≥ 1/(n(n-1)) > 0.
  - Empirically certified for all 59 Case-iiib templates n=10..15, 0 failures, min measure 7/36.
- **GAP-2, prime n regular k (PROVED)**: |E_div|≥2, prime n, k_i∈{1,...,n-2} → Miss guaranteed.
  - Three-step: E_div Transparency + Pigeonhole (|E_non|=n-3 < φ(n)) + Unit Residue Isolation.
  - Empirically certified: 445 configs n=6..15, 0 failures, all Miss widths >> 1/(n(n-1)).
  - File: `lrc_gap2_multidiv_analysis_v1.md`
- **GAP-2, composite n (empirically closed)**: Delayed Miss via unit runner sole-cover transition.
  - Mechanism: at t=0 all residues covered; as α advances, unit runner leaves sole coverage → Miss.
  - Analytic proof still open for sub-case B2 (all units present + sufficient non-units).

---

## 2. What Is Certified But Not Yet Theorem-Grade

| Evidence set | Scope | Status |
|---|---|---|
| D3 series: n=7..19, 339 templates, 34k checks | One-divisible, all-distinct, prime n | CERTIFIED, 0 violations |
| Multi-divisible n=13: 3,300 templates, 70k+ checks | \|E_div\|≥2 | CERTIFIED, 0 violations |
| GAP-2 composite n B2 (delayed Miss) | All |E_div|≥2 composite n, n=6..15 | CERTIFIED, 445 configs, 0 failures |
| S3 complementarity: 87,818 tuples | All composite n, Case-2 | CERTIFIED, 0 CB violations |
| Case-iiib discriminator: n=10..16, 380 templates | Near-complete Case-B | CERTIFIED, 0 FAIL, b-interval ≥35 |

---

## 3. Remaining Open Gaps

### ~~Gap G4-LAMBDA-CASEB~~ — **CLOSED (Session 8)**

**Was:** Case-B ∃τ with U_fix(τ)≠Z_n (n≥10) — SL-1 analytic proof.
**Now CLOSED by:** Lemma B (Sole Cover Witness) + E_div Transparency + Unit Residue Isolation at t=0.
**Proof:** At α∈(1/n,1/(n-1)): divisible runners transparent (∅ coverage). Unit runners at t=0: bijection e↦−e⁻¹ mod n. Dropping d exposes r_d = −d⁻¹ mod n. Miss_E(r_d) ⊇ (1/n, 1/(n-1)), meas 1/(n(n-1)) > 0. ✓
**Source:** `lrc_gap2_multidiv_analysis_v1.md`, `lrc_dropped_runner_witness_v1.md §11`

---

### Gap G4B-COMP-CAP: Complementarity run cap for composite n≥6

**What it blocks:** S3 structural theorem for all composite n≥6, L>2n.
**Statement:** |O∩C| ≤ |C|−n per B_div component C (O = obstruction set).
**Evidence:** 87,818 tuples, 0 CB violations; 95.2% of obstruction runs terminate at z=0.
**Proof obligations (from `lrc_gap4_complementarity_theorem_track_v1.md`):**
- B.Obs-1: contiguity (O forms ≤1 block per component)
- B.Obs-2: length cap (≥n non-obstructed fibers via G4.A + endpoint constraints)
- B.Obs-3: component summation

**Key signal:** n=4 complementarity proved completely. n≥6 blocked by adjacent-pair rotation mechanism. Only n=4 is tight (6 exact-saturation tuples).
**Session 8 anatomy (Test 2, n=6, 93,150 tuples):**
- CB violations: **0**. z0_event: 93.6%, at_B_div_end: 6.4%.
- **Prime n: zero at_B_div_end runs** (all unit z=0 events → Lemma S2 guarantees safety).
- **Composite n: at_B_div_end = boundary truncation** (100% have next_z0 within min_period of b_hi).
- gcd pattern: 79.2% of z0-terminating events come from non-unit runners (gcd=2 or 3 for n=6).
- Longest runs (≤89) all terminate at z0_event.
**Emerging proof route (confirmed by session 8 data):**
1. z=0 runs: run_len ≤ min_period − 1 [Lemma S2 for unit runners; non-unit z=0 creates safe fiber via combined bad-set].
2. at_B_div_end runs: run_len ≤ dist(run_start, top_band_safe_fiber) ≤ min_period.
3. Combined: max_obstr_run ≤ min_period ≤ B_div/e_min < B_div − n [needs B_div/e_min + n ≤ B_div].
**Session 8 analytic advancement (Test 3):**
- at_B_div_end sub-case PROVED: gcd(e_u,n)=1 + n|L + e_u|L → n·e_u|L → min_period≥n → lower band has ≥n safe fibers → at_B_div_end run ≤ B_div−n. (Tight: n=4, E=(1,3,4), run=3=B_div−n. ✓)
- z0-from-unit-runner sub-case PROVED: Lemma S2 → safe fiber at every unit z=0 event, run_len ≤ min_period−1.
- **Non-unit taxonomy (session 9 extended analysis):** 4 cases identified and resolved:
  - A (44.4%): unit z=0 → Lemma S2. PROVED.
  - B (11.1%): gcd≥3, bad_set→∅ at z=0 → sole-covered departing coset exposed. PROVED (100% sole_cover).
  - C (44.4%): gcd≥2 coset change → Non-Unit Coset Essentiality needed. Route identified.
  - D (11.1%): misattributed; all 100% caused by co-occurring Case B/C runner. Resolved.
- **Non-Unit Coset Essentiality Lemma (open, route identified):** "Subgroup Opacity" — non-unit runners cover a coset of n/g residues; at z=0 coset transition, vacated coset was solely covered by e → exposed. Farey adjacency prevents other runners from simultaneously covering it. Empirically: 100% verified (n=6, 3000 termination events, 0 exceptions).
**File:** `lrc_gap4_complementarity_theorem_track_v1.md`, `lrc_ideation_test_g4b_n6_v1.md`, `lrc_ideation_test_noz0_v1.md`, `lrc_g4b_coset_essentiality_v1.md`

---

### ~~Gap GAP-2, prime n regular k~~ — **PROVED (Session 8)**

**Was:** Multi-divisible |E_div|≥2 closure; Lemma R: B_safe ≥ n for L>n.
**Now PROVED (prime n, regular k):** E_div Transparency + Pigeonhole on unit residues.
**Analytic remaining:** (1) prime n, bad k (k mod n ∈ {0,n-1}) — empirically certified; (2) composite n B2 — empirically certified.
**File:** `lrc_gap2_multidiv_analysis_v1.md`

---

### Gap S3-PRIME-CAND: Outside-band safe mass for Xi_tr residuals

**What it blocks:** General prime-n Case-2 closure (Route A from gap1_open).
**Issue:** 92 residual rows (n=7,11,13,17,19) have B_safe(I_tot)=0 on canonical bands but x₀>>φ(n). Safe mass is outside I_tot. Uniform Xi_tr=0 on current I_tot is NOT achievable.
**Route A** (recommended): Prove S_out(F,M) ≥ Xi_tr(F,M) where S_out = safe fibers outside canonical I_tot. Define analytically tractable I_mid.
**File:** `lrc_gap1_open_exact_brief_v1.md`

---

## 4. Blocking Dependency Graph

```
n=all LRC proof
├── Irrational branch ──────────────────────────────── PROVED
├── Case 1 (no e|n) ───────────────────────────────── PROVED
└── Case 2 (∃e|n):
    ├── L=n, L=2n ─────────────────────────────────── PROVED
    └── Large L (L>2n):
        ├── Prime n, |E_div|=1:
        │   ├── Case-A (H1-H7 scope) ──────────────── PROVED-UNDER-H
        │   ├── Case-B near-complete Cases i/ii/iiia ─ PROVED
        │   ├── Case-B Case-iiib [SL-1=G4-LAMBDA] ─── CLOSED (session 8) ✓
        │   └── Xi_tr residuals [S3-PRIME Route A] ──  ← OPEN (hardest)
        ├── Prime n, |E_div|≥2 [GAP-2]:
        │   ├── regular k ────────────────────────────  PROVED (session 8) ✓
        │   └── bad k + composite n B2 ───────────────  empirically certified; analytic open
        └── Composite n [G4B]:
            ├── G4.A ───────────────────────────────── PROVED
            ├── G4B-COMP-CAP:
            │   ├── prime n sub-case ─────────────────  PROVED (Lemma S2 alone)
            │   └── composite n sub-case ─────────────  ← OPEN-TARGET (sub-lemma: non-unit z=0)
            └── G4C (from G4B) ──────────────────────  conditional
```

---

## 5. Priority Queue for Analytic Closure

| Priority | Gap | Status | Next Route |
|---|---|---|---|
| ~~1~~ | ~~SL-1 (Case-iiib / G4-LAMBDA-CASEB)~~ | **CLOSED session 8** | — |
| 1 | **G4B-COMP-CAP (composite n sub-case)** | Open | Non-unit z=0 creates safe fiber: why? (79.2% of terminations) |
| 2 | **GAP-2 bad k + composite B2** | Empirically certified | Farey density for bad k; "delayed Miss" analytic for B2 |
| 3 | **S3-PRIME Route A** | Open (hardest) | Outside-band anatomy (Test 4, 92 Xi_tr rows) |

G4B-COMP-CAP split by session 8: prime n sub-case PROVED; composite n needs non-unit z=0 lemma.
GAP-2 partial proof promotes from pure empirical to partially analytic.
S3-PRIME remains the deepest blocker (Xi_tr residual outside-band safe mass).

---

## 6. What the Paper Draft v2 Needs Updated

The draft's Case-2 section presents TCP certification as the main evidence.
Additions needed for a complete paper:
1. F1246689 T1 promotion (§: Hard case proof — replace T4 fit with exact CRT block)
2. Cases i/ii/iiia proved (new §: Near-complete family analytic closure)
3. Corrected discriminator result (replace vacuous S(F) claim with correct certificate table)
4. Gap map (new §: Remaining open claims with explicit routes)

**Files:** `lrc_case2_6theorem_framework_v2.md`, `lrc_g4open_near_complete_lemma_v1.md`
