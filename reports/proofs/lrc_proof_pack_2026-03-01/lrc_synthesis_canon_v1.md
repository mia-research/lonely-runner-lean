# LRC n=all Synthesis Canon v1
Date: 2026-03-07
Purpose: Authoritative status map of all results in the n=all proof program.
Classification: T1 (gap-free proved), T2 (proved-under-hypothesis), T3 (certified empirical, 0 violations), T4 (heuristic/pattern, needs tightening).
Primary truth source: proof pack at reports/proofs/lrc_proof_pack_2026-03-01/

---

## T1 — Fully Proved, Gap-Free

### Structural / Setup
| Result | Statement | Source |
|--------|-----------|--------|
| Irrational branch | Weyl equidistribution covers full-rank + partial-rank irrational tuples | lrc_irrational_branch_sketch_v1.md |
| Case 1 (no e divisible by n) | x₀(E) ≥ φ(n) for all E with no e|n. Witnesses {jL: gcd(j,n)=1}. | theorem_seq_v11 §4 |
| Lemma P | x₀(A_n) = φ(n). Safe(A_n) = {jL: gcd(j,n)=1}. Tight minimum confirmed. | theorem_seq_v11 §3 |
| C2 decomposition identity | x₀ = Σ_b |A_b| exactly. No assumptions. | lrc_case2_partial_analytic_v1.md |
| Encoding Invariance (T1) | B_div, C_bad, B_safe are permutation-invariant in E. PL.1: t_M(b) = floor(b/L₀) M-independent. | lrc_case2_6theorem_framework_v1.md |

### Small-L Cases
| Result | Statement | Source |
|--------|-----------|--------|
| L=n canonical | B_safe = n−1 = φ(n). Tight minimum. | lrc_case2_partial_analytic_v1.md |
| L=2n second-smallest | B_safe = 2(n−2) ≥ φ(n) for all n ≥ 3. | lrc_case2_partial_analytic_v1.md |
| B_div gap structure | {n,...,2n−5} unreachable as B_div values. Second smallest B_div = 2(n−2). | lrc_case2_bdiv_gap_structure_v1.md |

### Prime n Structure
| Result | Statement | Source |
|--------|-----------|--------|
| T3 degree bound | Prime n, |E_non| ≤ ⌊(n−1)/2⌋ → C_bad = 0. | lrc_case2_6theorem_framework_v1.md |
| T3(b) lower band | t_e = 0 for all e at the lower band → union_bad ≤ n−1 < n → C_bad = 0. All n, all Case-2. | lrc_case2_6theorem_framework_v1.md |
| T3(c) top band | Top-band fibers safe by symmetric argument. All n, all Case-2. | lrc_case2_6theorem_framework_v1.md |
| F1246689 exact CRT | n=11, E(M)=(1,2,3,4,6,6,8,9,M,11), L=792M. 7 distinct fixed speeds → 8-element union_bad, missing={1,2,3}. Free runner M covers ≤2. B_safe ≥ 16M ≥ φ(11). | lrc_case2_6theorem_framework_v1.md §T4.F |

### Case-B Near-Complete Family (prime n, one-div, |E_fix|=n−3)
| Result | Statement | Source |
|--------|-----------|--------|
| Case i (1 ∉ E_fix) | n−1 ∉ U_fix(0) → Miss exists at τ=0. Claim A proved. | lrc_g4open_near_complete_lemma_v1.md |
| Case ii (n−1 ∉ E_fix) | 1 ∉ U_fix(0) → Miss exists at τ=0. Claim B proved. | lrc_g4open_near_complete_lemma_v1.md |
| Case iiia | Both 1,n−1 ∈ E_fix but |U_fix(0)| < n → Miss at τ=0. Direct τ=0 witness. | lrc_g4open_near_complete_lemma_v1.md |
| Case iiib (G4-LAMBDA-CASEB) | Both 1,n−1 ∈ E_fix, U_fix(0)=Z_n. SL-1 proved via Sole Cover Witness. | lrc_dropped_runner_witness_v1.md §11 |

**Case-iiib proof chain (all sub-lemmas proved):**
- Lemma A: r_enter(t*) = (e*)⁻¹·(−(t*+1)) mod n ∈ bad_set(e*,t*,n), newly entering at t*/e*.
- Lemma NR (Freeze): I*(e*,t*) = [t*/e*, t*/e* + 1/(e*·e_max)) — all other runners frozen (Farey adjacency). e* covers r_enter throughout.
- Full Coverage: C_{E_all}(α) = Z_n → any Miss witness must be in dropped support.
- Lemma B (Sole Cover Witness): On (1/n, 1/(n−1)), r_d = −d⁻¹ mod n is covered ONLY by runner d. Since d is dropped, Miss_{E_fix}(r_d) ⊇ (1/n,1/(n−1)), meas ≥ 1/(n(n−1)) > 0.
- Sole Coverage Theorem: Full AP {1,...,n−1}, t=0, interval (1/n,1/(n−1)): residue bijection e ↦ −e⁻¹ mod n is perfect. Dropping d exposes r_d.
- Source: lrc_ap_synchronization_witness_v1.md, lrc_dropped_runner_witness_v1.md

### GAP-2 Multi-Divisible (prime n, |E_div|≥2)
| Result | Statement | Source |
|--------|-----------|--------|
| E_div Transparency | For e_div = k·n, k∈{1,...,n−2}: bad_set(kn,k,n) = ∅ at initial window (1/n,1/(n−1)). gcd(kn,n)=n, Sol fails both requirements. | lrc_gap2_multidiv_analysis_v1.md |
| Unit Residue Isolation at t=0 | Non-unit runners (gcd(e,n)>1) cannot cover unit residues (gcd(r,n)=1) at t=0. | lrc_gap2_multidiv_analysis_v1.md |
| GAP-2 prime n regular k | |E_div|≥2, prime n, k_i∈{1,...,n−2}: E_div transparent → |E_non|=n−3 < φ(n) unit runners cover ≤n−3 unit residues (bijection) → ≥2 unit residues uncovered → Miss width ≥ 1/(n(n−1)) > 0. | lrc_gap2_multidiv_analysis_v1.md |

### G4B Composite n Sub-cases
| Result | Statement | Source |
|--------|-----------|--------|
| G4.A Lipschitz bound | |U_fix(b+1)| − |U_fix(b)|| ≤ 4Σg_e across fiber transition. Local variation controlled. | lrc_gap4_complementarity_theorem_track_v1.md |
| at_B_div_end sub-case | gcd(e_u,n)=1, n|L, e_u|L → lcm(n,e_u)=n·e_u | L → min_period=L/e_u ≥ n. Lower band ≥ n safe fibers → at_B_div_end run ≤ B_div−n. | lrc_ideation_test_noz0_v1.md |
| z0-from-unit-runner | Lemma S2: unit z=0 event → safe fiber at transition → run_len ≤ min_period−1. | lrc_gap4_complementarity_theorem_track_v1.md |
| Non-unit z=0 Case A | 44.4% of n=6 terminations. Unit runner crosses zero → Lemma S2. PROVED. | lrc_g4b_coset_essentiality_v1.md |
| Non-unit z=0 Case B | 11.1% of n=6 terminations. gcd≥3 runner, bad_set→∅ → sole-covered departing coset exposed. 100% sole_cover verified. PROVED. | lrc_g4b_coset_essentiality_v1.md |
| Non-unit z=0 Case D | 11.1% of n=6 terminations. Misattributed — 100% caused by co-occurring Case B/C runner. Resolved. | lrc_g4b_coset_essentiality_v1.md |

### Disproved / Dead Ends (record to avoid re-exploring)
| Route | Why it failed | Source |
|-------|---------------|--------|
| C2-main(C) | n=12 CE: lhs3=99062 > rhs=92280. x₀=9386 >> φ(12)=4. | theorem_seq_v11 |
| Period-121 model | 22/110 classes sub-linear (C_bad decreasing relative to M). | lrc_case2_n11_pl_validation_v1.md |
| gcd_struct_bound n·lcm(gcd(e,n)) | 15,720 violations for n=6. | lrc_ideation_test_g4b_n6_v1.md |
| Top-band distance bound | Only 118/1705 at_B_div_end runs satisfy run_len ≤ top_band_dist+1. | lrc_ideation_test_noz0_v1.md |
| LB_5 universality | Not universal across all S3 families. LB_7 recommended instead. | theorem_seq_v11 §13 |
| Bug: min|R_fix| discriminator | Was computing min|R_fix| (trivially < n), not min|U_fix|. Corrected version: all 380 templates pass. | lrc_g4open_near_complete_lemma_v1.md §0 |

---

## T2 — Proved Under Hypothesis

| Result | Statement | Load-bearing hypothesis |
|--------|-----------|------------------------|
| G4-LAMBDA-CASEA | Case-A closed for G_tot ≤ d + 2|E_nu|. | H1..H7 scope conditions |
| Case-A degree bound (composite n) | |E_non| ≤ ⌊(n−1)/2⌋ → C_bad=0, prime case extends to composite. | Separate invertibility check needed |
| Lemma M1 (global) | Transition algebra including coincident-boundary handling. | Non-coincident boundaries only proved; coincident boundaries isolated |
| Lemma M2 (general) | Miss-interval existence beyond Siiib-U sub-scope. | Restricted to unit-dropped Case-iiib scope |
| Bottom/top fiber safety, composite n | Always safe. | Prime n proved; composite n gcd(e,n)>1 case analysis pending |
| D.3 Finite Small-M Closure Protocol | Family-level certification theorem. | Each family needs M_0(F) computed |

---

## T3 — Certified Empirical (0 violations)

| Evidence set | n range | Tuple / config count | Notes |
|---|---|---|---|
| All-distinct Case-2, exhaustive | n=3..7 | 158,626 tuples | 0 violations, max_L=56 |
| All-distinct Case-2, random | n=8..12 | ~50k (random sample) | 0 violations |
| D3 series one-div all-distinct | n=7..19, 339 templates | 34k+ checks | 0 violations |
| Multi-divisible |E_div|=2 | n=6..15 | 445 configs | 0 failures, min Miss >> 1/(n(n-1)) |
| GAP-2 composite n B2 (delayed Miss) | n=6..15 | 445 configs | 0 failures |
| S3 complementarity | composite n, Case-2 | 87,818 tuples | 0 CB violations |
| G4B n=6 diagnostic | n=6 | 93,150 tuples, 56,160 runs | 0 CB violations; 93.6% z0 termination |
| G4B across composite n | n=4,5,6,7,8,9,10,12 | 1,705 at_B_div_end runs | 0 TYPE-B mechanism |
| Case-iiib discriminator | n=10..16, 380 templates | 380 certified | 0 FAIL, min b-interval ≥35 |
| Non-unit z=0 taxonomy (n=6) | n=6 | 3,000 events | 4 cases classified, 0 violations |
| n=6 exhaustive max_v=50 | n=6 | 2,061,046 tuples | 0 counterexamples |
| Multi-div n=13 | n=13, 3,300 templates | 70k+ checks | 0 violations |
| GAP-2 bad k analytic open | n=6..15 | 445 configs | Empirically certified; analytic open |
| GAP-2 composite B2 | n=6..15 | 445 configs | Empirically certified; analytic open |

---

## T4 — Heuristic / Pattern (Not Yet Theorem-Grade)

| Pattern | Empirical strength | What needs tightening |
|---------|-------------------|----------------------|
| z=0 termination dominance | 93.6% of obstruction runs in n=6 data | Need exact theorem: "z=0 event ⇒ ∃ safe fiber" for ALL cases (Case C open) |
| Miss-width ≥ 1/(n(n-1)) | All Case-iiib, n=7..19, min measure 7/36 | Proved for unit dropped d. For non-unit d, coset structure changes the formula |
| Outside-band safe mass spread | S_out >> 0 for all 92 Xi_tr rows | Need exact lower bound S_out ≥ (e_div/n − 1)/e_div or similar |
| Multi-div large-L stability (x₀ grows) | Test 5 data | Need M_0(F) explicit threshold (M3 provides the framework) |
| Non-unit Coset Essentiality (Case C) | 100% verified n=6, 3000 events | Needs Subgroup Opacity + Farey adjacency proof |
| Alternating sum positivity (all n, all E) | Zero violations in all certified scans | Proved for specific families; general proof = the target theorem |
| Feasible signature compression | n=7: 10 realized of 120 abstract (12× compression) | Could reduce case analysis but not a standalone theorem |

---

## Summary of True Remaining Gaps (load-bearing for n=all)

| Gap | Priority | Status | Blocking |
|-----|----------|--------|---------|
| OPEN-3: G4B-COMP-CAP non-unit z=0 Case C (Non-Unit Coset Essentiality) | 1 | T4 (pattern only) | S3-GENERAL for composite n |
| OPEN-2: GAP-2 bad k + composite B2 | 2 | T3 (certified) | Full GAP-2 closure; S3-GENERAL for multi-div |
| OPEN-1: S3-PRIME Route A (Xi_tr outside-band safe mass) | 3 | T3 partially, T4 mechanism | General prime n Case-2 closure; S3-PRIME |
| OPEN-4: S3-GENERAL universal theorem | 4 | Conditional on OPEN-1,2,3 | n=all final closure |

**What's NOT a gap:** Irrational branch, Case 1, all small-L cases, Case-B (Cases i/ii/iiia/iiib), GAP-2 prime n regular k, G4B boundary sub-cases, and all sub-lemmas in the Sole Cover chain are fully proved.
