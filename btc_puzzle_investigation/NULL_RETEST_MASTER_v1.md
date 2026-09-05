# NULL RETEST MASTER — double-blind re-check of every null in this folder

**Opened:** 2026-09-05 · **Population:** 242 null-bearing documents (auto-enumerated, `scratchpad/build_master.py`; criterion = a null/refutation/closure word in the first 6 lines). 165 name a script that is present on disk.

## Why this exists

`MEMORY.md` records a **one-way suppression bias**: positives are converted to nulls *before* being
tested, and same-model gates do not catch it. `CLAIMS.md` "Standing flags" names M25 and N15 — the two
highest-stakes objects — as both converted toward null in the documented bias direction, and owes an
external review on both. Two nulls in this corpus are already known to have been **forced rather than
measured**: `ρ_p` (forced by `e₄=p²` composed with `canon()`'s lex sort) and the `F_{p³}` divisibility
"corroboration" (forced by `s₁=s₂=0` via `e₃=S₃/3`). This campaign re-checks all of them.

## Protocol — three arms, blinded

| arm | who | sees | must not see |
|---|---|---|---|
| **A — recompute** | `general-purpose` subagent | the setup (definitions, object, what to compute) | the claimed result, the grade, arm B |
| **B — recompute** | NotebookLM (`Mapping the Curve`) | the sources | arm A's output |
| **C — shortcut test** | `shortcut-tester` subagent | the claim + its script | arms A and B |

Arms A and B are asked for a **value**, never for agreement. They are compared only after both return.
Arm C answers a different question: *could this null have come out any other way.*

**Disagreement between A and B is the signal.** Agreement is not confirmation — both are the same
model family and share the failure mode. A null is `RECHECKED` only when A and B agree on the value
**and** C returns UNFORCED.

## Status vocabulary

`PENDING` · `RECHECKED` (A=B, C=UNFORCED) · `FORCED` (C: the statistic could not have come out
otherwise) · `SPLIT` (A≠B — adjudicate by hand) · `NO-REPRO` (no script, needs re-derivation)

---

## Batch index

| batch | rows | reproducible | status |
|---|---|---|---|
| 1 | 14 | 14 | IN FLIGHT |
| 2 | 14 | 14 | PENDING |
| 3 | 14 | 14 | PENDING |
| 4 | 14 | 14 | PENDING |
| 5 | 14 | 14 | PENDING |
| 6 | 14 | 14 | PENDING |
| 7 | 14 | 14 | PENDING |
| 8 | 14 | 14 | PENDING |
| 9 | 14 | 14 | PENDING |
| 10 | 14 | 14 | PENDING |
| 11 | 14 | 14 | PENDING |
| 12 | 14 | 11 | PENDING |
| 13 | 14 | 0 | PENDING |
| 14 | 14 | 0 | PENDING |
| 15 | 14 | 0 | PENDING |
| 16 | 14 | 0 | PENDING |
| 17 | 14 | 0 | PENDING |
| 18 | 4 | 0 | PENDING |


---

## Batch 1

| # | document | object / null claim | script | repro | A | B | C | status |
|---|---|---|---|---|---|---|---|---|
| 1.1 | `AUDIT_ks_backstop_and_joint_readout_v1.md` | - Claimed: `[VERIFIED-scope NULL]`, bounded by Cor B1 `[PROVED given KS]`, coupling ≤ 2⁻¹²⁸. | `AUDIT_secp_singlefeature_null_v1.py` | Y | · | · | · | PENDING |
| 1.2 | `EXTERNAL_REVIEW_PROMPT_M25_N15_v1.md` | **Current status (under review):** `[null — cofactor / sampling artifact, mechanism identified, model scale]`. | `h5_followup_run_v1.py` | Y | · | · | · | PENDING |
| 1.3 | `PREREG_n15_joint_readout_confinement_v1_DEVIATIONS.md` | grade cap (EMPIRICAL), datasets, exact-arithmetic rule, matched-null philosophy | `n15_readout_confinement_runner_v1.py` | Y | · | · | · | PENDING |
| 1.4 | `RESULT_n15_joint_readout_confinement_v1.md` | # RESULT — N15 joint multi-readout confinement: scoped null on constructed secp keys | `n15_readout_confinement_runner_v1.py` | Y | · | · | · | PENDING |
| 1.5 | `AUDIT_negative_bias_session2to4_v1.md` | sector and it came back generic … isolated to one decidable lattice-counting statement"* as a revert | `_audit_Sy_structure_v1.py` | Y | · | · | · | PENDING |
| 1.6 | `CORRECTION_cside_v1_null_underdispersion_v1.md` | # CORRECTION — `RESULT_cside_nonalgebraic_correlation_v1.md`: the null was under-dispersed by √2 | `cside_orbitlevel_v1.py` | Y | · | · | · | PENDING |
| 1.7 | `PREREG_cm_jointset_excess_v1_DEVIATIONS.md` | is dated, states the change, the reason, and the impact on statistic/null/power/scope. | `model_curve_infra_v1.py` | Y | · | · | · | PENDING |
| 1.8 | `PREREG_cm_jointset_excess_v3.md` | disjointness ruling, primary statistic `Î_prim`, matched null, PC-SEM/PC-GRADE, power, exactness, and | `cm_jointset_excess_v3.py` | Y | · | · | · | PENDING |
| 1.9 | `PREREG_cm_jointset_higherorder_v1.md` | null]`, `RESULT_cm_jointset_excess_v3.md`). This document pre-registers the SIX channels the v3 RESULT | `cm_jointset_ho_v1.py` | Y | · | · | · | PENDING |
| 1.10 | `PREREG_cm_jointset_semaev_r5_v1_DEVIATIONS.md` | null, plants, exactness rule, and falsification table are UNCHANGED. One RATIONALE correction (D1), | `cm_jointset_semaev_r5_v1.py` | Y | · | · | · | PENDING |
| 1.11 | `PREREG_e3_owed_measurement_v1.md` | # PREREG — E3 (A-1d) owed measurement: structural-null reframe + FWER + OOS + curve-class discriminator | `c2_grouplaw_diffset_curve_v1.py` | Y | · | · | · | PENDING |
| 1.12 | `PREREG_e3_owed_measurement_v2.md` | # PREREG v2 (FROZEN) — E3 (A-1d) owed measurement: structural-null reframe + FWER + OOS + curve-class | `c2_grouplaw_diffset_curve_v1.py` | Y | · | · | · | PENDING |
| 1.13 | `PREREG_e3_twist_and_cm_controls_v1.md` | # ⊘ WITHDRAWN — PREREG — E3 controls (twist / CM) | `check_no_float.py` | Y | · | · | · | PENDING |
| 1.14 | `PREREG_islands_curveimage_jointset_v1.md` | **Status: SPEC ONLY. Written and FROZEN before any island / curve data is seen. Decidable artifact.** | `islands_curveimage_jointset_v1.py` | Y | · | · | · | PENDING |

---

## Batch 2

| # | document | object / null claim | script | repro | A | B | C | status |
|---|---|---|---|---|---|---|---|---|
| 2.1 | `PREREG_mu3_diffset_control_repair_v1.md` | the μ₃ channel of `difference_set_xy_geometry_v1.py` and fixes the statistic, null, power, decision | `difference_set_xy_geometry_v1.py` | Y | · | · | · | PENDING |
| 2.2 | `PREREG_spectral_decomp_v1.md` | on the non-CM curve $E'$ is null ($E_3'=3711$, $p\approx 0.66$). But E3 is a *single-number | `spectral_decomp_apply.py` | Y | · | · | · | PENDING |
| 2.3 | `PROTOCOL_blinded_joint_readout_v1.md` | report a flat table. **No target is privileged.** You are not told which (if any) target is a | `ecc_secp256k1.py` | Y | · | · | · | PENDING |
| 2.4 | `RESULT_cm_jointset_excess_v3.md` | **Grade:** `[VERIFIED-scope — scoped null; discovery + OOS confirmation + scale ladder to 2¹⁶, R=10⁴, all firi | `cm_jointset_excess_v3.py` | Y | · | · | · | PENDING |
| 2.5 | `RESULT_cm_jointset_higherorder_v1.md` | # RESULT — A-joint-HO (higher-order / GLV / finer-label joint-set synergy): discovery-tier scoped null | `cm_jointset_ho_v1.py` | Y | · | · | · | PENDING |
| 2.6 | `RESULT_cm_jointset_semaev_r5_v1.md` | degenerate builds (D1). `[VERIFIED — KAT + artifact]`. | `cm_jointset_semaev_r5_v1.py` | Y | · | · | · | PENDING |
| 2.7 | `RESULT_cside_nonalgebraic_correlation_v1.md` | **Grade: `[EMPIRICAL — SCOPED, family-wise NULL]`** for the per-prime CDH/inversion structure; **`[FLAGGED LEA | `cside_nonalgebraic_correlation_v1.py` | Y | · | · | · | PENDING |
| 2.8 | `RESULT_cside_pooled_tilt_settlement_v1.md` | **Grade: `[EMPIRICAL — SCOPED]`** for the per-prime `inv` family-wise null (retained from v1); **`[FLAGGED LEA | `cside_pooled_tilt_settlement_v1.py` | Y | · | · | · | PENDING |
| 2.9 | `RESULT_e3_owed_measurement_v1.md` | # RESULT — E3 (A-1d) owed measurement DISCHARGED: set-specific reject survives the generator-free null, bounde | `e3_owed_measurement_v1.py` | Y | · | · | · | PENDING |
| 2.10 | `RESULT_grouplaw_e3_real82_v1.md` | # RESULT — group-law E3 on the real 82: a powered null; the "fires-harder" prediction is FALSIFIED, localizing | `grouplaw_e3_real82_v1.py` | Y | · | · | · | PENDING |
| 2.11 | `RESULT_islands_curveimage_jointset_v1.md` | **Grade: `[EMPIRICAL — scoped null, pre-registered, all controls live]`.** Executes | `islands_curveimage_jointset_v1.py` | Y | · | · | · | PENDING |
| 2.12 | `RESULT_islands_curveimage_jointset_v2.md` | **Grade: `[EMPIRICAL — scoped null on S1/S2/S3 only, pre-registered, controls live]`.** | `islands_curveimage_jointset_v1.py` | Y | · | · | · | PENDING |
| 2.13 | `RESULT_joint_shadow_decompose_v2.md` | unverified mechanism ("joint rho2≈1 because \|U\| is flat") and used dismissal language | `joint_shadow_decompose_v1.py` | Y | · | · | · | PENDING |
| 2.14 | `RESULT_joint_shadow_mu3_v1.md` | Follows `RESULT_joint_shadow_decompose_v2` (the joint-shadow magnitudes are generic; the | `joint_shadow_mu3_v1.py` | Y | · | · | · | PENDING |

---

## Batch 3

| # | document | object / null claim | script | repro | A | B | C | status |
|---|---|---|---|---|---|---|---|---|
| 3.1 | `RESULT_n15_twopoint_tuple_filter_v1.md` | **Date 2026-08-22. Grade: `[VERIFIED — exact, total enumeration; matched null]`** Scripts: | `n15_twopoint_tuple_filter_v1.py` | Y | · | · | · | PENDING |
| 3.2 | `ANALYSIS_destructive_interference_frame_v1.md` | Origin: user's recurring intuition — *"all these null / within-noise results. I keep thinking of | `spectral_matched_filter_v1.py` | Y | · | · | · | PENDING |
| 3.3 | `ANALYSIS_p0prime_excess_structure_v1.md` | `[RETRACTED]` claim failed its firing control; `[OPEN]` live thread. | `p0prime_s5_localization_v1.py` | Y | · | · | · | PENDING |
| 3.4 | `ANOMALY_DRILL_01_CT_SPLIT_v1.md` | reports magnitudes; it may **not** convert a magnitude into a verdict ("safe / generic / bounded / | `_anomaly_drill_ct_split_v1.py` | Y | · | · | · | PENDING |
| 3.5 | `AUDIT_d2_bridge_mod6_reduction_v1.md` | **Grade:** `[PROOF + EMPIRICAL — NULL, source ERRATA]` | `audit_d2_bridge_reduction_v1.py` | Y | · | · | · | PENDING |
| 3.6 | `AUDIT_mu3_subspace_residual_v1.md` | **Posture:** self-audit, adversarial. The counter-prior binds symmetrically — a null is audited | `mu3_subspace_residual_v1.py` | Y | · | · | · | PENDING |
| 3.7 | `AUDIT_mu_m_vanishing_law_run_v1.md` | `RESULT_..._v1.md` is **superseded**; its headline is withdrawn pending the rerun under | `mu_m_vanishing_law_v1.sage` | Y | · | · | · | PENDING |
| 3.8 | `AUDIT_semaev_v4_method_result_conclusion_v1.md` | relation-yield lever was an artifact; H1 null; H2 x-closure fires"). Audited in **both** directions — | `semaev_cm_relation_yield_v4.py` | Y | · | · | · | PENDING |
| 3.9 | `AUDIT_shortscalar_glv_interval_harness_v1.md` | # AUDIT — the proposed `shortscalar_glv_interval_harness_v1.py`: the test is null by construction | `AUDIT_shortscalar_glv_interval_harness_v1.py` | Y | · | · | · | PENDING |
| 3.10 | `CONSEQUENCES_mu3_subspace_null_v1.md` | # CONSEQUENCES — intersections of the μ₃-subspace null with the broader programme | `pointwise_inversion_2p128_item5_v1.py` | Y | · | · | · | PENDING |
| 3.11 | `CORRECTION_26_branch_locus_8point_v1.md` | **Superseded by:** `RESULT_26_PROVED_weil_restriction_v1.md`. **Grade of the correction:** `[PROVED]`. | `tors2_fp3_symmetry_v2.py` | Y | · | · | · | PENDING |
| 3.12 | `EXACT_RERUN_FINDINGS_v1.md` | finding holds, changes, or was a float artifact. Integer / Fraction / exact cyclotomic only. This | `coord_interference_v1.py` | Y | · | · | · | PENDING |
| 3.13 | `NOTE_brick_e_lead_rung_and_instruments_v1.md` | # NOTE — Brick E opened: instruments located, I1 covariance verified exactly, p=43 LEAD rung reads GENERIC (D= | `brick_e_degree_fitter_v1.py` | Y | · | · | · | PENDING |
| 3.14 | `NOTE_n8_branch_confinement_v1.md` | \| identity FAILS at `m = −2` (§3) \| **`[VERIFIED — exact, 4 primes, group-indexed]`** \| | `n8_branch_confinement_v1.py` | Y | · | · | · | PENDING |

---

## Batch 4

| # | document | object / null claim | script | repro | A | B | C | status |
|---|---|---|---|---|---|---|---|---|
| 4.1 | `NOTE_n8_mu3_structure_v1.md` | > # ⚠ WITHDRAWN 2026-09-04 — DUPLICATIVE, AND ITS CENTRAL EXPLANATION IS WRONG | `check_ledger.py` | Y | · | · | · | PENDING |
| 4.2 | `NOTE_n8_pointwise_convolution_v1.md` | > # ⚠ STATUS 2026-09-04 — this note is **M38** in `CLAIMS.md` `[VERIFIED — exact]`. It is NOT withdrawn. | `n8_pointwise_convolution_v1.py` | Y | · | · | · | PENDING |
| 4.3 | `NOTE_n8_twist_reduction_v1.md` | > # ⚠ WITHDRAWN 2026-09-04 — DUPLICATIVE, AND ITS CENTRAL EXPLANATION IS WRONG | `check_ledger.py` | Y | · | · | · | PENDING |
| 4.4 | `OPEN_d2_congruence_law_v1.md` | **Status: CLOSED — NULL (structural finding, public evaluation channel absent).** Source: `~/Downloads/d2-lang | `d2_carry_shadow_probe_v1.sage` | Y | · | · | · | PENDING |
| 4.5 | `POSITIVE_FINDINGS_MASTER_v17.md` | 1. **N15 (open since v11) — TESTED, scoped null.** `[VERIFIED-scope — scoped null]` No cheap predictor | `n15_readout_confinement_runner_v1.py` | Y | · | · | · | PENDING |
| 4.6 | `PREREG_anew_supersingularity_reaudit_v3.md` | v2's run is void: control **C4 fired** (7/18 primes). Session rule 2 forbids rescuing it and marks | `supersingular_mu4_mechanism_v1.py` | Y | · | · | · | PENDING |
| 4.7 | `PREREG_brick_e_cd_degree_v1_GATE_REVIEW_R2.md` | adjudicated on the merits (not pre-decided):** is the μ₃-null MATCHED on the QR-half, i.e. was R1's | `brick_e_anew_Lpoly_v1.sage` | Y | · | · | · | PENDING |
| 4.8 | `PREREG_brick_e_cd_degree_v2.md` | it**: the QR-half scalar arm with a μ₃-matched null resolves both R1 frame defects (F1 null-mismatch, F2 | `brick_e_anew_Lpoly_v1.sage` | Y | · | · | · | PENDING |
| 4.9 | `PREREG_brick_e_cd_degree_v2_GATE_REVIEW.md` | adjudicated on the merits (not pre-decided):** is the μ₃-null MATCHED on the QR-half, i.e. was R1's | `brick_e_anew_Lpoly_v1.sage` | Y | · | · | · | PENDING |
| 4.10 | `PREREG_c2_grouplaw_diffset_v1.md` | difference `x(Pᵢ−Pⱼ)` … never read because the run mis-tagged them [parity-void]."* Unblocked by the | `shortscalar_cneg_recalibration_v1.py` | Y | · | · | · | PENDING |
| 4.11 | `PREREG_flap_grouplaw_transition_v1.md` | **Status: SPEC ONLY. FROZEN before any transition/chain data is seen. Decidable artifact.** | `flap_grouplaw_transition_v1.py` | Y | · | · | · | PENDING |
| 4.12 | `PREREG_h2_order3_structure_control_v1.md` | `[VERIFIED — matched control]` "CM-specific vs generic split order-3, scope {these primes, k, m}." | `semaev_elimination_v1.py` | Y | · | · | · | PENDING |
| 4.13 | `PREREG_islands_glv_beta_crossset_v1.md` | **Status: SPEC ONLY. FROZEN before any island/curve GLV data is seen. Decidable artifact.** | `islands_glv_beta_crossset_v1.py` | Y | · | · | · | PENDING |
| 4.14 | `PREREG_kden_ramanujan_comb_v1.md` | computed for any configuration in the confirmatory set. Decidable artifact.** | `kden_ramanujan_comb_v1.py` | Y | · | · | · | PENDING |

---

## Batch 5

| # | document | object / null claim | script | repro | A | B | C | status |
|---|---|---|---|---|---|---|---|---|
| 5.1 | `PREREG_mu3_phase_within_triple_v1.md` | Companion magnitude probe (already done, scoped null): `RESULT_mu3_glv_frequency_support_v1.md`. | `xy_interference_U_v1.py` | Y | · | · | · | PENDING |
| 5.2 | `PREREG_mu3_subspace_residual_v2.md` | **Purpose:** tighten the v1 scoped null by extending the powered range from $\|Q_6\| \leq 426$ to | `mu3_subspace_residual_v2.py` | Y | · | · | · | PENDING |
| 5.3 | `PREREG_n1_phase_cap_v2.md` | **F6 — the exact variance of the matched null `[PROVED, and MC-verified to machine precision]`.** | `n1_phase_cap_sweep_v1.py` | Y | · | · | · | PENDING |
| 5.4 | `PREREG_n7_finite_rank_carrier_v1.md` | # PREREG — N7's carrier is FINITE RANK: the character's `U` is a sum of `r ≤ 4` Weil numbers, the null is a su | `subrayleigh_deficit_scaling_v1.py` | Y | · | · | · | PENDING |
| 5.5 | `PREREG_row_budget_lowtail_v2.md` | ### F10 — the `b=0` stratum has a DIFFERENT forced low-tail law, `8.0×` the generic rate `[PROVED]` | `row_budget_core_v1.py` | Y | · | · | · | PENDING |
| 5.6 | `PREREG_semaev_cm_solving_degree_v1.md` | CM-agnostic neutral system, so it cannot peek at the hypothesis) and (ii) the firing/VOID controls of | `semaev_elimination_v1.py` | Y | · | · | · | PENDING |
| 5.7 | `PREREG_semaev_structure_firstfall_vs_m_v2.md` | # PREREG v2 — Route A crux: the first-fall-degree NULL LADDER (semi-regular → S_m-symmetric → Semaev) vs m | `semaev_elimination_v1.py` | Y | · | · | · | PENDING |
| 5.8 | `PREREG_semaev_structure_solvingdegree_vs_m_v1.md` | # PREREG — Route A crux: does Semaev summation STRUCTURE lower the solving degree vs a degree/support-matched  | `semaev_elimination_v1.py` | Y | · | · | · | PENDING |
| 5.9 | `PREREG_semaev_symmetric_reduction_lastfall_v1.md` | # PREREG — Route A live lead: does the S_3-symmetric (elementary-symmetric-variable) reduction COLLAPSE the la | `semaev_elimination_v1.py` | Y | · | · | · | PENDING |
| 5.10 | `PREREG_semaev_symmetric_reduction_lastfall_v2.md` | first-fall provably is — Δ_coeff≡0 with no power to see a lever = the "null with no power" failure mode). | `semaev_symmetric_reduction_lastfall_v1.py` | Y | · | · | · | PENDING |
| 5.11 | `PREREG_shortscalar_sum_object_v4_amendment.md` | # PRE-REGISTRATION v4 — amendment to v3 (R-CONTIG null correction) | `shortscalar_sum_stageA_v2.py` | Y | · | · | · | PENDING |
| 5.12 | `PREREG_structured_pair_bilinear_v1.md` | **Status: SPEC ONLY. Written before any structured-pair data is seen. Decidable artifact.** | `difference_set_closure_verify_v1.py` | Y | · | · | · | PENDING |
| 5.13 | `PREREG_twist_orbit_magnitude_v1.md` | SIGNED channel, null) — shares its validated machinery; only the NEW object is spelled out. No | `twist_orbit_magnitude_run_v1.py` | Y | · | · | · | PENDING |
| 5.14 | `RESULT_L3_signature_leakage_v1.md` | Grade: **VERIFIED-scope** (empirical, controlled, scaling sweep). Conditional null: | `btc_puzzle_investigation/leak_test.sage` | Y | · | · | · | PENDING |

---

## Batch 6

| # | document | object / null claim | script | repro | A | B | C | status |
|---|---|---|---|---|---|---|---|---|
| 6.1 | `RESULT_N1_reframed_2sqrtp_cap_v1.md` | > **§2 and §3 of this document are WITHDRAWN as N1 findings.** See | `n1_exact_saturation_v1.py` | Y | · | · | · | PENDING |
| 6.2 | `RESULT_Sy_sign_skew_v1.md` | # RESULT — Sy sign-skew: CONFIRMED real, but curve-generic (not secp-special, not a leak) | `_sy_skew_test_v1.py` | Y | · | · | · | PENDING |
| 6.3 | `RESULT_amicable_log_bridge_v1.md` | # RESULT — amicable log-bridge: the decidable sub-question is NULL (scoped magnitude bound) (v1, 2026-07-24) | `amicable_log_bridge_v1.py` | Y | · | · | · | PENDING |
| 6.4 | `RESULT_anew_m_support_v2.md` | reporting**. Artifact: `audit_phase1_filters_v1.sage` / `.log`. No new sweep was run.* | `audit_phase1_filters_v1.sage` | Y | · | · | · | PENDING |
| 6.5 | `RESULT_anew_twisted_eigenvalues_nonabelian_v1.md` | # RESULT — FORK (1): the `a≠0` twisted eigenvalues are NON-ABELIAN → not Jacobi sums → L-Stick premise fails;  | `anew_eigenvalue_identify_v1.sage` | Y | · | · | · | PENDING |
| 6.6 | `RESULT_aperture_probes_v1.md` | **Seeds:** discovery `20260815`, OOS `20260816`–`20260818`. $R = 1000$ permutation-null draws per cell. | `aperture_probes_v1.py` | Y | · | · | · | PENDING |
| 6.7 | `RESULT_boundary_D_short_interval_CM_invariant_v1.md` | deviations in `..._DEVIATIONS.md`. **Grade:** `[EMPIRICAL — SCOPED NULL / collapse, both firing controls fired | `i1_shortinterval_localizer_check.py` | Y | · | · | · | PENDING |
| 6.8 | `RESULT_brick_e_cd_degree_v1.md` | # RESULT — Brick E, p=43: `c⁺(d)` is generic-degree (scoped NULL, lowest-power rung) | `brick_e_degree_fitter_v1.py` | Y | · | · | · | PENDING |
| 6.9 | `RESULT_brick_e_cd_degree_v2.md` | # RESULT v2 — Brick E, powered ladder: the cover-scramble degree `c⁺(d)` is at the GENERIC CEILING across all  | `brick_e_analysis_v2.py` | Y | · | · | · | PENDING |
| 6.10 | `RESULT_c2_chi2_leak_lead_REPRODUCED_v1.md` | > **⛔ WITHDRAWN — FALSE POSITIVE (2026-08-02, same day).** This "reproduction" was **invalid**: the | `c2_grouplaw_diffset_stageA_v1.py` | Y | · | · | · | PENDING |
| 6.11 | `RESULT_c2_grouplaw_diffset_stageA_v1.md` | **Grade:** `[EMPIRICAL — bounded; gate-cleared; fresh-vs-pool-verified null; per-channel plants; 5-seed OOS]`. | `c2_grouplaw_diffset_stageA_v1.py` | Y | · | · | · | PENDING |
| 6.12 | `RESULT_chi2_diffset_FALSE_POSITIVE_v1.md` | Supersedes `RESULT_c2_chi2_leak_lead_REPRODUCED_v1.md` (WITHDRAWN). **Scripts:** | `c2_grouplaw_diffset_curve_v1.py` | Y | · | · | · | PENDING |
| 6.13 | `RESULT_chik_dmodk_leakage_v1.md` | # RESULT — χ_k(x([d]G)) vs d mod k: NULL, gated, both key-sets `[EMPIRICAL — SCOPED]` | `chik_dmodk_leakage_v1.py` | Y | · | · | · | PENDING |
| 6.14 | `RESULT_chirp_hologram_plane_v1.md` | # The quadratic-phase ("chirp") plane: a new object, its one dark fringe, and a scoped null | `chirp_hologram_scan_v1.py` | Y | · | · | · | PENDING |

---

## Batch 7

| # | document | object / null claim | script | repro | A | B | C | status |
|---|---|---|---|---|---|---|---|---|
| 7.1 | `RESULT_cm_lattice_unfolding_v1.md` | \| ARM P: `I(Φ; (a,b) mod ℓ) < 9·10⁻⁴ bits`, ℓ∈{2,3,5,7}, both mod-12 classes, `p≈1.3·10⁵` \| **`[EMPIRICAL —  | `cm_lattice_setup_v1.py` | Y | · | · | · | PENDING |
| 7.2 | `RESULT_coherent_pool_P0prime_v1.md` | char-vs-null effect, not a pool construction bias.** `[VERIFIED — empirical, real null]` | `check_no_float.py` | Y | · | · | · | PENDING |
| 7.3 | `RESULT_d2_twist_rigidity_certificate_v1.md` | **Date 2026-08-21. Grade: `[VERIFIED — exact, decidable artifact]`** for every structural check below | `d2_twist_rigidity_certificate_v1.py` | Y | · | · | · | PENDING |
| 7.4 | `RESULT_descendant_frame_operator_v2.md` | is made (see §3 for why that phrasing, not the withdrawn one).* | `int1_frame_operator_v1.py` | Y | · | · | · | PENDING |
| 7.5 | `RESULT_diffset_cubic_cmvanishing_v1.md` | > ## ⊘ HEADLINE SUPERSEDED (banner added 2026-08-04, retrospective audit) | `cmvanishing_curve_setup.sage` | Y | · | · | · | PENDING |
| 7.6 | `RESULT_eis_carry_2d_dlp_reduction_v1.md` | `[EMPIRICAL — powered family null]` corroboration (`RESULT_eps_to_d_constraint_v2`).** Curve | `t2c_range_glv_structure_v1.py` | Y | · | · | · | PENDING |
| 7.7 | `RESULT_flap_a_invariance_v1.md` | exploratory, D3 classifier densities, D4 gate pool, D5 `check_no_float` fails on the carve-out lines, | `flap_a_invariance_v1.py` | Y | · | · | · | PENDING |
| 7.8 | `RESULT_flap_density_glv_130bit_null_v1.md` | # 130-bit vs 256-bit scalar: flap density of P=dG — high-powered NULL (no density bias) | `flap_density_glv_prereg_v1.py` | Y | · | · | · | PENDING |
| 7.9 | `RESULT_fld_6h_theorem_assembly_v4.md` | `[VERIFIED, not proved]`." **That split was an artifact of computing the wrong flap formula for the | `fld_root_symmetry_v1.py` | Y | · | · | · | PENDING |
| 7.10 | `RESULT_glm_flap_arithmetic_test_v1.md` | (spec honored verbatim); χ² ranked against a matched permutation null (the one float use the | `glm_flap_harness.py` | Y | · | · | · | PENDING |
| 7.11 | `RESULT_glv_norm_readout_matched_null_v1.md` | **Grade:** `[EMPIRICAL — SCOPED NULL]`, power and scope stated in §4. **The avenue is NOT closed.** | `glv_norm_readout_matched_null_v1.py` | Y | · | · | · | PENDING |
| 7.12 | `RESULT_h5_cofactor_artifact_v1.md` | # RESULT — H-5 resolved: the Semaev CM relation-yield lever is a COFACTOR / subgroup-confinement artifact of n | `h5_followup_run_v1.py` | Y | · | · | · | PENDING |
| 7.13 | `RESULT_h5_cofactor_restoration_v1.md` | - **M25 / N22 H1 leg** → re-graded from `[null — cofactor/sampling artifact]` to | `h5_cofactor_restoration_run_v1.py` | Y | · | · | · | PENDING |
| 7.14 | `RESULT_h5_cofactor_restoration_v2.md` | - **M25 / N22 H1 leg** stays `[null — cofactor/sampling artifact, model scale]`, now upgraded in | `h5_cofactor_restoration_run_v1.py` | Y | · | · | · | PENDING |

---

## Batch 8

| # | document | object / null claim | script | repro | A | B | C | status |
|---|---|---|---|---|---|---|---|---|
| 8.1 | `RESULT_harmonic_deficit_locus_v1.md` | > **⚠ RETRACTED (2026-07-21) — the "b=0 axis LOCALIZATION" claimed below is a WRONG-NULL ARTIFACT.** | `_axis_null_check_v1.py` | Y | · | · | · | PENDING |
| 8.2 | `RESULT_incomplete_sum_2p128_firstorder_v1.md` | **Grade:** `[EMPIRICAL — SCOPED NULL]`. The channel is **not** closed; §4 states what is untouched. | `incomplete_sum_2p128_firstorder_v1.py` | Y | · | · | · | PENDING |
| 8.3 | `RESULT_intensity_field_spatial_item2b_v1.md` | # RESULT — ITEM 2 REMAINDER: spatial statistics of `\|T(a,b)\|²`. No structure established; THREE artifacts ca | `intensity_field_rmt_v1.py` | Y | · | · | · | PENDING |
| 8.4 | `RESULT_interval_C4_M2000_v1.md` | # RESULT — C.4: the interval channel at `M = 2000`. A quantified BOUND (18.5× tighter), not a null. | `interval_C4_M2000_v1.py` | Y | · | · | · | PENDING |
| 8.5 | `RESULT_interval_cneg_recalibration_v1.md` | # RESULT — the `E₆` control debt is DISCHARGED; item C.2 unblocked; one new caveat on the field `E₃` null | `interval_cneg_recalibration_v1.py` | Y | · | · | · | PENDING |
| 8.6 | `RESULT_interval_inversion_and_hamming_v1.md` | **Grade:** `[EMPIRICAL — SCOPED NULL]`, power stated. **Neither covariate is closed as a channel.** | `interval_inversion_and_hamming_v1.py` | Y | · | · | · | PENDING |
| 8.7 | `RESULT_interval_multireadout_v2.md` | # RESULT — interval confinement, extended: larger `M`, group-law difference, and a readout axis that turned ou | `interval_multireadout_v3.py` | Y | · | · | · | PENDING |
| 8.8 | `RESULT_interval_sumobject_item3_v1.md` | **Log:** `item3_run_v1.log`. **Grade:** `[EMPIRICAL — SCOPED NULL]`, power measured. | `interval_sumobject_v1.py` | Y | · | · | · | PENDING |
| 8.9 | `RESULT_interval_vs_random_characterize_v1.md` | **Grade: `[EMPIRICAL — earned; located artifact + scoped bound]`.** This is the test I had SKIPPED, | `shortscalar_interval_vs_random_characterize_v1.py` | Y | · | · | · | PENDING |
| 8.10 | `RESULT_jacobi_closed_form_m_law_v3.md` | **Supersedes:** v2 (which superseded v1). **v3 is a correctness fix**: v1 and v2 both misnamed the | `jacobi_closed_form_m_law_v2.sage` | Y | · | · | · | PENDING |
| 8.11 | `RESULT_large_p_and_arrangement_v1.md` | # Larger primes on the `I` lens, and arrangement correlations — the semicircle null's blind side | `phase_family_scan_v1.py` | Y | · | · | · | PENDING |
| 8.12 | `RESULT_lmono_brick1_gkr_inputs_v1.md` | Scripts: `lmono_brick1_branch_v2.sage` (+ `.log`, `lmono_brick1_branch.json`; v1 superseded — see the | `lmono_brick1_branch_v2.sage` | Y | · | · | · | PENDING |
| 8.13 | `RESULT_lrc_null_typing_transfer_v1.md` | # Retyping the lift×band null under the LRC coverage-transport taxonomy (v1, 2026-07-23) | `lift_band_spectral_v1.py` | Y | · | · | · | PENDING |
| 8.14 | `RESULT_mu3_glv_frequency_support_v1.md` | **Grade:** `[EMPIRICAL — scoped null, τ-robust, well-powered]`. **No grade change** to the underlying | `mu3_glv_frequency_support_v1.py` | Y | · | · | · | PENDING |

---

## Batch 9

| # | document | object / null claim | script | repro | A | B | C | status |
|---|---|---|---|---|---|---|---|---|
| 9.1 | `RESULT_mu3_phase_within_triple_v1.md` | **Grade:** `[EMPIRICAL — scoped null, corrected null]`. No grade change to the −13.99σ deficit | `mu3_phase_within_triple_v1.py` | Y | · | · | · | PENDING |
| 9.2 | `RESULT_mu3_projection_v1.md` | **Scripts:** `mu3_projection_v1.py` (primary D₄ + plants), `mu3_selfnull_v1.py` (per-readout self-null), | `mu3_projection_v1.py` | Y | · | · | · | PENDING |
| 9.3 | `RESULT_mu3_subspace_residual_v1.md` | # RESULT — μ₃-forced subspace residual: three probes, scoped null on the powered-strata | `mu3_subspace_residual_v1.py` | Y | · | · | · | PENDING |
| 9.4 | `RESULT_mu6_cohomology_supersingular_v2.md` | Artifact: `supersingular_mu4_mechanism_v1.py` + `.log` (Sage, exact integer point counts over | `supersingular_mu4_mechanism_v1.py` | Y | · | · | · | PENDING |
| 9.5 | `RESULT_mu6_finer_syzygy_R1R2_v1.md` | **Grade:** R1 finer-syzygy lever `[VERIFIED — NULL, matched-quo, quo=2, m=2, p=523; single clean cell]`; | `r1_syzygy_m2.py` | Y | · | · | · | PENDING |
| 9.6 | `RESULT_mu6_isotypic_solving_degree_P2b_v1.md` | `[VERIFIED — scoped NULL, m∈{2,3}, p∈[523,601], last-fall degree]`. | `omega_isotypic_staircase_v1.py` | Y | · | · | · | PENDING |
| 9.7 | `RESULT_mu6_solving_degree_v1.md` | **`[EMPIRICAL — scoped component null; PROVISIONAL, citation-verifier owed]`.** **Object:** the last-fall degr | `mu6_solving_degree_v1.py` | Y | · | · | · | PENDING |
| 9.8 | `RESULT_n1_120deg_independent_reproduction_v1.md` | a document cannot witness its own audit; [[feedback-verification-claim-needs-artifact-2026-07-24]]). | `n1_120deg_g2_honest_reproduction_v1.py` | Y | · | · | · | PENDING |
| 9.9 | `RESULT_n1_cap_intersection_v1.md` | project's existing monodromy corpus shows that conclusion **converges with — and is superseded by — | `verify_e3_sign.sage` | Y | · | · | · | PENDING |
| 9.10 | `RESULT_n1_cap_proof_attempt_v2.md` | > # ⚠ SUPERSEDED — read `RESULT_n1_cap_intersection_v1.md` instead | `sage_ynq_v3.sage` | Y | · | · | · | PENDING |
| 9.11 | `RESULT_n1_flap_bridge_v1.md` | **Date:** 2026-07-25 · Scripts: `n1_flap_bridge_v1.py` (superseded statistic), `n1_flap_bridge_v2.py` | `n1_flap_bridge_v1.py` | Y | · | · | · | PENDING |
| 9.12 | `RESULT_n1_phase_cap_v2.md` | # RESULT v2 — N1 re-typed to a phase-pairing question; the v1 headline is withdrawn | `n1_phase_cap_sweep_v1.py` | Y | · | · | · | PENDING |
| 9.13 | `RESULT_n1_v_sign_mechanism_v1.md` | # N1: WHY `v ≤ 0` fails — an exact identity, and the conjecture restated as a sub-Weil bound | `n1_vsign_mechanism_v1.py` | Y | · | · | · | PENDING |
| 9.14 | `RESULT_n7_finite_rank_refuted_v1.md` | `[VERIFIED]` for the null-is-Rayleigh baseline; `[EMPIRICAL — suggestive, n=6, min-statistic]` for | `n7_finite_rank_v1.py` | Y | · | · | · | PENDING |

---

## Batch 10

| # | document | object / null claim | script | repro | A | B | C | status |
|---|---|---|---|---|---|---|---|---|
| 10.1 | `RESULT_nkd_dterms_subsurface_v2.md` | ## 4. Correction: NOT 2-adic — Dirichlet-generic in L `[VERIFIED — matched control]` | `nkd_dterms_mechanism_v1.py` | Y | · | · | · | PENDING |
| 10.2 | `RESULT_overlap_arm_power_v1.md` | `rho` against a 200-permutation null of the curve vector, and prints `\|z\|`. That arm shipped a matched | `lift_band_spectral_v1.py` | Y | · | · | · | PENDING |
| 10.3 | `RESULT_powermap_familywide_from_settlement_v1.md` | **Grade:** `[VERIFIED — calibrated pooled + K=2 OOS, 36-prime scan, gate firing]` for the NULLs; pow7 is a `po | `cside_orbitlevel_v1.py` | Y | · | · | · | PENDING |
| 10.4 | `RESULT_pubkey_relations_controlled_v1.md` | # RESULT — exposed-pubkey relations: the "found none" null was UNCONTROLLED; redone with a control | `pubkey_relations_controlled_v1.py` | Y | · | · | · | PENDING |
| 10.5 | `RESULT_r3_orbit_autocorrelation_v1.md` | `[EMPIRICAL — bounded; code-shuffle matched null; 5-seed OOS; gate-cleared]`. | `r3_orbit_autocorrelation_v1.py` | Y | · | · | · | PENDING |
| 10.6 | `RESULT_rmt_battery_on_spectrum_item2c_v1.md` | **Date:** 2026-08-01. **Script:** `transfer_operator_rmt_battery_v1.py`. **Grade:** `[EMPIRICAL — NULL, power  | `transfer_operator_rmt_battery_v1.py` | Y | · | · | · | PENDING |
| 10.7 | `RESULT_rmt_delta3_twopoint_item2_v1.md` | **Date:** 2026-08-01. **Script:** `rmt_delta3_twopoint_v1.py`. **Grade:** `[EMPIRICAL — SCOPED NULL]`. | `rmt_delta3_twopoint_v1.py` | Y | · | · | · | PENDING |
| 10.8 | `RESULT_scale_cm_laws_ladder_v1.md` | **Artifact:** `scale_cm_laws_ladder_v1.sage` (exact; passes `check_no_float.py`). | `scale_cm_laws_ladder_v1.sage` | Y | · | · | · | PENDING |
| 10.9 | `RESULT_semaev_cm_relation_yield_v3_wide.md` | experiment-designer gate-CLEARED; matched-#E null; firing controls live; m=3; \|V\|∈{4,5}]`.** | `semaev_cm_relation_yield_v3.py` | Y | · | · | · | PENDING |
| 10.10 | `RESULT_semaev_cm_solving_degree_v1.md` | # RESULT — P2c: the μ₆/μ₃ CM symmetry gives NO Semaev solving-degree lever (scoped component null, not an aven | `semaev_elimination_v1.py` | Y | · | · | · | PENDING |
| 10.11 | `RESULT_semaev_structure_firstfall_vs_m_v2.md` | unaffected. Owed if this null is ever leaned on beyond `[VERIFIED-scope, model]`. | `semaev_elimination_v1.py` | Y | · | · | · | PENDING |
| 10.12 | `RESULT_semicircle_null_and_verification_v1.md` | # The cap-respecting null, the re-adjudicated curve-native panels, and the `V₂` identity confirmed | `semicircle_null_v1.py` | Y | · | · | · | PENDING |
| 10.13 | `RESULT_shortscalar_sum_stageA_v1.md` | - `[EMPIRICAL — bounded, correctly-matched null]` for the band-confinement result (Q2). | `shortscalar_sum_stageA_v1.py` | Y | · | · | · | PENDING |
| 10.14 | `RESULT_shortscalar_sum_stageA_v2.md` | **Grade: `[EMPIRICAL — bounded; correctly-matched null; 5-seed OOS; NO closure]`.** | `shortscalar_sum_stageA_v2.py` | Y | · | · | · | PENDING |

---

## Batch 11

| # | document | object / null claim | script | repro | A | B | C | status |
|---|---|---|---|---|---|---|---|---|
| 11.1 | `RESULT_sidechannel_island_leak_infeasibility_v1.md` | null and NOT an ECDLP-security claim. It is a decidable feasibility finding about | `nested_recursion_worked_example_v1.py` | Y | · | · | · | PENDING |
| 11.2 | `RESULT_subrayleigh_deficit_arithmetic_scatter_v1.md` | > **⚠ SUPERSEDED by RESULT_...arithmetic_scatter_v2.md.** This v1 headline OVERCLAIMS: it reads the | `arithmetic_scatter_sweep_v1.py` | Y | · | · | · | PENDING |
| 11.3 | `RESULT_subrayleigh_deficit_arithmetic_scatter_v2.md` | ~44% explained. Corrected below. Everything else in v1 (H2 firing, H1 null, controls, robustness) holds. | `arithmetic_scatter_sweep_v1.py` | Y | · | · | · | PENDING |
| 11.4 | `RESULT_subrayleigh_deficit_scaling_v1.md` | Deviations: `PREREG_subrayleigh_deficit_scaling_v1_DEVIATIONS.md` (D1 prereg numeral slip, no effect; | `subrayleigh_deficit_scaling_v1.py` | Y | · | · | · | PENDING |
| 11.5 | `RESULT_t2c_carry_partition_kangaroo_bench_v1.md` | **Grade:** `[VERIFIED-scope — scoped null / no computational advantage; fair op-model, two model curves, | `t2c_carry_composition_bench_v2.py` | Y | · | · | · | PENDING |
| 11.6 | `RESULT_t2c_range_carry_skew_exact_v1.md` | **Date 2026-08-21. Grade: `[VERIFIED — exact integer counts; decidable artifact]`** for the | `t2c_range_carry_skew_exact_v1.py` | Y | · | · | · | PENDING |
| 11.7 | `RESULT_twist_orbit_forced_landscape_v1.md` | **Preview** `[EMPIRICAL — in-sample, design-only]` (`forced_landscape_v1.py`): null-ish at 5 in-sample | `twist_orbit_magnitude_run_v1.py` | Y | · | · | · | PENDING |
| 11.8 | `RESULT_weight1_phase_ramp_v1.md` | **(c) `[EMPIRICAL — bounded null, secp class, powered]` Where it exists, the channel does NOT align with | `weight1_phase_ramp_v1.py` | Y | · | · | · | PENDING |
| 11.9 | `RESULT_weyl_xreadout_item4_v1.md` | # RESULT — ITEM 4: quadratic (Weyl) phases on the x-readout. FOUR instrument faults; result is LOW-POWER, not  | `weyl_xreadout_item4_v1.py` | Y | · | · | · | PENDING |
| 11.10 | `RESULT_y_channel_chi2_vs_axis_v1.md` | > **⚠ SUPERSEDED (2026-07-21) — the "axis deficit" analyzed below is largely a WRONG-NULL ARTIFACT** | `_axis_null_check_v1.py` | Y | · | · | · | PENDING |
| 11.11 | `VALIDATION_sssa_lift_firing_control_v1.md` | **Layer:** mechanical only (per CLAUDE.md §2a: "does the plant fire", exactness) — self-audit + artifact | `sssa_lift_control_v1.py` | Y | · | · | · | PENDING |
| 11.12 | `VOID_anew_cartier_c4_adjudication_v1.md` | # VOID — the Cartier-arm adjudication of 2026-08-02, control C4 fired | `anew_cartier_audit_v1.sage` | Y | · | · | · | PENDING |
| 11.13 | `btc_puzzle_research_plan_v3.md` | Date: 2026-07-08. Supersedes selection logic in v1/v2 (does not retract their | `power_scaling.py` | Y | · | · | · | PENDING |
| 11.14 | `btc_puzzle_research_plan_v6.md` | # BTC Puzzle — Research Plan v6 (gap audit: what the null battery never touched) | `power_scaling.py` | Y | · | · | · | PENDING |

---

## Batch 12

| # | document | object / null claim | script | repro | A | B | C | status |
|---|---|---|---|---|---|---|---|---|
| 12.1 | `masked_structure_findings_v1.md` | ### A — μ₃-invariant cubic moment `E[z³]` [null, scoped, well-controlled] | `masked_structure_harness_v1.py` | Y | · | · | · | PENDING |
| 12.2 | `masked_structure_findings_v13.md` | investigation that is a **proof general in p** (covers secp), not a small-p empirical null. | `summation_poly_structure_v1.py` | Y | · | · | · | PENDING |
| 12.3 | `masked_structure_findings_v20.md` | work (v9/v10/v11) counted relation/decomposition **yield** (generic) and v13 analysed a **single** | `semaev_elimination_v1.py` | Y | · | · | · | PENDING |
| 12.4 | `masked_structure_findings_v22.md` | - **(b)** **no soft mode beyond μ₆ in general y-readouts** `[EMPIRICAL, p≤2503, multi-shuffle null]` | `conservation_spectrum_v2.py` | Y | · | · | · | PENDING |
| 12.5 | `masked_structure_findings_v26.md` | Tautology ≠ no structure (Dₖₙ/D_err is how we found the Eisenstein lift, rhombus, sextic, 3/4-1/8-1/8). | `positive_structure_hunt_v1.py` | Y | · | · | · | PENDING |
| 12.6 | `masked_structure_findings_v31.md` | unique additive cocycle." The finding is deeper than an empirical null: it is a **theorem** (prime | `carry_cocycle_v1.py` | Y | · | · | · | PENDING |
| 12.7 | `masked_structure_findings_v32.md` | ## (1) Finer-m difference scan `[VERIFIED, powered null, control fires]` | `difference_set_xy_geometry_v1.py` | Y | · | · | · | PENDING |
| 12.8 | `masked_structure_findings_v8.md` | Framing (user): ECDLP is a fence, not a proven wall — a null is scoped to the statistic and | `collinear_lift_structure_v1.py` | Y | · | · | · | PENDING |
| 12.9 | `phi_n_native_knd_findings_v1.md` | (the user's RH-line framework), not generic ML. Prior "k has no structure" nulls | `phi_n_native_prime_content_v1.py` | Y | · | · | · | PENDING |
| 12.10 | `phi_n_residue_XY_findings_v1.md` | lens — the framework's OWN basis, not generic ML. Statistics: the Ramanujan-sum | `phi_n_residue_q53_replicate_v1.py` | Y | · | · | · | PENDING |
| 12.11 | `struct_test_results.md` | ## Test A — reverse-ladder branch predictor → NULL (measured 2026-07-08) | `puzzle_kangaroo.py` | Y | · | · | · | PENDING |
| 12.12 | `AUDIT_m25_n15_null_conversions_v1.md` | # AUDIT — the M25 & N15 null-conversions: are they fired-surrogate-established, or assumed-away? | `—` | N | · | · | · | NO-REPRO |
| 12.13 | `AUDIT_m25_n15_null_conversions_v2.md` | surfaces** — v18's one-line flag row (`M25 \| [A−] \| [null …]`, accurate for the H1 leg it names) and | `—` | N | · | · | · | NO-REPRO |
| 12.14 | `AUDIT_m25_n15_null_conversions_v3.md` | # AUDIT — M25 & N15 null-conversions (v3): the external review ran the two remainders, and both close | `—` | N | · | · | · | NO-REPRO |

---

## Batch 13

| # | document | object / null claim | script | repro | A | B | C | status |
|---|---|---|---|---|---|---|---|---|
| 13.1 | `CORRECTION_e3_cmvanishing_interaction_reading_v1.md` | # ⊘ SCOPE-WITHDRAWN — CORRECTION — the E3 curve-swap establishes a key-set × curve INTERACTION | `—` | N | · | · | · | NO-REPRO |
| 13.2 | `PREREG_cm_jointset_excess_v1.md` | statistic computed in this task.** Decidable artifact. Designed by the context-isolated | `cm_jointset_excess_v1.py` | N | · | · | · | NO-REPRO |
| 13.3 | `PREREG_cside_replication_v1.md` | OOS AND-gate. **In-scope:** the null is orbit-label permutation (curve-intrinsic), not a generator pool | `—` | N | · | · | · | NO-REPRO |
| 13.4 | `PREREG_deflation_120deg_generic_j_v1.md` | # PRE-REGISTRATION — is the 120° law generic to odd-order cyclic elliptic curves, or specific to `j=0`? | `—` | N | · | · | · | NO-REPRO |
| 13.5 | `PREREG_deflation_120deg_generic_j_v1_DEVIATIONS.md` | **Date:** 2026-08-01. **Status of the spec: WITHDRAWN BEFORE DATA. The run was never executed.** | `—` | N | · | · | · | NO-REPRO |
| 13.6 | `RESULT_joint_carry_twokey_mi_v1.md` | **`[VERIFIED-scope NULL]`.** **Object:** cross-point synergy of the summand-flap `A=b_eps(x_{P₂})` and | `scratchpad/joint_carry_twokey_mi_v1.py` | N | · | · | · | NO-REPRO |
| 13.7 | `RESULT_joint_fiber_carry_mi_v1.md` | **`[VERIFIED-scope NULL]`.** **Object:** cross-channel dependence between the public coordinate flap | `scratchpad/joint_fiber_carry_mi_v1.py` | N | · | · | · | NO-REPRO |
| 13.8 | `ANALYSIS_idea_improvements_and_nogo_relook_v1.md` | test*, not a result. Each carries its readout, matched null, firing control, scope, and the grade its | `—` | N | · | · | · | NO-REPRO |
| 13.9 | `ANALYSIS_interval_charsum_generic_prediction_v1.md` | # The generic prediction for the interval character sum — committed BEFORE the L=80000 row | `—` | N | · | · | · | NO-REPRO |
| 13.10 | `ANALYSIS_island_twist_sextic_q2q3_v1.md` | Q3 `[structural null — island determines π_n but does not display the symbol]`.** Date 2026-08-17. Follows | `—` | N | · | · | · | NO-REPRO |
| 13.11 | `ANALYSIS_mu6_solving_degree_m4m5_mechanism_v1.md` | # ANALYSIS — the m=4/5 mechanism: does the ω-symmetry lower the S₅/S₆ solving degree? The isotypic-block chann | `m4_mechanism_check.py` | N | · | · | · | NO-REPRO |
| 13.12 | `ANALYSIS_semaev_cm_yield_mechanism_v1.md` | > (prime-field summation-poly index calculus is non-competitive with generic √p to begin with). **§4 is | `—` | N | · | · | · | NO-REPRO |
| 13.13 | `AUDIT_prereg_incomplete_shortscalar_SELFAUDIT_v1.md` | *2026-07-29. **THIS IS NOT THE GATE.** `experiment-designer` was launched twice and failed both times | `tdev_calib.py` | N | · | · | · | NO-REPRO |
| 13.14 | `COMPENDIUM_mu6_lever_v1.md` | ### 4. Characters index the orbits — `[EMPIRICAL — real skew]` + boundary null | `—` | N | · | · | · | NO-REPRO |

---

## Batch 14

| # | document | object / null claim | script | repro | A | B | C | status |
|---|---|---|---|---|---|---|---|---|
| 14.1 | `CONFIRMED_k3_phase_channel_weierstrass_v1.md` | **Grade: EMPIRICAL / VERIFIED-scope** — survives a *negation-parity-matched* permutation null | `scratchpad/k3_fixed.py` | N | · | · | · | NO-REPRO |
| 14.2 | `KNOWN_FACTS_secp256k1_and_keys_v5.1.md` | or tags changed — correcting places where the body prose stated a *null* or an | `—` | N | · | · | · | NO-REPRO |
| 14.3 | `KNOWN_FACTS_secp256k1_and_keys_v5.md` | numbers, or tags changed). v5 corrects places where the body prose stated a *null* | `—` | N | · | · | · | NO-REPRO |
| 14.4 | `LEAK_HUNT_LEDGER_2026_08_11_v1.md` | to find *how* it leaks. "ECDLP is secure / nothing here / generic" is the training reflex this project | `—` | N | · | · | · | NO-REPRO |
| 14.5 | `NOTE_carry_readout_leak_nulls_v1.md` | **Grade: `[EMPIRICAL — scoped null, firing controls fire; small scale n=967]`.** Date 2026-08-17. Active | `scratchpad/eps_leak.py` | N | · | · | · | NO-REPRO |
| 14.6 | `NOTE_menu_move2_monodromy_N7_refuted_v1.md` | **Grade:** `[VERIFIED-scope — named mechanism refuted by an on-disk at-scale artifact]`, model | `—` | N | · | · | · | NO-REPRO |
| 14.7 | `NOTE_n7_xy_axis_localization_v1.md` | `PREREG_subrayleigh_deficit_scaling_v1.md` ("report D restricted to strata {b=0},{c=0},{b=c},generic | `scratchpad/cubic_coherence/probes12_v1.py` | N | · | · | · | NO-REPRO |
| 14.8 | `NOTE_v15_draft_three_frontiers_grounded_out_v1.md` | all three. **Each grounds out — as tested-null, object-obstructed, or classical-known — for a NAMED | `..._v2.py` | N | · | · | · | NO-REPRO |
| 14.9 | `PLAN_interval_charsum_realbranch_characterization_v1.md` | # Real-branch characterization plan — what to run IF L=80000 refutes the generic prediction | `—` | N | · | · | · | NO-REPRO |
| 14.10 | `PLAN_representation_boundary_program_v1.md` | **Date:** 2026-08-13. Follows `ANALYSIS_public_gate_glv_carry_circularity_v1.md` (which failed the | `—` | N | · | · | · | NO-REPRO |
| 14.11 | `POSITIVE_FINDINGS_MASTER_v18.md` | > `\|V_y\|≤2√p`** is `[PROVED — symbolic]` only MODULO the Weil-II purity citation (N31, failed | `—` | N | · | · | · | NO-REPRO |
| 14.12 | `PREREG_brick_e_cd_degree_v1.md` | pre-registration. Time-order preserved: the statistic, matched null, firing controls, and falsification | `—` | N | · | · | · | NO-REPRO |
| 14.13 | `PREREG_bridge_dichotomy_v1_DEVIATIONS.md` | `D = −7, −8, −15, −20` gave `< 40` instances in v1. This was **not** treated as a null: the cause | `—` | N | · | · | · | NO-REPRO |
| 14.14 | `PREREG_bridge_mechanism_isolation_v1_DEVIATIONS.md` | 1. **H-constant's sub-claim (iii) failed and the hypothesis was repaired post-hoc.** The prereg's | `cubic_bridge_v1.py` | N | · | · | · | NO-REPRO |

---

## Batch 15

| # | document | object / null claim | script | repro | A | B | C | status |
|---|---|---|---|---|---|---|---|---|
| 15.1 | `PREREG_c2_grouplaw_diffset_v2.md` | Supersedes v1, which the gate FAILED with 2 blocking defects (retained as the record). Executes | `—` | N | · | · | · | NO-REPRO |
| 15.2 | `PREREG_cm_decomposition_count_PROVISIONAL_v1.md` | > **⛔ SUPERSEDED (2026-08-09) — DO NOT RUN.** Written on session-resume without awareness that | `scratchpad/grounding_cm_curves_v1.py` | N | · | · | · | NO-REPRO |
| 15.3 | `PREREG_cm_hecke_grossencharacter_vertical_v1.md` | the object, the single decidable artifact, the anti-tautology construction, the matched/firing | `—` | N | · | · | · | NO-REPRO |
| 15.4 | `PREREG_diffset_cubic_beta2_characterization_v1.md` | decomposition — **no reject/accept verdict**; every sub-slice carries its own matched null. | `—` | N | · | · | · | NO-REPRO |
| 15.5 | `PREREG_diffset_cubic_secondcontrol_v1.md` | **Status:** rule + interpretation FROZEN before the new null is built. Reproduction of the fired | `—` | N | · | · | · | NO-REPRO |
| 15.6 | `PREREG_ell_ge5_conditional_MI_v2_DEVIATIONS.md` | Filed as they occurred. None changes a verdict (all arms null in + OOS); all are recorded plainly. | `ell_condmi_verify_designer_v1.py` | N | · | · | · | NO-REPRO |
| 15.7 | `PREREG_ell_ge5_mutual_information_v2_DEVIATIONS.md` | the null point; it is not — copying with probability `s` adds correlation on top of the baseline, so | `—` | N | · | · | · | NO-REPRO |
| 15.8 | `PREREG_isotypic_trace_carry_stratify_v1.md` | built around neutralizing it (orbit-rep reduction + rank-in-matched-null + a power gate that ABSTAINS | `—` | N | · | · | · | NO-REPRO |
| 15.9 | `PREREG_localized_bit_extraction_v2.md` | **Predecessor:** `PREREG_localized_bit_extraction_v1.md` (v1 battery, outcome N1, scoped bounded null). | `—` | N | · | · | · | NO-REPRO |
| 15.10 | `PREREG_mu3_glv_frequency_support_v2.md` | statistic, Null-B, power, scope, and falsification — **unchanged** by this amendment). | `—` | N | · | · | · | NO-REPRO |
| 15.11 | `PREREG_semaev_yield_frobenius_channel_P1_v1.md` | **Gate:** this is itself the pre-registration artifact. | `—` | N | · | · | · | NO-REPRO |
| 15.12 | `PREREG_twist_orbit_magnitude_v1_DEVIATIONS.md` | excluded; 0 of 90/150 non-DC even-`μ₃`-trivial coefficients forced-zero; null non-degenerate); null | `—` | N | · | · | · | NO-REPRO |
| 15.13 | `PREREG_twist_orbit_monodromy_v1.md` | \| `E[u⁴]` within the iid-SU(2) band at S, and the deviation from 1/8 shrinks with `p` \| **full SU(2) monodro | `monodromy_preview_v1.py` | N | · | · | · | NO-REPRO |
| 15.14 | `PREREG_twist_orbit_monodromy_v1_DEVIATIONS.md` | iid-SU(2) null (centered at the asymptotic `1/8`) is correctly matched to finite-p data, given all 7 | `monodromy_preview_v1.py` | N | · | · | · | NO-REPRO |

---

## Batch 16

| # | document | object / null claim | script | repro | A | B | C | status |
|---|---|---|---|---|---|---|---|---|
| 16.1 | `RESULT_anew_multiprime_torsion_exploratory_v1.md` | # RESULT — multi-prime torsion channels (ℓ=7,19): reduced-scale EXPLORATORY null (not the powered verdict) | `powered_gen.sage` | N | · | · | · | NO-REPRO |
| 16.2 | `RESULT_diffset_cubic_beta2_characterization_v1.md` | null, 3000 resamples. Integer-exact. | `—` | N | · | · | · | NO-REPRO |
| 16.3 | `RESULT_diffset_sdiff_v1.md` | **Grade:** `[MEASURED-EXACT — scoped null for the frozen-orientation projection, n=82, secp P]`. | `—` | N | · | · | · | NO-REPRO |
| 16.4 | `RESULT_dirichlet_island_structure_and_leakage_v1.md` | **Grade: Part A `[VERIFIED — exact, real secp params]`; Part B `[EMPIRICAL — NULL at power, scale-resolved]`.* | `scratchpad/islands_rethink.py` | N | · | · | · | NO-REPRO |
| 16.5 | `RESULT_ell_ge5_mutual_information_v1.md` | # ℓ≥5: the blind spot held no bridge — a mutual-information probe tightens the D3 null | `ell_mi_oos.py` | N | · | · | · | NO-REPRO |
| 16.6 | `RESULT_eps_to_d_constraint_v1.md` | ## Results — `[EMPIRICAL — SCOPED NULL; plant-fired, powered]` | `scratchpad/eps_to_d_run_v1.py` | N | · | · | · | NO-REPRO |
| 16.7 | `RESULT_eps_to_d_constraint_v2.md` | ## Results — `[EMPIRICAL — FAMILY-WIDE SCOPED NULL; plant-fired, powered]` | `scratchpad/eps_to_d_family_v2.py` | N | · | · | · | NO-REPRO |
| 16.8 | `RESULT_exclusion_hard_empty_cells_v1.md` | **Date:** 2026-08-16. **`[EMPIRICAL — scoped null on HARD exclusion; NOT "impossible"]`.** Gate-free | `scratchpad/exclusion_occupancy_v1.py` | N | · | · | · | NO-REPRO |
| 16.9 | `RESULT_intertwined_proxy_WN_tested_v1.md` | **Grade of this finding:** `[VERIFIED — decidable artifact]` for the mechanism incoherence (§2.1–2.2); | `scratchpad/test_intertwined_proxy.py` | N | · | · | · | NO-REPRO |
| 16.10 | `RESULT_item5_deep_k135_v1.md` | **Grade:** `[EMPIRICAL — BOUND, power measured]`. **Not a null.** | `—` | N | · | · | · | NO-REPRO |
| 16.11 | `RESULT_linchpin_s_gate_v2.md` | trail). **Artifact:** `scratchpad/linchpin_s_gate_v1.py` + stdout. Exact arithmetic | `scratchpad/linchpin_s_gate_v1.py` | N | · | · | · | NO-REPRO |
| 16.12 | `RESULT_linchpin_s_gate_verified_v1.md` | > **SUPERSEDED by `RESULT_linchpin_s_gate_v2.md` (2026-08-11). Kept as trail.** v1's title/grade | `scratchpad/linchpin_s_gate_v1.py` | N | · | · | · | NO-REPRO |
| 16.13 | `RESULT_mu6_cover_and_conductor_v2.md` | *2026-07-23. Supersedes `RESULT_mu6_cover_and_conductor_v1.md`, which is **superseded in §1 and carries | `scratchpad/mu6_derivation.py` | N | · | · | · | NO-REPRO |
| 16.14 | `RESULT_mu6_isotype_leak_structure_v1.md` | # μ6-isotype grading of readouts — tying the flap-null to the leak-structure | `scratchpad/mu6_isotype.py` | N | · | · | · | NO-REPRO |

---

## Batch 17

| # | document | object / null claim | script | repro | A | B | C | status |
|---|---|---|---|---|---|---|---|---|
| 17.1 | `RESULT_mu6_quotient_relation_multiplication_v1.md` | it does NOT need to beat generic `√n` or solve ECDLP to count. Disparate real findings compound; recording a | `—` | N | · | · | · | NO-REPRO |
| 17.2 | `RESULT_orbit_bit_ladder_v1.md` | exact over `Z/n`. Supersedes the verdict-language framing ("trivial symmetry / no lever") used earlier in | `—` | N | · | · | · | NO-REPRO |
| 17.3 | `RESULT_outside_symmetry_v2.md` | symmetrized norm N̄ as "within null (flat/geometric)". They are NOT within the null — they are | `scratchpad/e_outside.py` | N | · | · | · | NO-REPRO |
| 17.4 | `RESULT_outside_symmetry_v3.md` | # "Outside the symmetry" v3 — CORRECTS the "flat/geometric" characterization | `scratchpad/diag_mechanism.py` | N | · | · | · | NO-REPRO |
| 17.5 | `RESULT_plays_1_and_4_refuted_predata_v1.md` | **Status: DERIVATION + exact verification.** No statistic, no null, no p-value on either posed | `—` | N | · | · | · | NO-REPRO |
| 17.6 | `RESULT_public_feature_dmodq_battery_v1.md` | **Grade: `[EMPIRICAL — NULL at power, SCOPED]`.** Date 2026-08-17. Motivation: the D2/mod-6 audit | `scratchpad/idea2.py` | N | · | · | · | NO-REPRO |
| 17.7 | `RESULT_score_exclusion_rangecut_v1.md` | **`[VERIFIED — deterministic refutation, exact artifact]`.** The deterministic-pin amplifier route | `scratchpad/score_exclusion_frechet_verify_v1.py` | N | · | · | · | NO-REPRO |
| 17.8 | `RESULT_semaev_cross_twist_yield_P1pp_v1.md` | # RESULT — P1″ INCONCLUSIVE: instrument bug caught, then the pre-registered statistic found to SATURATE. The b | `p1pp_run.py` | N | · | · | · | NO-REPRO |
| 17.9 | `RESULT_semaev_yield_frobenius_channel_P1_v1.md` | computation). **Grade:** `[EMPIRICAL — SCOPED NULL, plant fired → informative; Outcome C]`. Existing R1 data | `p1_run.py` | N | · | · | · | NO-REPRO |
| 17.10 | `RESULT_stickelberger_citation_verified_v1.md` | Discharges the `[UNVERIFIED CITATION]` debt on Stickelberger that failed three prior runs. No leakage | `—` | N | · | · | · | NO-REPRO |
| 17.11 | `RESULT_t1b_tail_geometry_v1.md` | **Artifact:** `scratchpad/t1b_tail_split_v1.py`. Float carve-out: \|U\| magnitudes, integer args in the | `scratchpad/t1b_tail_split_v1.py` | N | · | · | · | NO-REPRO |
| 17.12 | `RESULT_t1b_yaxis_forced_v1.md` | decidable dimensionality fact, not a matched-null verdict). Follows `RESULT_t1b_tail_geometry_v1.md` | `scratchpad/t1b_yaxis_dim_v1.py` | N | · | · | · | NO-REPRO |
| 17.13 | `RESULT_t2d_soft_exclusion_v1.md` | **Date:** 2026-08-16. **`[EMPIRICAL — SCOPED NULL; plant-fired]`.** Runs `PREREG_soft_exclusion_dmodk_v1.md`. | `scratchpad/t2d_soft_exclusion_run_v1.py` | N | · | · | · | NO-REPRO |
| 17.14 | `STRUCTURAL_IMPLICATIONS_2026-07-30_v1.md` | **Epistemic posture:** This document works against the base-model reflex ("ECDLP secure / generic / a wall").  | `—` | N | · | · | · | NO-REPRO |

---

## Batch 18

| # | document | object / null claim | script | repro | A | B | C | status |
|---|---|---|---|---|---|---|---|---|
| 18.1 | `VERIFY_SPEC_jacobi_stickelberger_v1.md` | up front" artifact (`CLAUDE.md` §3), not an experiment pre-registration: the object below is a | `—` | N | · | · | · | NO-REPRO |
| 18.2 | `VOID_item5_k128_adjudication_v1.md` | # VOID — the k=128 adjudication of the Item 5 deep run | `—` | N | · | · | · | NO-REPRO |
| 18.3 | `btc_puzzle_research_plan_v1.md` | 1. **Positive control is mandatory.** A null with no firing control is discarded as | `farm/smoke_test.py` | N | · | · | · | NO-REPRO |
| 18.4 | `btc_puzzle_research_plan_v2.md` | dismissing whole buckets on priors** ("already answered flat", "circular", "needs | `farm/lib_data.py` | N | · | · | · | NO-REPRO |