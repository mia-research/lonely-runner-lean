> **⛔ FROZEN — NOT CURRENT.** This file is a historical snapshot. The single current-state
> document is **`CLAIMS.md`**. Do not read status, grades, or open items from here; do not
> write a successor version of this file. (Frozen 2026-09-01.)

# POSITIVE FINDINGS MASTER — v13

**Date:** 2026-08-21
**Author:** ZCode (audit-driven rewrite of v12)
**Baseline audited:** POSITIVE_FINDINGS_MASTER_v12.md (166KB, 2026-08-18)
**Primary sources:** AUDIT_narrative_conclusion_layer v1–v2, AUDIT_session_conclusions v1, AUDIT_loadbearing_claims v1, AUDIT_item2_overclaims v1, AUDIT_deflation_claim_chain v1, AUDIT_semaev_v4_method_result_conclusion v1 (all synthesized in full), plus a partial extraction of v12's later sections.

---

## Part 0: Scope and Honesty Statement

### 0.1 What this document is

An audit-corrected ledger of the investigation's findings. Every item below is graded by what the **audit trail** actually established, not by what v12 or the project summaries claimed. Where v12's grade diverged from the audited evidence, the corrected grade is given and the divergence is named.

### 0.2 What this document is NOT

It is NOT a complete inventory of the investigation. v12 certified itself "reconciled across master + both addenda" while referencing ADD1 zero times, ADD2 once, and ADD3 zero times. This document makes no completeness claim.

### 0.3 Explicit gaps — source files never read in this pass

A tooling failure in the authoring session (repeated wrong-tool calls) blocked direct reading of the following. Their contents are known here ONLY through the audit documents' summaries, never from source:

| File | Why it matters | Consequence for v13 |
|---|---|---|
| v12 lines 1–1600 (front matter, findings N1–N11, Parts I–X) | First half of the ledger | Only items the audits named by ID are carried forward; the rest are listed as "not re-audited" in Part VII |
| POSITIVE_FINDINGS_ADDENDUM_1_v1.md (87KB) | 7 retractions, 7 frontiers, 1 re-claim | Known only via AUDIT v2's tally |
| POSITIVE_FINDINGS_ADDENDUM_2_v1.md (40KB) | 6 retractions, 13 frontiers, 4 de-sharpenings | Known only via AUDIT v2's tally |
| POSITIVE_FINDINGS_ADDENDUM_3_v1.md (6KB) | 4 frontiers, 1 method-note; 0 items survived consolidation | Never read at all |
| DEGRADATION_AUDIT_H3_TO_MASTER_v1.md | Version-to-version loss tracking | Not read; may hold additional loss inventory |
| COUNTERPRIOR_and_closure_grade_spec_v1.md | Formal closure-grade definitions | Grades below use audit-inferred definitions |
| 9x CORRECTION_*.md files | Formal corrections/downgrades | Known only via audit cross-references |
| CONFIRMED_*.md files | Independently verified results | Known only via audit cross-references |
| POSITIVE_FINDINGS_MASTER_v9.md | Pre-consolidation master | v9-to-v12 diff never performed |

**v14 MUST begin with a full corpus revision of everything in this table.** Until then, treat every grade below as "best audited estimate," not certified.

---

## Part I: Findings That Survive Independent Audit

These were re-tested or exhaustively re-checked. Grades reflect the audit's verdict.

### I.1 KS U-bound — [VERIFIED, SOUND]
`max |U(a,b,c)| <= 4*sqrt(p) + 1`
Exhaustive FFT re-check over all `a` and all `(b,c)` at p = 61, 67, 211. Worst-case ratio `max|U| / (4*sqrt(p)+1) = 0.960`. The single most load-bearing claim in the project; it held. (AUDIT_loadbearing_claims_v1.)

### I.2 Joint (x,y) character-sum shadow at ~0.93 — [VERIFIED, p <= 433]
Metric `max |Corr(a_0)| / ||F||_inf`: x-only ~0.34, joint ~0.93, ratio ~2.7–2.8, reproduced exactly to two decimals at p = 163, 211, 433. Note: the auditor first graded this NOT REPRODUCED, then found they had read the wrong metric from the script output and self-retracted. The claim is real; the false-negative is documented as a failure mode, not a defect in the claim. (AUDIT_loadbearing_claims_v1.)

### I.3 The 2*sqrt(p) cap on |V(a)| — [GENUINE EMPIRICAL GAP; MECHANISM UNPROVEN]
The cap is a factor-2 improvement over every cited bound. But:
- Mechanism M1 (Frobenius-swap): DECIDABLY FALSE. If M1 held, V(a) would vanish identically for nonzero a; measured minima are 1.878 / 1.349 / 0.971 / 0.192 > 0 across four primes.
- Mechanism M2: analytically refuted.
- Mechanism M3 (Katz / small monodromy): the only consistent framework, but monodromy gives the distribution, not the pointwise ceiling.
**Audit verdict: "No verified progress toward proving the cap. Three wrong roads are closed."** The cap stands as an empirical fact with no mechanism. (AUDIT_item2_overclaims_v1.)

### I.4 Proved group-law identities — [PROVED]
- slope-squared identity: `x1 + x2 + x3 = m^2` — a group-law identity, holds unconditionally.
- un-normalized k=3 x chi_2 channel — proved, correctly scoped.
- mu-6 6x relation (multiplication structure) — verified exact, correctly scoped.

### I.5 Measured regularities — [VERIFIED, bounded scope]
- Census-uniformity law: 1171/1171.
- Twist character constant: 1560/1560.
- Character grading skew: ~9 sigma, real, correctly graded EMPIRICAL (not promoted).
- k=3 phase channel: EMPIRICAL, survives a found-and-fixed sorted-index method bug; correctly NOT promoted after its multiplicativity-null showed degenerate; reads "NOT CM."
- GLV orbit readout at puzzles 135 and 140: exact arithmetic, CONFIRMED.

### I.6 Semaev v4 H2 x-closure — [VERIFIED; LABEL OVERREACH]
`R2 ~= 1.6, p = 0.0011`, reproducible, real. But the label "novel CM x-closure effect" is not earned: the control compared 3k independent elements against k beta-orbits, so R2 > 1 may be generic order-3 orbit-closure, not beta/CM specificity. Correct control (beta-orbits vs random order-3 orbits) is OWED. Correct statement: "structured (beta-closed) V raises quo vs unstructured V; beta/CM specificity NOT isolated." (AUDIT_semaev_v4_method_result_conclusion_v1.)

### I.7 Scoped nulls that hold with margin — [VERIFIED NULLS]
Re-tested with added power:
- cubic-e(dG) vs chi_2(d): 0/8 curves survive at n ~6000, pair-matched permutation p, MI ~0.0000.
- mu-6 block incidence: chi-squared 0.837 vs critical 3.84.
- fill-in: graded 940 vs random 1008 sits at the 30th percentile of the proper null.
- d_LF Delta = 0: consistent, scoped.

### I.8 Semaev v3 "+0.21 CM relation yield" is an artifact — [REFUTED, ROBUSTLY]
Three independent tests: class-stratified means all within [-0.06, +0.04]; class 0 null (mean +0.029, n=4); decisive B=1 isolation gives T1 = -0.014 (n=5, perm_p = 0.68). Mechanism identified: v3's un-bracketed nearest match was one-sided, and with quo proportional to 1/#E, a one-sided gap manufactures a positive T1. The +0.21 was #E-leakage. Caveat kept: effects below 0.092 log-units are NOT excluded by power.

---

## Part II: Claims v12 (and its summaries) Overstated — Corrections Applied

### II.1 The 120-degree law
- **What was claimed:** [PROVED -- exact] (summary); "secp-specific signature."
- **What the audits established:** at j=0 the law is verified; at generic j ONLY the e_2 relation was measured — e_3 and e_4 were inferred assuming purity, and purity was never tested at generic j. The correct statement is: **the e_2 relation is not j=0-specific.** That is much weaker than "the 120-degree law holds generically."
- **Sepc-specificity: RETRACTED.** The law does not discriminate secp256k1. But note the over-correction trap: "gone as a lead" (D-2) was itself retracted — the law remains TRUE of secp; what died is only "the law is evidence of special mu-3/CM structure in secp."
- **New structure that survives (from D-5):** the corrected general law `e_2 = e_1^2 - chi_2(-1)*p` and the exhibited factorization `D(T) = T^2 + zeta_3*e_1*T + chi_2(-1)*p*zeta_3^2` are genuinely new. "Zero new structure" was false.

### II.2 A_new supersingular at secp — [CONFLICTED, see Part IV]
Summary says "proved scale-free via Cartier, valid at 2^256." v9 says "verified 24/24 at small p, NOT proved for dimension 2; extrapolation to 2^256 is an assumption," with 2 citation caveats, 2 owed citations, and an owed sign-flip on the Cartier derivation. The firmer version must not be used until this is resolved.

### II.3 "No keyspace reduction from the public readout" — [CORRECTED: TOO STRONG]
This dismissal was argued, never tested. The actual test: the readout carries full determined information (MI = 1.585 bits), but no cheap arithmetic function of d predicts e(dG) (max MI 0.033 bits across 8 predictors). So: cheap-invertibility fails; the **joint readout question (e + s + parity + interval vs d) is OPEN and untested.** The original closure was narrative, not empirical. (AUDIT_session_conclusions_v1, item #4.)

### II.4 Mechanism claims around the cap
- "M1 supported" — decidable false (I.3).
- D_beta non-square as discriminating evidence — it is the GENERIC outcome (5 of 6 tested n), discriminating nothing; no matched null was run; and it is orthogonal to the cap ("F1 does not constrain the cap").
- The 73.9% firing-control baseline was the unmatched ensemble; the matched figure is 36.9%.

### II.5 lambda-3 eigenvector mu-3-covariance — [DISPUTED]
"60–85% mu-3-covariant, broadband" was retracted TWICE in ADD1 as a gauge artifact ("not a property of a well-defined object"), then re-asserted in v9 as "real, broadband, OPEN" with no new evidence. Until re-derived, this stays DISPUTED, and the double retraction is the controlling record.

### II.6 Internal grade contradictions inside v12's own structure
- N1 / half-saturation: heading "RESOLVED," body "structural," ledger "Open on uniformity" (frontier #26), v9 text "no explanation is offered." Three grades for one object. Controlling grade: OPEN.
- Compendium v2 section 0 asserted "complete necessity — no congruence can do it" while every supporting row was [VERIFIED -- bounded] and its own section 4 admitted a class of bridges "would read as absent — wrongly." Textbook synthesis-outruns-rows.

---

## Part III: Buried and Dropped — What the Consolidation Seams Lost

The false "reconciled" certificate hid the following. These are recovered HERE as audit-referenced items needing restoration or testing in v14:

- **E3 cubic difference-set on the real 82 keys:** pre-registered reject at the 98.4th percentile, p ~0.033, verified not a null-estimation artifact, interpretation open — then buried back to a stale "at the floor" null at the v9 seam. Audit language: "precisely the kind of positive the suppression bias would hide… owed a test — not a re-deflation."
- **N1/half-saturation mechanistic account** (relative rigidity, eigenvalue budget): delivered in ADD1 and ADD2, reverted in v9 to "no explanation is offered."
- **Dropped live threads from ADD2:** d-side thread; LBE battery; twist-orbit forced landscape; sub-Weil reduction; W_N analytical lock; two deficit-channel exclusions; full-scale-at-secp scoped nulls.
- **ADD3 in its entirety:** 4 frontiers + 1 method-note, 0 items survived consolidation.
- **Retraction losses:** 13 retractions (7 from ADD1, 6 from ADD2) were dropped from the master — meaning killed claims lost their kill-records and could be (and in one documented case were) re-asserted.
- **The priority frontier itself:** the Eisenstein-lift-norm route ("a candidate public route to epsilon, UNTESTED," Part XVI.D in v9) is absent from the summary a new session reads first.

---

## Part IV: Conflicts That Must Be Resolved Before Any Downstream Use

1. **A_new at secp:** summary "PROVED (Cartier, scale-free, valid at 2^256)" vs v9 "verified 24/24 small p, not proved at dimension 2." P13's [PROVED] grade depends on this and carries 2 caveats in the summary vs 0 in v9. Resolution required: read the Cartier derivation, the citation caveats, and the owed sign-flip.
2. **lambda-3 eigenvector:** double retraction vs v9 re-assertion.
3. **N1 half-saturation:** three coexisting grades in one document.
4. **P13:** [PROVED] (v9) vs [PROVED — conditional, 2 caveats] (summary) — likely same underlying A_new dependency as (1).

---

## Part V: Open Frontiers — the Do-Not-Close List

Explicitly OPEN per the audits. None of these may be closed by argument, mood, or session-summary convenience:

1. **Joint readout:** do e + s + parity + interval jointly constrain d? Untested. The load-bearing open cryptographic question.
2. **Eisenstein-lift-norm route to epsilon:** priority frontier, UNTESTED.
3. **E3 cubic difference-set:** owed a proper test (pre-registered signal at p ~0.033 exists).
4. **Cap mechanism:** M3/monodromy gives distribution, not ceiling; no proof path verified.
5. **Semaev H2 control:** beta-orbits vs random order-3 orbits — the test that would earn or kill the "CM" label.
6. **Semaev power floor:** residual effects below 0.092 log-units not excluded.
7. **Purity at generic j:** assumed, never tested — the missing premise under the 120-degree-law generalization.
8. **All Part III dropped threads** (d-side, LBE, twist-orbit landscape, sub-Weil, W_N lock, deficit-channel exclusions, ADD3 items): status unknown until read from source.
9. **Five genuinely open items flagged by AUDIT_session_conclusions** beyond the above, including the "once these connect" thesis.

---

## Part VI: The Closure-Pattern Catalog (editorial law for every future version)

Six distortion mechanisms, documented in this project's own audits. Every future master must be checked against them:

1. **Staleness** — a summary frozen behind the graded results it summarizes, with no signal of its age. Rule: every summary states which master version and which addenda it actually consumed.
2. **Synthesis-outruns-rows** — headings/assertions stronger than the graded rows beneath them. Rule: no sentence may be firmer than the weakest row it summarizes.
3. **False completeness certification** — claiming reconciliation that never happened. Rule: a completeness claim must cite, by name, every source folded in; anything else is a gap list, not a certificate.
4. **Deflation overreach** — scoped nulls enlarged into global verdicts ("deflationary for the leak hunt" had no object, class, power, or scope). Rule: every negative verdict names its object and power.
5. **Self-cert words** — "honestly" fired in exactly the places the claims could not be shown. Rule: the word is a tripwire; audit whatever sentence contains it.
6. **Auditor false-negatives** — reviewers can manufacture defects (the 0.93 shadow near-miss). Rule: reproduce the exact stated metric before flagging a claim.

Plus one asymmetry to remember: the audits found the dominant distortion was NOT nulls-inflated-to-closures but **staleness, omission, and negative bias** — positives buried, retraction-records dropped, mechanisms refuted and then re-narrated as "supported."

---

## Part VII: v14 Requirements — Full Corpus Revision

Before any new findings work, v14 must:

1. Read v12 lines 1–1600 (N1–N11, Parts I–X) from source.
2. Read ADD1, ADD2, ADD3 in full; restore or explicitly re-kill every item the audits tallied as dropped.
3. Read DEGRADATION_AUDIT_H3_TO_MASTER_v1 and merge its loss inventory.
4. Read COUNTERPRIOR_and_closure_grade_spec_v1 and re-certify every grade in this document against the formal definitions.
5. Read all 9 CORRECTION files; verify each correction is applied to the finding it targets.
6. Read all CONFIRMED files.
7. Diff v9 vs v12 (findings ledgers) to catch losses in the v10–v12 progression, which no audit has yet examined.
8. Resolve the four Part IV conflicts from source.
9. Re-grade everything in this document; v13 grades are provisional.

---

## Version History

| Version | Date | Notes |
|---|---|---|
| v13 | 2026-08-21 | Audit-corrected ledger from v12; explicit gap table; closure-pattern law; v14 corpus-revision mandate. Provisional grades throughout. |
| v12 | 2026-08-18 | Baseline audited here. Carried the false reconciliation certificate; dropped the addenda layer. |
| v9 | 2026-08-11 | Last pre-consolidation-seam master per the audits; source for several v12 grades; not re-read here. |
