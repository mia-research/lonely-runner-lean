> **⛔ FROZEN — NOT CURRENT.** This file is a historical snapshot. The single current-state
> document is **`CLAIMS.md`**. Do not read status, grades, or open items from here; do not
> write a successor version of this file. (Frozen 2026-09-01.)

# POSITIVE FINDINGS MASTER — v15 (delta successor to v14: H-5 resolved, H2 resolved, N16 folded, N7-monodromy gated)

**Date:** 2026-08-24
**Author:** ZCode (executing the supervisor intersection-menu triage
`ANALYSIS_supervisor_intersection_menu_triage_v1.md`).
**Predecessor:** `POSITIVE_FINDINGS_MASTER_v14.md`.
**What v15 is.** A **delta successor**, not a rewrite. **All of v14 is carried forward verbatim by
reference; anything not updated below is unchanged** (compile rule, Editorial Law 6). v15 folds five
same-session artifacts and updates only the rows / do-not-close items they touch, each with a named
artifact in the same edit (grade-up rule). No v14 open item, retraction, or caveat is deleted.

**The five folds, up front:**
1. **H-5 RESOLVED — the Semaev relation-yield lever (M25/H1) is a cofactor/sampling artifact**, not
   the #E-leak the audit named. Two owed arms of do-not-close #5 both delivered.
2. **H2 RESOLVED (CM-affirming) — the x-closure lever (M26) IS β/CM-specific**, mechanism = GLV
   relation-triples. do-not-close #4 discharged.
3. **N16 folded — both clauses were discharged 2026-08-18** (v14 listed owed work three days done).
4. **N7-monodromy gate (Move 2) — P32's monodromy is NOT the a-family monodromy #28**; the proposed
   character-table→N7 prediction is a category error. #28 stays open, its object now stated precisely.
5. **Standing-asymmetry note.** This session produced one upward recovery (H2 real) AND one downward
   correction (H1 artifact — my own earlier "rehabilitates" lean superseded). Both directions audited
   (Editorial Law 7 holds).

---

## Part 0 — Sources consumed this pass (added to v14 §0.1)

| # | File | Extent |
|---|---|---|
| A | `NOTE_v14_item9_n16_state_v1.md` + `RESULT_n16_eps_object_identity_crosscheck_v1`, `RESULT_eis_carry_2d_dlp_reduction_v1`, `REVIEW_eis_carry_framing_suppression_v1` (the three 2026-08-18 files v14 §0.1 missed), `RESULT_t2c_range_carry_skew_exact_v1` | full/at grade |
| B | `RESULT_semaev_cm_relation_yield_v4.md` + `.log` (leaky headline run) + `..._v4_results.jsonl` (corrected rebuild) + `AUDIT_semaev_v4…` | full |
| C | `RESULT_26_PROVED_weil_restriction_v1.md`, `RESULT_subrayleigh_deficit_scaling_v1.md` | full |
| D | `semaev_elimination_v1.py` (`measure_system`, `mu3_lever_test`) | code |
| — | **produced this session:** `RESULT_h5_V_signature_leak_derivation_v1`, `RESULT_h5_cofactor_artifact_v1`, `RESULT_h2_order3_cm_specific_v1`, `ANALYSIS_move2_monodromy_n7_gate_v1`, `PREREG_h5_factor_isolation_and_orbit_quo_v1`, `PREREG_h2_order3_structure_control_v1` | — |

---

## Part I — Row updates (each with its artifact)

### M25 / N22 — H1 relation-yield lever: DISPUTED → **[null — cofactor/sampling artifact, mechanism identified, model scale]**
*Artifacts: `RESULT_h5_V_signature_leak_derivation_v1.md`, `RESULT_h5_cofactor_artifact_v1.md`
(powered, pre-registered under `PREREG_h5_factor_isolation_and_orbit_quo_v1.md`).*

The v14 H-5 seam (§IX.H-5: the final v4 RESULT's T1_j0 = 0.207→0.834 vs the same-day audit's null)
is **resolved.** Two independent, plant-checked results on the frozen f92cb4bb schedule:
- **The #E-leak (the audit's stated mechanism) is refuted.** On the leaky run, T1_j0(p) is
  uncorrelated with the frozen #Egap (Pearson ≤0.06 at all |V|), the #E-gap channel explains 1.8% of
  the |V|-growth, and the lever exceeds the β=−1 #E-leak ceiling by 8.5–34×. E_F2a (matching) ≈ 0 and
  E_F2b (prime-drop, free arm) is negative — both #E arms null.
- **The actual mechanism is a cofactor / subgroup-confinement artifact.** j0 (A=0,B=1) is non-cyclic
  at 24/24 model primes; `gens()[0]` confines the factor base to the index-n₂ subgroup, inflating
  quo. **Pearson(T1_j0, log n₂) = 0.962**; the only two negative-T1 primes are exactly the two with a
  non-cyclic control; under whole-group (`random_point`) sampling the lever vanishes (T1_underF8 =
  0.011/−0.006/−0.024, null; plant fires). Orbit-reduction (Exp-2) shows the excess is distinct
  relations, but subgroup-confined.
- **Cryptographic reading:** yield ∝ |V|^m·n₂/#E — a cofactor effect; secp256k1 has prime order
  (n₂=1), so **the mechanism is absent at the target** (consistent with N15, now mechanism-level).
- **Reconciliation:** the audit's *null was right*, its *mechanism wrong* (F8/sampling, not
  F2/#E-bracket). My own earlier RESULT-v1 "rehabilitates H1 / μ₆-multiplicity" lean is **superseded
  downward** by the powered test — a tested null with a firing plant and an r=0.96 mechanism.

### M26 — x-closure lever: **UPGRADED → [VERIFIED — matched control; CM-specific; mechanism = GLV relation-triples]**
*Artifact: `RESULT_h2_order3_cm_specific_v1.md` (pre-registered under
`PREREG_h2_order3_structure_control_v1.md`).*

The audit's "over-labeled as CM" concern is resolved **in M26's favor.** β-orbits beat generic split
order-3 Möbius orbits at the permutation-null floor (perm_p=0.001, both |V|=9,12 arms; β wins 70% of
1080 comparisons), plants fired (P-a exact 36/36; P-b rising 6/6), tie-guard passed. Mechanism named
and confirmed (quo tracks n_rel; generic orbits that accidentally form relation-triples also boost
quo): each β-orbit `{x,βx,β²x}={x(P),x(λP),x(λ²P)}` satisfies `P+λP+λ²P=O` — the **GLV endomorphism
relation.** This is the known `√(#Aut)` automorphism structure (GLV; Wiener–Zuccherato): a
**constant-factor** effect, present at secp, **not a keyspace reduction.**

### N16 (+ do-not-close #9) — **DISCHARGED** (v14 listed work three days done)
*Artifact: `NOTE_v14_item9_n16_state_v1.md` and the three 2026-08-18 files.*
- `|u−v|≤½ == build.eps`: **DISCHARGED** — 200,000/200,000 identical + both real keys, re-verified
  first-hand; `[VERIFIED — exact]`.
- `eps == ε_LBE`: **PLACED as a conditional negative** — ε_LBE is the overflow bit of the GLV halves
  `(a,b)`, 2-D-DLP-gated; no public per-point map equals it; generic-`d` `[PROVED — reduction]`,
  range-scoped open. Live continuation = the T2c exact range→carry skew law
  (`RESULT_t2c_range_carry_skew_exact_v1`).

---

## Part II — Do-Not-Close list updates (v14 §VI)

- **#2 (a-family monodromy #28) — SHARPENED, still OPEN.** *Artifact:
  `ANALYSIS_move2_monodromy_n7_gate_v1.md`.* P32's Klein-four×ℤ/3 is the **within-fiber** descent
  group forcing the `e₂(a)=e₁(a)²−εp` rigidity per a (P32 §8: "says nothing about any statistic
  outside the V₁/V₂ collapse"). N7 needs the **horizontal** monodromy: the geometric monodromy of the
  family `{E₁,a}/F_{p³}` (equivalently the distribution of `c₃(a)`). Different object. The supervisor's
  character-table→N7 prediction is a **category error**; its "collapses into #6 (purity)" claim also
  fails (purity bounds within-fiber eigenvalue sizes, not the family distribution). #28 remains open;
  the correct next probe is a pre-registered discrete-vs-Sato–Tate test of `c₃(a)` with a
  granularity-matched null — a distinct investigation, not the advertised "symbolic afternoon."
- **#4 (Semaev H2 control) — DISCHARGED** (CM-affirming; see M26 above).
- **#5 (Semaev H-5 resolution) — DISCHARGED.** Both offered arms delivered: the |V|-signature
  derivation (leak refuted) and the mechanism (cofactor artifact). See M25/N22 above.
- **#9 (N16) — DISCHARGED** (see N16 above).
- **#1, #3, #6, #7, #8, #10–#16 — carried forward from v14 unchanged.** (Note #6/#7: the cap /
  purity items are untouched by this session — N31 still owes its citation; H2/H-5 do not bear on it.)

---

## Part III — Everything else

All v14 Parts (I ledger P1–P32 / M1–M40 / N1–N31 except the rows above, II corrections, III addendum
reconciliation, IV conflicts, V post-v12 states, VII loss inventory, VIII Editorial Law, IX
certification table except the H-5 rows now resolved) are **carried forward verbatim.** The v14 scale
banner and all conditional grades govern every quotation. No ECDLP, key-recovery, or 256-bit claim is
made anywhere; the two model-scale results (H-5 artifact, H2 GLV constant-factor) both explicitly do
not transfer to the cryptographic prime.

## Version History (appended to v14's)

| Version | Date | Notes |
|---|---|---|
| v15 | 2026-08-24 | Delta successor: H-5 resolved (M25/N22 → cofactor/sampling artifact; #E-leak refuted; do-not-close #5 discharged, both arms); H2 resolved (M26 upgraded → CM-specific, GLV relation-triples; do-not-close #4 discharged); N16 folded (do-not-close #9 discharged); N7-monodromy gate (do-not-close #2 sharpened, category error named, #28 object stated). Two pre-registrations + four powered/analytical results, all plant-checked. |
| v14 | 2026-08-21 | Full corpus revision + results-level certification (P32, H-5 seam opened). |
