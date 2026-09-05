# LRC Open Gaps — Canonical Reset
**Date:** 2026-03-03  
**Source authority:** `lrc_ap_grid_extremizer_theorem_sequence_v11.md`, `section_1720_final.docx`, and `lrc_claim_status_table_v1.csv`

---

## Closed / Certified Scope (canonical)

The following are established and may be cited as closed:

- Lemma P, Lemma E Case-1, irrational branch.
- Case-2 canonical base branches (`L=n`, `L=2n`), degree-bound branch, lower/top-band safety.
- TM1/TM2/TM3 and D.1'/D.2' mechanism chain (analytic).
- TCP as a proof schema (analytic).
- Gap 1 closure in explicit prime one-divisible all-distinct near-complete scope:
  `n` prime, `|E_div|=1` with `E_div={n}`, `|E_fixed|=n-3`, fixed speeds distinct mod `n`.
  Closed by final `§17.20` theorem statement in `section_1720_final.docx` (with explicit `Lambda2>0` proof via `tau=0 in T2` and finite explicit `M0_glob(F)`).
- All-distinct one-divisible template certifications for `n in {7,8,9,10,11}`:
  `145` templates, `5514` exact finite checks, `0` violations.
- Additional one-divisible boundary certifications now in-pack for `n=13,17,19`:
  `339` templates, `34432` exact finite checks, `0` violations (finite-window certification evidence).

Finite-window (support only, not asymptotic closure):
- Multi-divisible boundary/TCP runs at `n=13`, `|E_div| in {2,3}`, widened pool `{1,2,3,4}`:
  - seed batch: `3300` templates, `70263` checks, `0` violations;
  - TCP-affine target checks: `195448`, `0` violations.

---

## Open Items (canonical)

### 1. Gap 2 — Multi-divisible asymptotic closure (`|E_div| >= 2`)

**Statement needed:** full theorem-grade closure across all prime/all-family templates, plus non-prime extension outside unit-speed-compatible scope.

**Current status:** OPEN.

**What is done:**
- Prime-scope local component-band closure and affine `S(F,M)` chain are now formalized (`§17.23`-`§17.26` in `v11`).
- The residual open part is the full-family asymptotic/global binding and the non-unit composite regime.
- Existing finite-window multidiv certification remains strong support only.

---

### 2. Gap 3 — Composite-`n` general Case-2 closure

**Statement needed:** full composite-`n` proof in the general regime including gcd-conflict/invertibility interactions in TM/D.2-style counting.

**Current status:** OPEN.

**What is done:** several composite-safe certified sub-ranges and partial analytic subcases are in pack,
but no canonical general theorem is inserted.

---

### 3. Gap 4 — Universal S3 structural theorem

**Statement needed:** template-free structural inequality implying `|B_safe| >= n-1` (or equivalent)
for full Case-2 scope.

**Current status:** OPEN-PROGRESS (n=4 fully proved; Case-iiib unit-dropped branch now analytically closed via Sole Cover witness; residual n≥6 composite L>2n general scope remains open).

**What is newly done (2026-03-03 to 2026-03-04):**

**Phase-1 (2026-03-03):**
- Composite-n diagnostic: 88,626 tuples (exhaustive n∈{4,5,6,7}, stress n∈{8..12}).
  Zero violations of `B_safe >= n-1`. Zero violations of `B_safe >= n` for `L>n`.
- Biconditional: `B_safe = n-1 ⟺ L = n` (zero violations, 88,626 tuples).
- z=0 bad_a reduction lemma proved: at z_e=0 with gcd(e,n)=1, |bad_a(e,b)| = exactly 1.
- Failed routes documented: good anchors, z=0 universal safety, band coverage, anchor sum.

**Phase-2 (2026-03-04 — Complementarity Bound):**
- Theorem-track memo inserted: `lrc_gap4_complementarity_theorem_track_v1.md` (`G4.A` proved; `G4.B` open target; `G4.C` conditional closure).
- Event-cell diagnostic: 87,818 L>n tuples. Zero CB violations (max_obstr_run ≤ B_div−n). ✓
- Tight cases: only 6, all n=4, E=permutation of {1,3,4}, L=12. ✓
- 95.2% of obstructed runs terminate at z=0 events of some runner.
- H2 failures (max_obstr > min_period−1) for n≥5 show single-runner period bound insufficient for n≥5.
- **n=4 CB proved** via three-step argument:
  1. z=0 safety: for gcd(e,4)=1 runners, z=0 events always safe (|bad_a|=1, union≤3<4).
  2. H2 for n=4: max_obstr_run ≤ L/e_max − 1 (obstruction confined to interior of one period).
  3. Key inequality: L/e_max ≤ B_div−n+1 for L≥12 (e_max≥3 always, and 2L/(L−4)≤3 for L≥12).
- Mixed-gcd cases (gcd=(1,2) or k_non≤1): C_bad=0 directly.
- Tight case unique: only n=4,L=12,e_max=3 satisfies L/e_max = B_div−n+1 as an integer.


**Phase-4 (2026-03-04 — Sole Cover witness):**
- `lrc_dropped_runner_witness_v1.md` now contains a complete Lemma B proof in locked Case-iiib unit-dropped scope (`gcd(a,n)=gcd(b,n)=1`).
- Witness interval: `I_d = (1/n, 1/(n-1))` with `r_d = -d^{-1} mod n` (`d in {a,b}`), giving `I_d subset Miss_{E_fix}(r_d)` and `meas(I_d)=1/(n(n-1))`.
- This closes M2 in that locked scope and yields scoped corollaries for positive slope via M3.
- Remaining Gap-4 blocker is the extension beyond that locked sub-scope (non-unit/general Case-B/global S3).

**Phase-3 (2026-03-04 — Scope-lock re-audit):**
- New canonical audit memo: `lrc_gap4_scope_lock_audit_v1.md`.
- Scope locked for proved core: one-div near-complete (`E_div={n}`, `|E_fix|=n-3`).
- Per-band density chain and affine growth are confirmed under that scope.
- `Lambda_eff>0` split corrected: Case A proved; Case B with `n<=9` proved-under-cited-small-k; Case B with `n>=10` remains open (load-bearing blocker).
- Therefore "only small-M remains" is conditional, not global, until Case-B (`n>=10`) positivity is resolved.

**Open core:** Prove CB for n=6 composite, L>2n. Routes:
- Single-runner period bound: fails for n≥5 (obstruction spans multiple periods).
- z=0 event density argument: z=0 events terminating runs at 95.2%, but analytically
  showing density is sufficient (≥1 safe fiber per B_div−n+1 window) is not yet proved.
- Key structural observation: for n=6, no tight cases exist, B_div−n grows rapidly with L,
  and the tight-case equation has no integer solutions.

**Key files (new):**
- `lrc_gap4_s3_event_path_v1.py` — event-cell diagnostic
- `lrc_gap4_s3_event_path_rows_v1.csv` — 87,818-row event-path data
- `lrc_gap4_s3_event_path_summary_v1.md` — diagnostic summary
- `lrc_gap4_s3_complementarity_proof_v1.md` — CB proof (n=4 complete; n≥6 open core)
- `lrc_gap4_scope_lock_audit_v1.md` — strict scope-lock + corrected conditional status split

**Key files (existing):**
- `lrc_gap4_s3_composite_diag_rows_v1.csv` — 88,626-row Phase-1 data
- `lrc_gap4_s3_composite_proof_v1.md` — Phase-1 analysis and Routes A–D

---

## Current Frontier

The core remaining work is theorem promotion in the multidiv/composite/global branches.
The immediate next load-bearing targets are:
1. Gap 2 all-family asymptotic binding in the multidiv regime.
2. Composite non-unit extension.
3. Universal S3 structural closure.

### 4. Gap 4 housekeeping update (2026-03-05, NZ0 correction)

- ELDC formulation corrected from `Enter_e` to `Leave_e` at run exits.
- Final finite-window certifier v2 (all-candidates, no silent drops) in scope `n in {6,8}` reports:
  - interior exits: `319`
  - `nu_only_pos` exits: `234`
  - denominator: `243` `(exit,e)` candidate pairs
  - pass: `243/243`, fail: `0`
  - `unit_only` exits: `85` (explicitly counted, outside NZ0 denominator)
- Status impact: `G4B-NONUNIT-Z0` is now `PROVED-UNDER-H` in existential pure-exit form (with finite-window strengthening cert).

**Implication:** remaining blocker for theorem-grade promotion is branch integration/aggregation inside `G4.B` (not local witness existence).

