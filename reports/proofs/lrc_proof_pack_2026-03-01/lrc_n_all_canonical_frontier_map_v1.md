# LRC `n=all` Canonical Frontier Map (v1)
**Date:** 2026-03-07  
**Purpose:** one authoritative synthesis map of theorem-grade, scoped, certified, and heuristic results for the current `n=all` program.  
**Authority rule:** the proof pack is canonical; registry rows are provenance and tracker support only.

## 1) Canon rule
Use exactly these status labels in synthesis work:
- `PROVED`
- `PROVED-UNDER-H`
- `CERTIFIED-FINITE-WINDOW`
- `HEURISTIC`
- `OPEN`
- `OPEN-PROGRESS`
- `OPEN-TARGET`
- `CONDITIONAL`
- `DISPROVED/RETIRED`
- `SUPERSEDED`

Hard rule:
- strong certification may promote conjecture choice,
- but only theorem statements with explicit scope locks count as closure.

## 2) Canonical closed core

| Item | Status | Scope note | Primary source |
|---|---|---|---|
| Irrational branch | `PROVED` | full-rank and partial-rank equidistribution branch | `lrc_irrational_branch_sketch_v1.md` |
| Case 1 (`no e \equiv 0 mod n`) | `PROVED` | rational non-divisible branch | `lrc_ap_grid_extremizer_theorem_sequence_v11.md §4` |
| Lemma P / AP exact model | `PROVED` | baseline exact safe-point structure | `lrc_ap_grid_extremizer_theorem_sequence_v11.md §3` |
| Case-2 `L=n` | `PROVED` | canonical minimum branch | `lrc_case2_partial_analytic_v1.md` |
| Case-2 `L=2n` | `PROVED` | second-smallest branch | `lrc_case2_partial_analytic_v1.md` |
| TM1/TM2/TM3 | `PROVED` | mechanism chain | `lrc_ap_grid_extremizer_theorem_sequence_v11.md §14` |
| TCP schema | `PROVED` | asymptotic-plus-finite bridge | `lrc_ap_grid_extremizer_theorem_sequence_v11.md §16.13` |
| Lower/top-band safety | `PROVED` | all `n`, all Case-2 | `lrc_case2_6theorem_framework_v2.md` |
| Gap-1 prime one-div near-complete closure | `PROVED` | explicit `§17.20` scope only | `section_1720_final.docx` and `v11 §17.20` |
| F1246689 exact CRT promotion | `PROVED` | family-specific hard case | `lrc_case2_6theorem_framework_v2.md §T4.F` |
| G4-LAMBDA-CASEB unit-dropped Case-iiib | `PROVED-UNDER-H` | locked one-div near-complete unit-dropped scope | `lrc_dropped_runner_witness_v1.md §11` |
| n=4 complementarity bound | `PROVED` | exact closure at `n=4` only | `lrc_gap4_s3_complementarity_proof_v1.md` |

## 3) Canonical scoped / partial frontier

| Item | Status | What is actually closed | Primary source |
|---|---|---|---|
| `G4.A` transition Lipschitz bound | `PROVED-UNDER-H` | theorem-grade within declared Gap-4 scope lock | `lrc_gap4_complementarity_theorem_track_v1.md` |
| `G4B-NONUNIT-Z0` pure-exit existential core | `PROVED-UNDER-H` | interior `nu_only_pos` exits with leave-based witness | `lrc_g4b_nonunit_z0_lemma_v1.md` |
| `G4-LAMBDA-CASEA` | `PROVED-UNDER-H` | Case-A under H1-H7 scope lock | `lrc_gap4_scope_lock_audit_v1.md` |
| GAP-2 prime regular `k` | `PROVED` | prime `n`, regular divisible classes only | `lrc_gap2_multidiv_analysis_v1.md` |
| E1 unit sole-cover witness | `PROVED-UNDER-H` | `Siiib-U` only | `lrc_essentiality_program_v1.md` |
| E3 verified width lower bound | `OPEN-PROGRESS` | script-verified only for `E_div={n,2n}` scope | `lrc_essentiality_program_v1.md §7` |

## 4) Certification layer

| Evidence family | Status | Use in synthesis |
|---|---|---|
| D3 one-divisible exact checks through boundary packs | `CERTIFIED-FINITE-WINDOW` | support for prime one-div branches outside theorem text |
| Multi-divisible `n=13` packs | `CERTIFIED-FINITE-WINDOW` | support for asymptotic multidiv conjectures |
| Gap-2 composite B2 delayed-Miss scans | `CERTIFIED-FINITE-WINDOW` | support only until analytic relay proof exists |
| S3 complementarity 87,818-tuple pack | `CERTIFIED-FINITE-WINDOW` | strong structural signal, not closure |
| NZ0 denominator cert (`243/243`) | `CERTIFIED-FINITE-WINDOW` | strengthens pure-exit theorem alignment |

## 5) Disproved / retired / superseded

| Item | Status | Reason |
|---|---|---|
| Anchor-only Gap-1 shortcut | `DISPROVED/RETIRED` | explicit counterexample route exists |
| `C2-main(C)` old occupancy route | `DISPROVED/RETIRED` | explicit counterexample/autopsy in pack |
| Old `Enter_e` NZ0 framing | `SUPERSEDED` | replaced by leave-based event object |
| `G1.H` pre-final occupancy target | `SUPERSEDED` | Gap-1 closed by later theorem chain |

## 6) Load-bearing open frontier only
After canon compression, the live blockers are:

| Branch | Canonical status | Immediate blocker | Why load-bearing |
|---|---|---|---|
| `G4B-COMP-CAP` | `OPEN-PROGRESS` | branch integration from local exit theorems to component cap | blocks composite `S3` route |
| `MULTI-DIV` asymptotic closure | `OPEN` | full-family affine/global binding beyond certified slices | blocks `|E_div|>=2` theorem-grade closure |
| `COMPOSITE-N` general non-unit regime | `OPEN` | template-free non-unit geometry beyond scoped lemmas | blocks general composite extension |
| `S3-GENERAL` | `OPEN-PROGRESS` | global structural inequality or substitute master theorem | universal rational closure target |
| `S3-PRIME-CAND` Xi residual / outside-band mass | `OPEN` | period-summed outside-band safe-mass theorem | remaining prime one-div hard residual |

## 7) Canonical compression result
For synthesis purposes, the open frontier should be treated as exactly four branches:
1. `G4B-COMP-CAP`
2. `MULTI-DIV`
3. `COMPOSITE-N`
4. `S3-GENERAL`

`S3-PRIME-CAND` is not an independent fifth branch; it is the prime one-div manifestation of the `S3-GENERAL` occupancy / outside-band problem.

Likewise:
- `G4B-NONUNIT-Z0` is no longer a frontier branch; it is a sub-lemma inside `G4B-COMP-CAP`.
- `E2-E4` are not separate top-level blockers; they are bridge programs for the composite non-unit branch.

## 8) Review consequence
Any new proof attempt or memo should first declare:
1. which of the four frontier branches it targets,
2. whether it changes the canonical status of that branch,
3. whether it is theorem-grade or only certification support.
