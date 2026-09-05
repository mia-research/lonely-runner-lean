# Master Problem 1 Checklist (v1)
**Date:** 2026-03-07  
**Master problem:** local exposure / complementarity geometry in the unresolved composite/non-unit rational frontier.  
**Top-level target:** convert event-local exposure theorems into the component cap

`|O cap C| <= |C| - n`

for every `B_div` component `C` in the declared composite Case-2 large-`L` scope.

## 1) Scope
Default synthesis scope `MP1-S0`:
- composite `n >= 6`,
- Case-2 tuple `E` with `|E|=n-1`, `E_div != emptyset`, `gcd(E)=1`,
- `L > 2n`,
- obstruction set `O = {b in B_div : D(b)=0}`,
- component decomposition of `B_div` as used in the Gap-4 theorem track.

Auxiliary bridge scope `MP1-S1`:
- generalized non-unit essentiality program (`Siiib-G` and related composite non-unit branches),
- used only when a local exit theorem needs a delayed witness or width transfer.

## 2) Canonical objective split
Master Problem 1 has two outputs:
1. **G4B branch integration:** theorem-grade closure of the component run-cap route.
2. **Composite non-unit bridge:** package non-unit exposure/essentiality so it can feed the same route template-free.

## 3) Exact subclaims

| ID | One-line target | Current | Dependencies | Primary artifact target |
|---|---|---|---|---|
| MP1.1 | Interior exit has at least one causative leave set | `PROVED` | exit definitions, `D(b_last)=0`, `D(b_exit)>=1` | `lrc_master_problem1_branch_integration_v1.md` |
| MP1.2 | Interior exits partition exactly into `nu_only_pos`, `mixed`, `unit_only` | `PROVED` | MP1.1 + `UnitLeave/NuLeave` definitions | `lrc_master_problem1_branch_integration_v1.md` |
| MP1.3 | Pure non-unit exit existential theorem (`NZ0-Pure-Existential`) is cited in final form | `PROVED-UNDER-H` | leave-based NZ0 note | `lrc_g4b_nonunit_z0_lemma_v1.md` |
| MP1.4 | Mixed / unit-only exits route to the unit branch with no NZ0 debt | `PROVED-UNDER-H` | unit branch theorem references + MP1.2 | `lrc_master_problem1_branch_integration_v1.md`, `lrc_g4b_nonunit_z0_lemma_v1.md`, and `lrc_gap4_complementarity_theorem_track_v1.md` |
| MP1.5 | Boundary-ending runs satisfy `run_len <= |C|-n` | `PROVED-UNDER-H` | lower-band safe-fiber theorem | `lrc_gap4_complementarity_theorem_track_v1.md` |
| MP1.6 | Every maximal obstruction run in `C` ends at a theorem-controlled safe opening | `PROVED-UNDER-H` | MP1.2 + MP1.3 + MP1.4 + MP1.5 | `lrc_master_problem1_branch_integration_v1.md` |
| MP1.7 | Safe-fiber budget theorem: `B_safe(C) >= n` in declared scope | `OPEN-TARGET` | event-path occupancy + theorem-controlled safe openings + boundary safe occupancy | `lrc_master_problem1_safe_fiber_budget_note_v1.md` and `lrc_master_problem1_safe_fiber_budget_sf3_v1.md` |
| MP1.8 | `G4B-Branch-Closure`: `B_safe(C)>=n` implies `|O cap C| <= |C|-n` | `OPEN-TARGET` | MP1.6 + MP1.7 | `lrc_gap4_complementarity_theorem_track_v1.md` or dedicated closure note |
| MP1.9 | Non-unit coset-change exposure is template-free enough for composite global use | `OPEN` | coset essentiality + essentiality bridge (`E2-E4`) | `lrc_g4b_coset_essentiality_v1.md`, `lrc_essentiality_program_v1.md` |

## 4) Dependencies by layer

### Layer A: local event logic
- leave-based exit objects,
- `UnitLeave/NuLeave` definitions,
- existence of a causative leave on any genuine exit.

### Layer B: branch-local exposure
- unit branch theorems,
- pure non-unit existential theorem,
- boundary-ending cap.

### Layer C: component aggregation
- exhaustive exit partition,
- safe-fiber budget in each component,
- final deduction `|O cap C| <= |C|-n`.

### Layer D: template-free composite extension
- non-unit coset essentiality,
- delayed witness existence/width,
- counting transfer from width to safe-mass budget.

## 5) Pass criteria

### Event layer pass
- every interior exit is shown to have a causative leave,
- classes `nu_only_pos`, `mixed`, `unit_only` are disjoint and exhaustive.

### Branch layer pass
- every exit class is covered by an analytic theorem that yields a safe opening,
- no residual exit class remains untreated.

### Aggregation layer pass
- safe-fiber budget is theorem-grade in the declared scope,
- component cap follows with no empirical step.

### Composite extension pass
- non-unit exposure is template-free enough to connect `COMPOSITE-N` to the same closure scheme.

## 6) Artifact targets

| Purpose | Artifact |
|---|---|
| event partition and integration lemmas | `lrc_master_problem1_branch_integration_v1.md` |
| theorem-track target / final closure statement | `lrc_gap4_complementarity_theorem_track_v1.md` |
| non-unit local engine | `lrc_g4b_coset_essentiality_v1.md` |
| non-unit quantitative bridge | `lrc_essentiality_program_v1.md` |
| strict checklist sync | `lrc_proof_checklist_v1.md` |

## 7) Immediate execution order
1. Prove MP1.1 and MP1.2 in a dedicated integration note.
2. Isolate the exact remaining content of MP1.7; do not blur it with branch-partition work.
3. Once MP1.7 is explicit, promote MP1.8 (`G4B-Branch-Closure`).

## 8) Program stance
Master Problem 1 should now be treated as:
- a theorem-writing program with a clear local event layer,
- a clear aggregation layer,
- and one quantitative bridge still open (`B_safe(C) >= n` in full declared scope).

That is narrower than the old “Gap-4 remains open” wording.
