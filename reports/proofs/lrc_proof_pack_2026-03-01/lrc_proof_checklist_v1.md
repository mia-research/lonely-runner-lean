# LRC Proof Checklist (Strict) v1
Date: 2026-03-04
Purpose: Uniform pass/fail checklist for parallel theorem-track execution.

Allowed status values: `PROVED`, `PROVED-UNDER-H`, `CONDITIONAL`, `OPEN`, `FAILED`.

## 1. SL-1 / Y-chain (Gap-4 Case-iiib)

| ID | One-line target | Pass criteria | Fail condition | Current |
|---|---|---|---|---|
| Y.2 | `Cov_e(r)` and `Miss(r)` endpoints are rational Farey points | Every endpoint represented as `t/e` with `e<=e_max`; conclude `den<=e_max<=n` | Any endpoint introduced without denominator control | PROVED |
| Y.3 | `exists r*` with `m(r*) >= 1/(e_max(e_max-1))` | Explicit construction or theorem-level lower bound valid for all Case-iiib templates in scope | Uses finite enumeration as proof | OPEN |
| Y.4 | Interior witness `alpha*` induces positive integer `b`-interval | Convert alpha interval `I` to integer count `#{b: b/L in I}>=1` | Witness only at a boundary point | OPEN |
| Y.5 | Case-iiib implies `Lambda_eff>0` | Direct implication from Y.4 into positive slope mass | Hidden empirical dependency | OPEN |

## 2. G4B / Z-chain (Composite cap)

| ID | One-line target | Pass criteria | Fail condition | Current |
|---|---|---|---|---|
| Z.2 | Every obstruction run has z=0 trigger/termination structure | Full event logic for entry/exit with floor transitions | "Observed in data" used as proof | OPEN |
| Z.3 | Successive z=0 events spacing `<=L/n` | Deterministic spacing lemma from floor/residue arithmetic | Average/probabilistic spacing only | OPEN |
| Z.4 | Run cap `|R|<=B_div-n` | Deduced from Z.2+Z.3 and locked hypotheses | Uses removed gcd-lcm cap | OPEN |
| Z.5 | Global `max_run<=B_div-n` | All runs covered by Z.4 | Leaves residual run class untreated | OPEN-TARGET |
| NZ0 | Pure non-unit exit existential leave witness (`NZ0-Pure-Existential`) | Prove: on every interior `nu_only_pos` exit, `exists e in NuLeave` and `exists r in Leave_e(b_exit)\U_{-e}(b_exit)`; plus mixed/unit-only exits routed to unit branch | Any pure non-unit exit lacking existential witness, or mixed exits treated as NZ0 failures | PROVED-UNDER-H |
| G4BI | Branch-integration closure (`G4B-Branch-Closure`) | Boundary cap + exhaustive interior partition + pure non-unit existential theorem + mixed/unit routing + safe-fiber budget imply `max_obstr_run(C)<=|C|-n` on each component | Any missing branch class, unresolved routing dependency, or missing safe-fiber budget theorem in scope | OPEN-TARGET |

## 3. Gap-2 / W-chain (corrected target)

| ID | One-line target | Pass criteria | Fail condition | Current |
|---|---|---|---|---|
| W.2 | Small-L block (`L<=2n`) closes for `x0>=phi(n)` | Explicitly connected to locked small-L theorems | Uses old target `B_safe>=n-1` | PROVED-UNDER-H |
| W.3 | `x0(F,M)=s1(F)M+s0(F)` for active `L>2n` scope | Affine derivation in scope + no empirical fit-only step | Slope inferred only from data | OPEN |
| W.4 | Tail threshold `M0=ceil((phi-s0)/s1)` | Prove `s1>0` then threshold implication | Missing positivity argument for `s1` | OPEN |

## 4. S3-prime / V-chain (interior-period route)

| ID | One-line target | Pass criteria | Fail condition | Current |
|---|---|---|---|---|
| V.2 | Interior period `P_k` frozen-fixed partition for all `k` | Partition construction uniform in k | Proven only for `k=1` | OPEN |
| V.3 | Exact CRT badness criterion per interior period | Uniform identity in k; no approximations | Uses sampled/heuristic CRT | OPEN |
| V.4 | Per-period safe lower bound `S_k` | Explicit lower bound each period with constants exposed | "bulk safe mass" narrative only | OPEN |
| V.5 | Global interior-period sum closes route | `sum_k S_k` + boundary handling yields final inequality | Boundary-local argument reused as global bulk | OPEN |

## 5. Required Agent Report Format

For each attempted ID, report exactly:
1. `ID`
2. `Status`
3. `Scope used`
4. `Core derivation` (5-10 lines max)
5. `Dependencies used`
6. `Blocker` (if not PROVED)
7. `Artifact path`


## 6. Essentiality / E-chain

| ID | One-line target | Pass criteria | Fail condition | Current |
|---|---|---|---|---|
| E1 | Unit dropped runner sole-cover witness in Siiib-U | Explicit arithmetic proof of `I_d subseteq Miss(r_d)` with `r_d=-d^{-1}` and `I_d=(1/n,1/(n-1))` | Empirical-only argument | PROVED-UNDER-H |
| E2 | Non-unit delayed essentiality existence | Prove existence of delayed witness interval for dropped non-unit runner | Uses finite scan as proof | OPEN |
| E3 | Non-unit witness width lower bound | Derive explicit `|I_d|>=c(n,g_d)` theorem | Width bound only heuristic/fit | OPEN |
| E4 | Counting transfer to unresolved global inequalities | M3-based derivation yielding target safe-mass inequality in designated branch | No explicit constants or branch mapping | OPEN |
