# M2-drop Proof Template v1
Date: 2026-03-04

Use this template for theorem-grade attempts. Keep each subclaim explicit.

## Target
Prove `exists r* in Cover_drop` with `Miss(r*) != empty` in Case-iiib scope.

## Required subclaims

### SC0 (Setup validity)
Show template is in Case-iiib scope:
- composite `n`, near-complete `E_fix={1,...,n-1}\{a,b}`
- `1,n-1 in E_fix`
- `U_fix(tau=0)=Z_n`

Status: ____

### SC1 (Coverage algebra)
Express `Miss(r)=I_div \ union_e Cov_e(r)` with exact `bad_set`/CRT form.
No heuristic window simplification in non-unit regime.

Status: ____

### SC2 (Dropped-support relevance)
Show target can be restricted to `r in Cover_drop`:
`exists r in Z_n with Miss(r)!=empty` => `exists r in Cover_drop with Miss(r)!=empty`.
(Or prove directly in dropped support.)

Status: ____

### SC3 (Existence core)
Prove `exists r in Cover_drop` such that `union_e Cov_e(r)` does not saturate `I_div`.
This is the load-bearing step.

Status: ____

### SC4 (Interiority)
Show witness miss interval is strictly interior (not only endpoint artifact).

Status: ____

### SC5 (Bridge)
Convert miss interval to integer fiber witness via counting bridge (`M3`).

Status: ____

## Pass/fail criteria
- `PROVED` requires SC0..SC5 all proved with no empirical-only step in SC3.
- `PROVED-UNDER-H` allowed only if hypotheses are explicit and isolated.
- If SC3 open, final status must be `OPEN` or `OPEN-PROGRESS`.

## Agent report block (exact)
1. ID: `M2-drop`
2. Status:
3. Scope used:
4. Core derivation (5-10 lines):
5. Dependencies used:
6. Blocker:
7. Artifact path:
