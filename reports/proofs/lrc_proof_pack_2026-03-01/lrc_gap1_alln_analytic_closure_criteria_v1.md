# Gap 1 All-n Analytic Closure Criteria
**Date:** 2026-03-03

## Purpose

Define what counts as true Gap-1 closure for `n=all`.

## Non-closure (explicit)

The following do **not** by themselves constitute all-`n` theorem closure:

- certifying additional individual `n` values,
- scaling template batch runs,
- larger finite-window evidence.

These are support evidence only.

## Closure criterion (analytic)

Gap 1 is analytically closed only when one of the following is proved in canonical form:

1. Template-free theorem route:
   - a universal structural inequality (S3-level or equivalent) proving the Case-2 one-divisible
     all-distinct branch for all admissible `n` without per-template finite checks.

2. Uniform finite-bridge elimination route:
   - an analytic argument that removes template-by-template dependence in G1.E
     (for example by proving checksets are vacuous or uniformly discharged analytically).

## Current status

- G1.B-G1.K theorem-link chain is complete in prime one-divisible all-distinct scope.
- TM2 obstruction is eliminated in that scope (`O_tm2=empty`, `E_tm2=0`).
- Remaining open part is uniform residual elimination (`Xi_tr=0`) or an equivalent outside-band compensation theorem that discharges `(G1.G.2)` without per-template finite checks.
