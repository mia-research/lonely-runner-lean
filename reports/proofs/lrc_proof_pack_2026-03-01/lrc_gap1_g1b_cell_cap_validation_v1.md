# G1.B Cellwise Cap Validation (Support Artifact)
**Date:** 2026-03-03

## Target inequality checked

For fixed-signature cells `C` on canonical bands (`I_lo`, `I_hi`):

`C_bad(C) <= |C|/n + 2L0`.

This is the bound inserted as Lemma G1.B in canonical `v11` §17.7.

## Data windows checked

1. Certified one-divisible checksets:
   - `lrc_case2_d3_batch_checks_n7n11_v2.csv`
   - `lrc_case2_d3_batch_checks_n8n9n10_v1.csv`
   - total checks processed: `5514`

2. Boundary-certified one-divisible checksets:
   - `lrc_case2_d3_batch_checks_n13_boundary_v1.csv`
   - `lrc_case2_d3_batch_checks_n17_boundary_v1.csv`
   - `lrc_case2_d3_batch_checks_n19_boundary_v1.csv`
   - total checks processed: `34432`

## Result

- Violations: `0` (all tested fixed-signature cells in canonical bands passed).

## Scope note

This artifact is a consistency backcheck for the inserted analytic bound. It is **not** used as a
proof dependency; theorem status remains controlled by the formal text in `v11`.
