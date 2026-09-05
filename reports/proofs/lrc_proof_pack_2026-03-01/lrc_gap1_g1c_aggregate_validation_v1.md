# G1.C Aggregate Constant Validation (Support Artifact)
**Date:** 2026-03-03

## Target inequalities checked

For canonical bands `I_tot = I_lo union I_hi`:

1. `C_bad(I_tot) <= |I_tot|/n + K_F^*`, where
   `K_F^* = 2L0*(2+4S_F)`, `S_F = sum_{e in E_fixed}(e+1)`.
2. (Tighter runtime form) `C_bad(I_tot) <= |I_tot|/n + 2L0*m_tot`,
   where `m_tot` is the observed number of fixed-signature cells after intersecting with `I_tot`.

## Windows checked

- `lrc_case2_d3_batch_checks_n7n11_v2.csv`
- `lrc_case2_d3_batch_checks_n8n9n10_v1.csv`
- `lrc_case2_d3_batch_checks_n13_boundary_v1.csv`
- `lrc_case2_d3_batch_checks_n17_boundary_v1.csv`
- `lrc_case2_d3_batch_checks_n19_boundary_v1.csv`

Total checks processed: `39946`.

## Results

- Violations against `K_F^*` bound: `0`.
- Violations against tighter `2L0*m_tot` bound: `0`.
- Observed `max(m_tot)` on tested windows: `3`.

## Scope note

This artifact is an implementation-consistency backcheck for inserted Lemma G1.C.
It is support evidence only, not a proof dependency.
