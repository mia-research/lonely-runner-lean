# G1.D Affine Extraction Validation (Support Artifact)
**Date:** 2026-03-03

## Target bound checked

Using canonical G1.D constants:

- `delta_F = 1/e_max - 1/n`
- `a_F = 2L0((n-1)/n)delta_F`
- `K_F^* = 2L0(2+4S_F)`, `S_F = sum_{e in E_fixed}(e+1)`
- `b_F = -3((n-1)/n) - K_F^*`

check

`B_safe >= a_F*M + b_F`.

(Here `B_safe` is from check artifacts; since this is total `B_safe` on `B_div`, it is an upper
envelope for `B_safe(I_tot)` and is suitable as a consistency backcheck.)

## Windows checked

- `lrc_case2_d3_batch_checks_n7n11_v2.csv`
- `lrc_case2_d3_batch_checks_n8n9n10_v1.csv`
- `lrc_case2_d3_batch_checks_n13_boundary_v1.csv`
- `lrc_case2_d3_batch_checks_n17_boundary_v1.csv`
- `lrc_case2_d3_batch_checks_n19_boundary_v1.csv`

Total rows checked: `39946`.

## Results

- Violations: `0`.
- Worst (smallest) margin `B_safe - (a_F*M+b_F)`: `33183/8 = 4147.875`.

## Scope note

This note is a consistency check for inserted G1.D formulas; it is support evidence only,
not a proof dependency.
