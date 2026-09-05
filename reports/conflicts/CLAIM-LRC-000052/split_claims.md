# CLAIM-LRC-000052 Split Claims

## 000052-A (Arithmetic Cohort)
For `lrc_validation_data_2025-09-23T11-19-31-619Z.csv` rows with:
- `family=arithmetic`, `test_type=arithmetic_baseline`:
  - rows: 3300
  - `phi_match=YES`: 3300
  - `isolation_count>0`: 3300
  - `first_isolation ≈ 10/n` within tolerance `1e-6`: 3300/3300

For arithmetic extended variant:
- `family=arithmetic`, `test_type=arithmetic_extended`:
  - rows: 1991
  - `phi_match=YES`: 1991
  - `isolation_count>0`: 1991

## 000052-B (Methodology-Boundary Cohort)
For non-arithmetic test slice (`test_type=non_arithmetic`):
- geometric rows: 495 (`phi_match=YES`: 0, `isolation_count>0`: 0)
- quadratic rows: 495 (`phi_match=YES`: 0, `isolation_count>0`: 0)
- perturbed rows: 506 (`phi_match=YES`: 0, `isolation_count>0`: 0)

Interpretation:
- `phi_match` appears arithmetic-specific in this pipeline and should not be used as a universal success metric for non-arithmetic families.
- Non-arithmetic rows require a dedicated criterion before any global negative inference is made.
