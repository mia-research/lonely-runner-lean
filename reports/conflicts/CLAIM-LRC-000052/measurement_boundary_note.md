# CLAIM-LRC-000052 Measurement Boundary Note

## Verified in-file cohorts
- Arithmetic baseline (`arithmetic_baseline`): 3300 rows.
- Arithmetic extended (`arithmetic_extended`): 1991 rows.
- Non-arithmetic detector slice (`non_arithmetic`):
  - geometric=495, quadratic=495, perturbed=506.
- Performance rows (`performance_test::performance`): 500 (tracked separately; not part of the phi-match theorem claim).

## Guardrail
Do not aggregate arithmetic and non-arithmetic cohorts into one binary theorem-style statement.
Treat them as separate claims with separate validity criteria.
