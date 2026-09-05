# CLAIM-LRC-000055 Formalized Claim

## Operational Proposition (Empirical, Falsifiable)
In `lrc_validation_large_1759238706040.csv`, for rows satisfying:
- `test_type = arithmetic_varied`
- `family = arithmetic`
- `n = 5`

the following measured properties hold in the extracted slice:
1. Row count in slice: 10000
2. `phi_match = YES` in 10000/10000 rows.
3. `unique_phases = phi_n` in 10000/10000 rows.

This converts the prior CSV-fragment statement into a checkable proposition over a defined row subset.

## Falsification Rule
Reject the claim if any row in the stated subset violates:
- `phi_match == YES`, or
- `unique_phases == phi_n`.
