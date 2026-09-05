# Metric Definitions: CLAIM-LRC-000056

- `phi_match_rate(F)`: proportion of rows in family F with `phi_match=YES`.
- `phase_eq_rate(F)`: proportion of rows in family F where `unique_phases == phi_n`.
- `isolation_rate(F)`: proportion of rows in family F with `isolation_count > 0`.
- `avg_isolation(F)`: mean of `isolation_count` over all rows in family F.
- `avg_boundary(F)`: mean of `boundary_count` over all rows in family F.
- `boundary_count`: number of LRC boundary events detected per row; used for
  structural comparison across families.
- `isolation_count`: number of isolated phase events per row; non-zero only in
  arithmetic family in this corpus.
- `unique_phases`: count of distinct detected phases per row; compared against
  `phi_n` (Euler's totient of `n`) as the phase-saturation test.
- `phi_n`: Euler's totient φ(n); serves as the theoretical phase-count reference.
- `runtime_ms`: measured run time per row; used for descriptive context only.
- `first_isolation`: the first isolation point value per row; included for context,
  not directly tested in this claim's falsification rule.
