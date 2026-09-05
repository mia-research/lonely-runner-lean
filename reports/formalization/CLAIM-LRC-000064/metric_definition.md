# Metric Definitions: CLAIM-LRC-000064

- `n`: integer parameter of the LRC construction; values tested: {4, 5, 6}.
- `configs`: number of configurations tested per n value (50 for all n here).
- `success_rate(n)`: proportion of 50 configurations where the LRC detector
  succeeds; 1.0 = all 50 configurations succeeded.
- `median_first_time(n)`: median first-detection time across 50 configurations
  for the given n; lower values indicate faster detection.
- `median_boundary_count(n)`: median number of LRC boundary events across 50
  configurations for the given n; reflects structural complexity of the
  detection process for this n.
- Note: no IQR or per-configuration variance data is present in this summary,
  unlike the by-family summary (CLAIM-LRC-000058). Within-n variance is
  therefore unquantified from this source alone.
