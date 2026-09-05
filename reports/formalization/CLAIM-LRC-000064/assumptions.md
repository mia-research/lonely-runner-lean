# Assumptions: CLAIM-LRC-000064

1. Source integrity verified by SHA-256
   `2ff4420e11f156bcb2ec1feb8994e239589d43e43a85ca5a1cb52577aaaab024`.
2. Each row aggregates 50 configurations for the given n; per-configuration data
   is not present in this summary file.
3. success_rate=1.0 definition inherited from pipeline; independently specifying
   what constitutes "success" requires access to the underlying per-configuration
   data or pipeline documentation.
4. median_first_time and median_boundary_count are medians over 50 configurations;
   no IQR or variance data is available in this summary (unlike CLAIM-LRC-000058).
5. Timing values are assumed to share consistent units and measurement conditions
   across n values; no hardware normalisation is stated.
6. The n range {4, 5, 6} is narrow; monotone trends across only 3 data points
   cannot be extrapolated to larger n without further testing.
7. The dataset is distinct from CLAIM-LRC-000058/000063 (different SHA-256,
   different schema — by n rather than by family, 50 configs vs 30 per group).
8. The inverse relationship between first_time and boundary_count (statement 4)
   is an observational finding within this corpus and does not constitute a
   causal or mechanistic claim.
