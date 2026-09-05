# Assumptions: CLAIM-LRC-000058

1. Source integrity verified by SHA-256
   `e7553c19ce9061048af54fc64ecbabc704e0658a281cfe522cd4d78f1ea84e42`.
2. Each family summary aggregates 30 configurations; underlying per-configuration
   data is not present in this file but is assumed to exist in the source pipeline.
3. `success_rate=1.0` means the detector correctly identified the target for all
   30 configurations; the definition of "success" is inherited from the pipeline
   and is not independently specified in this summary file.
4. `median_first_time` and `median_boundary_count` are medians over 30 configs;
   individual configuration variance is partially captured by q25/q75 but full
   distributions are not available in this summary.
5. This is a per-family summary claim; results do not generalise to families or
   configurations beyond those tested without further validation.
6. Timing values are assumed to share consistent units and measurement conditions
   across families; no cross-family hardware normalisation is stated in the source.
7. The five families (exact_arithmetic, fibonacci_ratios, harmonic_series,
   sqrt_primes, transcendental) are treated as the complete tested set for this corpus.
