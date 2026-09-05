# Assumptions: CLAIM-LRC-000065

1. Source integrity verified by SHA-256
   `eee26d22c03b41977311020edd904d061e72a5a2a8d9127e111e480fc37053aa`.
2. This is a single-run measurement; no replicate runs are present. All 6 values
   reflect one execution; run-to-run variance is unquantified.
3. boundary_fragility_epsilon = 0.0 is interpreted as "no boundary fragility
   detected at epsilon = 0"; it does not constitute a sweep across epsilon values
   and does not assert fragility_eps_star = inf (which would require a full sweep).
4. torus_boundary_hits is a raw count for this run; no per-triplet rate or
   comparison to theoretical expectation is asserted beyond the derived rate in
   the formal claim.
5. gen_time_s reflects wall-clock timing for a single run on unspecified hardware;
   throughput estimate is hardware-dependent and not universally reproducible.
6. plane_onrate_baseline is consistent with uniform distribution at this n, but
   a single sample cannot rule out rare bin concentrations not captured in this run.
7. This characterisation is generator-specific (PCG64) and does not generalise
   to other PRNGs or parameter choices without further testing.
8. Cross-reference: PCG64 was also tested in CLAIM-LRC-000042 (200K triplets);
   the different n_words and epsilon framework make direct comparison non-trivial.
