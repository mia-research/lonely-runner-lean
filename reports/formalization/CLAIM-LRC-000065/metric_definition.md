# Metric Definitions: CLAIM-LRC-000065

- `n_words`: total random words generated (400,000); determines corpus size.
- `triplets`: consecutive word triplets formed (n_words − 2 = 399,998).
- `plane_onrate_baseline`: maximum fractional occupancy of any single bin in the
  3D planar projection of triplets; for uniform PRNGs expected ≈ 1/n_words.
  Value 2.5000125000625003e-06 ≈ 1/400,000 = 2.5e-06 (deviation ~5e-11).
- `boundary_fragility_epsilon`: smallest epsilon at which the LRC boundary method
  detects fragility in this run; 0.0 means no fragility detected at epsilon=0.
  Does NOT imply fragility_eps_star = inf without a full epsilon sweep.
- `torus_boundary_hits`: count of torus boundary crossing events detected in this
  single run; hit rate = torus_boundary_hits / triplets ≈ 0.1298.
- `gen_time_s`: wall-clock generation time in seconds for n_words=400,000;
  hardware-dependent, not a universal performance bound.
- Derived: throughput ≈ n_words / gen_time_s ≈ 2.385 × 10^8 words/second
  (hardware-specific).
