# Metric Definitions: CLAIM-LRC-000042

- `plane_zero_frac`: fraction of planar projection bins with zero occupancy; 0.0
  for all generators in this corpus.
- `plane_max_bin_frac`: maximum single-bin fractional occupancy in the 3D planar
  projection; the primary lattice discriminant in this dataset.
- `lattice_rate_tol0`: lattice detection rate at zero tolerance; 0.0 for all
  generators, confirming no false positives at the strictest threshold.
- `lattice_rate_tol1e3`: lattice detection rate at tolerance 1e-3; non-zero only
  for MT19937 (5e-06) in this corpus.
- `eff_rank_lag3`: effective rank of the lag-3 autocorrelation matrix; 4 for all
  generators, indicating full-rank structure across generators tested.
- `sv_max`: largest singular value of the triplet distribution matrix.
- `sv2`: second singular value; gap (sv_max - sv2) indicates anisotropy.
- `boundary_hits_eps1e-3`: count of LRC boundary hit events at epsilon=1e-3;
  zero for TORUS_rational_1/5, 773–818 for all others.
- `fragility_eps_star`: epsilon value at which structural fragility is first
  detected; inf (sentinel) for all generators in this corpus.
- `fragility_base_rate` / `fragility_end_rate`: fragility rates at base and end
  epsilon; non-zero only for MT19937 (5e-06 each).
- `elapsed_sec`: wall-clock time per generator run; descriptive only.
- `plane_top_bins_preview`: top-5 most occupied bins with counts; illustrates
  extreme concentration for TORUS_rational_1/5 (count ~40,000) vs. near-uniform
  distribution for stochastic generators (count 1–2).
