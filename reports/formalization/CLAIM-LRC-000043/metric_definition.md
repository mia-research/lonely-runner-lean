# Metric Definitions: CLAIM-LRC-000043

- `n`: Number of walkers/agents in the LRC construction. Integer in
  {5,7,8,10,11,12,13,15,16,17,19,20,23,25,29,30} for this corpus.

- `phi` (also written φ(n)): Euler's totient of n; the count of integers in [1,n]
  coprime to n. Stored as an integer column.

- `phi_over_n`: The ratio φ(n)/n as stored in the CSV, truncated to 6 decimal places
  for most n values. Exact (rel_err = 0) only when φ(n)/n has a terminating decimal
  representation, i.e., when n's prime factors are a subset of {2, 5}. In this corpus,
  exact for n ∈ {5, 8, 10, 16, 20, 25}; truncated for all others.

- `efficiency`: The ratio `isolation_count / boundary_count` per row. Stored as a
  computed float in the CSV. Represents the fraction of boundary events that produce
  isolation events.

- `isolation_count`: Number of isolation events detected per LRC simulation run.

- `boundary_count`: Total number of boundary crossing events per run.

- `within-n efficiency range`: For a given n, the difference between the maximum and
  minimum `efficiency` values across all 6 seeds. Quantifies seed-invariance of
  arithmetic efficiency.

- `sensitive threshold (1e-6)`: The pipeline's threshold below which numeric differences
  are classified as "below sensitive"; values above trigger `float_risk = medium`.
  Relevant here for phi_over_n precision at n=30.

- `seed`: Integer 0..5. Indexes the parameter configuration within each (family, n) group.
  The specific random or deterministic sequence associated with each seed is not
  described in this claim (the seed-to-sequence mapping is not in the CSV).
