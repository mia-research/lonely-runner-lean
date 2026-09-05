# Metric Definitions: CLAIM-LRC-000056-EXT-001

- `n`: Number of walkers/agents in the LRC construction. Integer in {5, 6, ..., 15} for
  this corpus. Governs both the speed sequence length and the Euler totient reference.

- `phi_n`: Euler's totient φ(n); the count of integers in [1, n] coprime to n.
  Used as the theoretical phase-count reference (CLAIM-LRC-000056) and as the lower bound
  reference for `isolation_count` (Law 2 of this claim).

- `delta`: Arithmetic step parameter for the speed sequence. The sequence is
  `a_k = base + k·delta` for k = 0, 1, ..., n-1. Enters directly in the fi formula
  `fi = 1/(n·delta)` (Law 1).

- `base`: Arithmetic base parameter for the speed sequence. Does NOT appear in the
  fi formula; all tested (base, delta, alpha, seed) combinations satisfy Law 1.

- `first_isolation (fi)`: The continuous time value at which the first isolation event
  occurs in the LRC simulation for a given row. Stored as a floating-point column.
  Defined and non-empty exclusively for arithmetic rows in this corpus.

- `isolation_count (iso)`: Count of distinct isolation events observed per row.
  An isolation event occurs when a boundary point becomes phase-isolated in the LRC
  trajectory. Non-zero exclusively for arithmetic rows in this corpus.

- `relative_error(fi)`: Quantity `|first_isolation − 1/(n·delta)| / (1/(n·delta))`.
  Used to verify exactness of Law 1. Threshold for machine-precision exactness: < 1e-9.
  Observed maximum across all 55,000 arithmetic rows: 5.12e-13.

- `mode(iso | n)`: The most frequently occurring value of `isolation_count` among all
  arithmetic rows with the given `n`. Computed across all seeds, base values, delta
  values, and alpha values for that n. Used in Law 3.

- `unique_phases`: Count of distinct isolated phase regions per row; equals `phi_n`
  for all arithmetic rows (100% phase saturation, established in CLAIM-LRC-000056).
  Confirms that isolation events produce exactly phi_n distinct phases in arithmetic rows.

- `boundary_count (bc)`: Total number of boundary crossing events per row. In this corpus,
  bc does NOT follow the `5000·n(n-1)` law from CLAIM-LRC-000044 (different simulation
  regime: continuous vs discrete time, scales differ by ~3 orders of magnitude). bc is
  not directly tested in this claim's laws.
