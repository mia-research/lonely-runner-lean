# Formalized Claim: CLAIM-LRC-000042

## Claim Type
Empirical comparative claim (LRC method discriminability across PRNG and deterministic
torus generators via planar, lattice, boundary, and singular-value metrics).

## Domain
Dataset: `/Users/trentpalelei/Downloads/LRC_Quick_Validation__methods_focus_.csv`
SHA-256: `27bf7a704cac6795a98828791b067fa09d016a94662d904819ee65d4374565f9`
Rows: 5 generators, n=200,000 triplets each.
Columns used: `generator, n, triplets, plane_zero_frac, plane_max_bin_frac,
lattice_rate_tol0, lattice_rate_tol1e3, eff_rank_lag3, sv_max, sv2,
boundary_hits_eps1e-3, fragility_eps_star, fragility_base_rate, fragility_end_rate`.

## Observed Data (complete dataset)

| generator               | plane_max_bin_frac | boundary_hits | lattice_tol1e3 | sv_max   | sv2      | fragility_base | fragility_end |
|-------------------------|--------------------|---------------|----------------|----------|----------|----------------|---------------|
| RANDU                   | 5.00e-06           | 773           | 0.0            | 129.456  | 129.159  | 0.0            | 0.0           |
| PCG64                   | 1.00e-05           | 816           | 0.0            | 129.339  | 129.170  | 0.0            | 0.0           |
| MT19937                 | 1.00e-05           | 818           | 5.00e-06       | 129.431  | 129.341  | 5.00e-06       | 5.00e-06      |
| TORUS_rational_1/5      | 2.00e-01           | 0             | 0.0            | 170.129  | 144.720  | 0.0            | 0.0           |
| TORUS_irrational_sqrt2/2| 5.00e-06           | 796           | 0.0            | 174.148  | 147.783  | 0.0            | 0.0           |

Common values across all generators: n=200,000, triplets=199,998,
plane_zero_frac=0.0, lattice_rate_tol0=0.0, eff_rank_lag3=4, fragility_eps_star=inf.

## Formal Proposition
Define the following discriminant metrics over generators G in the dataset:
- `plane_max_bin_frac(G)`: maximum fractional bin occupancy in planar projection.
- `boundary_hits(G)`: count of boundary hit events at epsilon=1e-3.
- `lattice_rate_tol1e3(G)`: detected lattice rate at tolerance 1e-3.

Adjudicable statements:
1. TORUS_rational_1/5 exhibits plane_max_bin_frac = 0.2000, which is approximately
   20,000x–40,000x larger than all stochastic generators (range: 5e-06 to 1e-05),
   correctly reflecting its deterministic rational lattice structure.
2. TORUS_rational_1/5 is the only generator with boundary_hits = 0, while all other
   generators produce boundary_hits in [773, 818].
3. All generators share eff_rank_lag3 = 4 and lattice_rate_tol0 = 0.0, indicating
   the LRC method does not over-trigger lattice detection at zero tolerance.
4. TORUS_irrational_sqrt2/2 is indistinguishable from stochastic PRNGs on
   plane_max_bin_frac (5e-06) and boundary_hits (796), correctly reflecting
   equidistribution properties of irrational torus sequences.
5. fragility_eps_star = inf for all generators, indicating no finite epsilon
   produces structural fragility in this corpus.
6. MT19937 is the only stochastic generator exhibiting any non-zero lattice signal
   (lattice_rate_tol1e3 = 5e-06), a marginal but notable structural trace.

## Falsification Rule
This claim is falsified if recomputation from the same source file (SHA-256 above)
yields plane_max_bin_frac for TORUS_rational_1/5 outside [0.19, 0.21], or
boundary_hits for TORUS_rational_1/5 != 0, or boundary_hits for any stochastic
generator outside [700, 900].
