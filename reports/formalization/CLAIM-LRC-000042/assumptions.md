# Assumptions: CLAIM-LRC-000042

1. CSV rows are valid and schema-consistent; source integrity verified by SHA-256
   `27bf7a704cac6795a98828791b067fa09d016a94662d904819ee65d4374565f9`.
2. All generators were evaluated under identical parameters: n=200,000 points,
   triplets formed from consecutive triples.
3. `plane_max_bin_frac` is the maximum fractional occupancy of any single bin in
   the planar 3D projection histogram; higher values indicate lattice concentration.
4. `boundary_hits_eps1e-3` counts LRC boundary crossings at epsilon=1e-3;
   zero for TORUS_rational_1/5 reflects its fixed lattice preventing random boundary events.
5. `fragility_eps_star = inf` is a valid sentinel indicating no finite epsilon
   threshold triggers structural fragility for any generator in this corpus.
6. This is a 5-generator benchmark claim; results do not generalise to all PRNGs
   or to other parameter choices (n, epsilon, bin resolution) without further testing.
7. The rational torus TORUS_rational_1/5 is treated as a positive control for
   deterministic lattice structure; TORUS_irrational_sqrt2/2 as a negative control
   (equidistributed, hence indistinguishable from stochastic generators on these metrics).
