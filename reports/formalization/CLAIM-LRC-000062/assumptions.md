# Assumptions: CLAIM-LRC-000062

1. Source integrity verified by SHA-256
   `98b5f1bef13cb0097234a2936f299491966ac123b2afebadbf9e82c346c17897`.
2. All 1,200 rows share fixed parameters: n=10, T=100.0, threshold=0.1.
   Results are specific to this parameter regime and do not generalise to
   other n, T, or threshold values without further testing.
3. `miss_due_to_coarse` is the ground-truth miss indicator; a value of True
   would mean the coarse method failed to detect what the boundary method caught.
   Zero such cases observed in this corpus.
4. `boundary_witness_time` and `coarse_witness_time` are per-trial wall-clock
   witness times; variance across runners and configs is inherent in the data.
   Mean comparison (statement 4) summarises this distribution.
5. The speeds column contains per-config speed arrays (10 speeds per row at n=10);
   these are inputs, not outputs, and are not directly adjudicated here.
6. 120 distinct config IDs each tested across 10 runners; runner variation
   contributes to the observed spread in witness times.
7. The float64 repro error (2.045e-10) is elevated relative to other cycle claims
   but remains below the stable threshold (1e-09). The decimal128 anchor
   (2.433e-32) confirms high-precision stability.
8. Coarse midpoint method is understood as an approximation of the boundary set
   method; equivalence in this corpus does not imply general equivalence.
