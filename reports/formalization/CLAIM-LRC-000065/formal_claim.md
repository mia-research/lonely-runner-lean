# Formalized Claim: CLAIM-LRC-000065

## Claim Type
Empirical single-sample characterisation claim (PCG64 generator under LRC boundary
fragility analysis: planar uniformity, boundary fragility, torus boundary hits,
and generation time).

## Domain
Dataset: `pcg64_boundary_fragility.json`
SHA-256: `eee26d22c03b41977311020edd904d061e72a5a2a8d9127e111e480fc37053aa`
Structure: Single JSON record, 6 numeric fields.
Generator: PCG64. Sample size: n_words=400,000, triplets=399,998.

## Observed Data (complete dataset)

| Field                      | Value                          |
|----------------------------|--------------------------------|
| name                       | PCG64                          |
| n_words                    | 400,000                        |
| triplets                   | 399,998                        |
| plane_onrate_baseline      | 2.5000125000625003e-06         |
| boundary_fragility_epsilon | 0.0                            |
| torus_boundary_hits        | 51,930                         |
| gen_time_s                 | 0.0016772940002738324          |

## Formal Proposition
Define for this single PCG64 run:
- `plane_onrate_baseline`: maximum fractional bin occupancy in planar projection
  for 400,000 words (399,998 triplets).
- `boundary_fragility_epsilon`: smallest epsilon at which boundary fragility is
  detected; 0.0 indicates no fragility detected at the tested threshold.
- `torus_boundary_hits`: total torus boundary crossing events in this run.
- `gen_time_s`: wall-clock generation time in seconds for 400,000 words.

Adjudicable statements:
1. plane_onrate_baseline = 2.5000125000625003e-06, consistent with theoretical
   uniform distribution: 1/n_words = 1/400,000 = 2.5e-06 exactly. The deviation
   from theoretical uniformity is ~1.25e-11 (= 2.5000125000625003e-06 − 2.5e-06),
   well within sampling noise at this
   corpus size.
2. boundary_fragility_epsilon = 0.0, indicating no boundary fragility detected
   at the tested epsilon threshold for this PCG64 run.
3. torus_boundary_hits = 51,930 for 399,998 triplets, giving a torus boundary
   hit rate of ~0.1298 (51,930 / 399,998) in this single run.
4. gen_time_s = 0.001677 s (~1.68 ms) for 400,000 words, implying a throughput
   of ~2.385 × 10^8 words/second in this run.

## Falsification Rule
Falsified if recomputation from the same source file (SHA-256 above) yields any
of the 6 numeric values differing from those stated above by more than 1e-06
(relative). Note: torus_boundary_hits and gen_time_s are single-run measurements
and may vary across independent runs; the falsification rule applies strictly to
the recorded source values, not to expected run-to-run reproducibility.
