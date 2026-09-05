# Assumptions: CLAIM-LRC-000056

1. CSV rows are valid and schema-consistent; source integrity verified by SHA-256
   `99b30d585e6378f834d3357efef71ec14852fee04e01ecbb52e86a5d52c00139`.
2. `phi_match` is the operational phase-match indicator, but it is NOT uniformly
   computed across all families. It takes value YES/NO only for arithmetic and perturbed
   families; geometric and random families have this column empty (the pipeline does not
   apply the phi_match test to these families). Statements about phi_match_rate=0.0 for
   geometric/random are therefore invalid — the correct status is N/A (not measured).
3. `unique_phases == phi_n` is the structural phase-saturation condition. It is only
   measurable when `unique_phases` is non-empty. `unique_phases` is derived from isolated
   boundary points: a perfect bijection holds across all 220,110 rows —
   isolation_count > 0 ↔ unique_phases non-empty ↔ first_isolation non-empty.
   Only arithmetic rows satisfy isolation_count > 0; all other families have
   isolation_count = 0, making unique_phases undefined by construction (not by pipeline
   design choice).
4. This is a dataset claim, not a universal theorem over all LRC constructions or
   all possible speed families beyond those tested.
5. No hidden row filtering beyond family grouping is applied.
6. `n` ranges over {5..15} and phi_n ranges over {2, 4, 6, 8, 10, 12}; results
   are not claimed to generalise beyond these parameter ranges without further testing.
7. The four families (arithmetic, geometric, perturbed, random) are treated as
   exhaustive for this corpus; no family-level sampling bias is asserted.
