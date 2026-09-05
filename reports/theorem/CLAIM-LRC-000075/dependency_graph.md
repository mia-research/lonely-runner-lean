# Dependency Graph: CLAIM-LRC-000075 (Reclassified Empirical Validator)

Generated: 2026-02-26T03:00:40Z

## Workflow Nodes
- W1: Read configuration (horizon, tests per config, n range).
- W2: Generate speed families (arithmetic, perturbed, random, geometric).
- W3: Compute boundary times and individual-isolation detection events.
- W4: Aggregate success rates/runtime and export CSV summary.

## Workflow Edges
- W1 -> W2 (config_drives_generation)
- W2 -> W3 (generated_speeds_tested)
- W3 -> W4 (detections_aggregated)
