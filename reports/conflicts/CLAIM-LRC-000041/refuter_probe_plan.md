# CLAIM-LRC-000041 Refuter Probe Plan

## Primary Probes
1. Recompute success rates for arithmetic vs random at `n=6`, `horizon=1000`.
2. Validate that arithmetic rows are all complete (`complete_success=YES`).
3. Re-run the two random failure seeds with extended horizons (`T=10,000`, `T=100,000`) to test delayed isolation vs structural failure.

## High-Risk Seeds
- seed 506060 (boundary_count=18186, runners_isolated=4, avg_first_isolation=0.6412558629808041)
- seed 506091 (boundary_count=20428, runners_isolated=4, avg_first_isolation=2.323276403825178)

## Publication Gate
Hold promotion if random-family failures are unresolved or if arithmetic universal-complete property is not reproducible.
