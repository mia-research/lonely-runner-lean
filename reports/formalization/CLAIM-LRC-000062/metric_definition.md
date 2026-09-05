# Metric Definitions: CLAIM-LRC-000062

- `boundary_detect`: boolean; True if the boundary set method detects the target
  in a given trial.
- `coarse_detect`: boolean; True if the coarse midpoint method detects the target
  in a given trial.
- `miss_due_to_coarse`: boolean; True if boundary_detect=True AND coarse_detect=False
  for a given trial (i.e. the coarse method missed what the boundary method caught).
  Zero such cases in this corpus.
- `boundary_witness_time`: time at which the boundary method first witnesses
  detection, in the same units as T (T=100.0 in this corpus).
- `coarse_witness_time`: time at which the coarse midpoint method first witnesses
  detection; uses coarser grid resolution than boundary method.
- `detect_rate(method)`: proportion of 1,200 rows where the method's detect
  flag is True.
- `miss_rate`: proportion of rows with miss_due_to_coarse=True; 0.0 in this corpus.
- `mean_witness_time(method)`: arithmetic mean of witness time across all rows.
- `threshold`: detection sensitivity parameter; fixed at 0.1 for all rows.
- `T`: time horizon for the experiment; fixed at 100.0 for all rows.
- `speeds`: per-config array of n=10 speed values; input parameters, not outputs.
