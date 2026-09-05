# Metric Definitions: CLAIM-LRC-000057

- `agreement_rate`: proportion of rows where Agreement=true; measures correctness
  of boundary method relative to brute-force ground truth.
- `isolation_match_rate`: proportion of rows where Boundary Isolated == Brute Isolated;
  measures whether both methods detect the same number of isolated phases.
- `Speedup`: ratio Brute Time / Boundary Time as recorded per row; values > 1 indicate
  boundary method is faster.
- `mean_speedup`: arithmetic mean of Speedup over all rows.
- `speedup_range`: [min(Speedup), max(Speedup)] over all rows.
- `Boundary Time` / `Brute Time`: per-case execution times in milliseconds.
- `Boundary Isolated` / `Brute Isolated`: count of isolated LRC phase events detected
  by each method per test case.
- `Agreement`: boolean flag (true/false) indicating whether the two methods produce
  consistent results for a given case; serves as the primary correctness indicator.
