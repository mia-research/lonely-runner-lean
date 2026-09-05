# Reproduction Policy

Statuses:
1. `match`: Numeric deltas within tolerance across all compared values.
2. `partial`: Majority matches but at least one significant discrepancy.
3. `fail`: Widespread mismatch or incompatible structures.

Promotion policy:
- Only `match` may proceed to A-level promotion checks.

Required report fields:
1. status
2. expected artifact
3. actual artifact
4. tolerance config
5. compared value count
6. mismatch count
7. max relative diff
