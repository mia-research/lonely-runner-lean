# `n = 11` Self-Contained Certificate Appendix

This appendix packages the exact finite data currently available for the actual
exactly-one-divisible `n = 11` branch.

## Exact Objects Frozen Here

- The full local multiplicity-profile kernel for `9` singleton/pair contributors on `Z_11`.
- The `45` fully covered local profiles inside that kernel.
- The exact singleton-collapse classifier for actual bad profiles.
- Explicit witness tuples for each of the `38` actual bad local profiles.

## Exact Counts

- Total reachable local profiles: `1268`
- Fully covered local profiles: `45`
- Actual bad profiles: `38`
- Impossible bad profiles: `7`
- Profiles with positive local `min_bN_capsolv` lower bound: `1223`

## Exact Classifier

Let `q^down = (q_1,...,q_11)` be a fully covered local profile and let
`T = sum_i q_i`. Then the singleton-collapse theorem gives:

```text
q^down is actual bad  <=>  q_1 >= 18 - T.
```

This separates the `45` fully covered local profiles into `38` actual bad
profiles and `7` impossible profiles.

## Exact Limitation

This packet closes the local-state layer, but it does **not** by itself prove
the final weighted occupancy inequality needed for a self-contained proof of
the full actual exactly-one-divisible branch.

The remaining theorem target is still:

```text
sum_j N_j <= B_div - 10
```

on the actual bad-event decomposition along `B_div`.

## Files

- `lrc_n11_local_profile_rows_2026-03-30.csv`
- `lrc_n11_local_bad_profile_rows_2026-03-30.csv`
- `lrc_n11_actual_bad_state_witnesses_2026-03-30.csv`
- `lrc_n11_impossible_bad_profile_rows_2026-03-30.csv`
- `lrc_n11_selfcontained_certificate_manifest_2026-03-30.json`
