# RESULTS schema — one file per work package

Every farmed work package writes exactly one `WP<n>_<slug>.json` here. Opus reads
all of them in the coordination pass (WPZ). Required top-level keys:

```json
{
  "wp": "WP1_nq_nearmiss",
  "model": "sonnet",
  "n_samples": 20000,
  "bit_range": [8, 120],
  "attack_valid": true,
  "positive_control": {"planted_strength": 0.6, "detected": true, "control_z": 31.2},
  "null_model": "wrong-n' candidates + label permutation",
  "primary_result": { "...": "test-specific numbers" },
  "reading": "conditional negative/positive, bounded to features+n+floor",
  "artifacts": ["path/to/any/plots_or_npz"],
  "runtime_sec": 812
}
```

Rules (enforced in review, from `btc_puzzle_hunt_method`):
- `positive_control.detected` MUST be true or the null is **discarded, not reported**.
- `attack_valid` false ⇒ result is a *structure probe*, never phrased as an attack.
- `reading` must be a **conditional** negative (never "impossible"/"ruled out"),
  bound to the feature set, sample size, and noise floor.
- No feature may derive from `d,n,k,D,D_terms` in an attack-valid WP
  (`lib_data.assert_attack_valid`).
