# Metric Definitions: CLAIM-LRC-000058

- `configs`: number of configurations tested per family (30 for all families).
- `success_rate`: proportion of configurations where the LRC detector succeeds;
  1.0 = all 30 configurations succeeded.
- `median_first_time`: median first-detection time across 30 configurations per
  family; lower values indicate faster detection.
- `q25_first_time` / `q75_first_time`: 25th and 75th percentile first-detection
  times; IQR = q75 - q25 measures timing consistency within a family.
- `median_boundary_count`: median number of LRC boundary events per configuration
  across 30 configs; reflects structural complexity of the detection process,
  not directly equivalent to detection speed.
- `IQR_first_time`: derived metric = q75_first_time - q25_first_time; used to
  quantify within-family timing variance.
