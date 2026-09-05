# Gap-2 Multi-Divisible Geometry Probe (n=13, v1)

Status: empirical probe for geometry regularity; not a closure claim.

Tool: `lrc_case2_multidiv_band_geometry_v1.py`

Setup: fixed non-divisible set `E_fixed={1,2,3,4,5,6,7,8,9}`, admissible `M` up to 80 (`gcd(M, n*L0)=1`, `L0=32760`), and multi-divisible profiles shown below.

## E_div = (13,26,39)

- Samples: 18 admissible M values (`M <= 80`).
- `B_div_components`: constant `4` across all samples: `True`.
- `B_div_count`: `21840*M + 4` (exact across samples: `True`).
- `lo_total_len`: `1120*M + 0` (exact across samples: `True`).
- `hi_total_len`: `1120*M + 1` (exact across samples: `True`).
- Component endpoint formulas (exact over all sampled M):
  - comp 0: `lo=2520*M+0`, `hi=10080*M+0`, `len=7560*M+1` (exact: `True`).
  - comp 1: `lo=11760*M+0`, `hi=15120*M+0`, `len=3360*M+1` (exact: `True`).
  - comp 2: `lo=17640*M+0`, `hi=21000*M+0`, `len=3360*M+1` (exact: `True`).
  - comp 3: `lo=22680*M+0`, `hi=30240*M+0`, `len=7560*M+1` (exact: `True`).

## E_div = (13,26)

- Samples: 18 admissible M values (`M <= 80`).
- `B_div_components`: constant `2` across all samples: `True`.
- `B_div_count`: `25200*M + 2` (exact across samples: `True`).
- `lo_total_len`: `1120*M + 0` (exact across samples: `True`).
- `hi_total_len`: `1120*M + 1` (exact across samples: `True`).
- Component endpoint formulas (exact over all sampled M):
  - comp 0: `lo=2520*M+0`, `hi=15120*M+0`, `len=12600*M+1` (exact: `True`).
  - comp 1: `lo=17640*M+0`, `hi=30240*M+0`, `len=12600*M+1` (exact: `True`).

## E_div = (13,39)

- Samples: 18 admissible M values (`M <= 80`).
- `B_div_components`: constant `3` across all samples: `True`.
- `B_div_count`: `24360*M + 3` (exact across samples: `True`).
- `lo_total_len`: `1120*M + 0` (exact across samples: `True`).
- `hi_total_len`: `1120*M + 1` (exact across samples: `True`).
- Component endpoint formulas (exact over all sampled M):
  - comp 0: `lo=2520*M+0`, `hi=10080*M+0`, `len=7560*M+1` (exact: `True`).
  - comp 1: `lo=11760*M+0`, `hi=21000*M+0`, `len=9240*M+1` (exact: `True`).
  - comp 2: `lo=22680*M+0`, `hi=30240*M+0`, `len=7560*M+1` (exact: `True`).

## E_div = (26,39)

- Samples: 18 admissible M values (`M <= 80`).
- `B_div_components`: constant `4` across all samples: `True`.
- `B_div_count`: `24360*M + 4` (exact across samples: `True`).
- `lo_total_len`: `1120*M + 0` (exact across samples: `True`).
- `hi_total_len`: `1120*M + 1` (exact across samples: `True`).
- Component endpoint formulas (exact over all sampled M):
  - comp 0: `lo=1260*M+0`, `hi=10080*M+0`, `len=8820*M+1` (exact: `True`).
  - comp 1: `lo=11760*M+0`, `hi=15120*M+0`, `len=3360*M+1` (exact: `True`).
  - comp 2: `lo=17640*M+0`, `hi=21000*M+0`, `len=3360*M+1` (exact: `True`).
  - comp 3: `lo=22680*M+0`, `hi=31500*M+0`, `len=8820*M+1` (exact: `True`).

## Interpretation for Gap 2

- For these profiles, the `B_div` component decomposition is structurally stable in `M` and all measured component endpoints are affine in `M`.
- This supports a component-wise frozen-band construction where each component can be treated with D.1'/D.2'-style counting after replacing a single interval by a finite union of affine components.
- Next required step: derive these affine endpoint formulas analytically from congruence conditions, then plug into a multi-component D.2-style lower bound.

## Artifacts

- `lrc_case2_multidiv_band_geometry_summary_n13_ediv13_26_39_m80_probe.csv`
- `lrc_case2_multidiv_band_geometry_components_n13_ediv13_26_39_m80_probe.csv`
- `lrc_case2_multidiv_band_geometry_summary_n13_ediv13_26_m80_probe.csv`
- `lrc_case2_multidiv_band_geometry_components_n13_ediv13_26_m80_probe.csv`
- `lrc_case2_multidiv_band_geometry_summary_n13_ediv13_39_m80_probe.csv`
- `lrc_case2_multidiv_band_geometry_components_n13_ediv13_39_m80_probe.csv`
- `lrc_case2_multidiv_band_geometry_summary_n13_ediv26_39_m80_probe.csv`
- `lrc_case2_multidiv_band_geometry_components_n13_ediv26_39_m80_probe.csv`
