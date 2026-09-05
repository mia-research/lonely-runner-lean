# Gap 1 Extension Progress: One-Divisible All-Distinct Boundary Certification (n=17,19)

## Objective
Advance Gap 1 coverage beyond the previously certified set by running the boundary/event-cell
D.3 batch certifier on the next prime values.

## Method
Script:
- `lrc_case2_d3_batch_certify_boundary_v1.py`

Class certified:
- one-divisible all-distinct templates with `E(M)=E_fixed ∪ {M} ∪ {n}` and `|E_fixed|=n-3`.

Outputs generated in standard D.3 format:
- rows CSV
- checks CSV
- summary MD

## New Results

### n=17
- templates: `120` (`C(16,14)`)
- total finite checks `|T|`: `11,959`
- total violations: `0`
- min template worst-case `x0`: `159,856`
- max `M0(F)`: `579`

Artifacts:
- `lrc_case2_d3_batch_rows_n17_boundary_v1.csv`
- `lrc_case2_d3_batch_checks_n17_boundary_v1.csv`
- `lrc_case2_d3_batch_summary_n17_boundary_v1.md`

### n=19
- templates: `153` (`C(18,16)`)
- total finite checks `|T|`: `18,377`
- total violations: `0`
- min template worst-case `x0`: `1,590,410`
- max `M0(F)`: `723`

Artifacts:
- `lrc_case2_d3_batch_rows_n19_boundary_v1.csv`
- `lrc_case2_d3_batch_checks_n19_boundary_v1.csv`
- `lrc_case2_d3_batch_summary_n19_boundary_v1.md`

## Context with Existing Boundary Result
Existing in-pack boundary run for `n=13`:
- templates: `66`
- checks: `4,096`
- violations: `0`

## Scope Statement
These runs extend exact finite certification evidence for Gap 1 to additional prime `n`.
They do not, by themselves, constitute a full analytic theorem closing Gap 1 for all prime `n`.
