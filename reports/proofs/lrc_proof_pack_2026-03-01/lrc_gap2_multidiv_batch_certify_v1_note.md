# Gap-2 Multi-Divisible Batch Certification Layer (v1)

Status: computational certification layer delivered. This is finite-window certification, not full asymptotic theorem closure.

## New batch script

`lrc_case2_multidiv_batch_certify_v1.py`

What it adds:
- Enumerates multi-divisible template families with `|E_div|>=2`.
- Builds admissible finite checksets `T(F;m_cap) = {1<=M<=m_cap : gcd(M,nL0)=1}`.
- Runs exact boundary/event kernel (`lrc_case2_multidiv_boundary_certifier_v1.py`) on each check.
- Emits D.3-style batch artifacts:
  - `rows` (per-template aggregates),
  - `checks` (per-template, per-M exact results),
  - `summary` (group totals).

## First full batch run (n=13)

Run config:
- `n=13`
- `|E_div| in {2,3}`
- factor pool `f_pool={1,2,3}` with `E_div={13*f : f in subset}`
- `m_cap=80`

Artifacts:
- `lrc_case2_multidiv_batch_rows_n13_d23_f123_m80_v1.csv`
- `lrc_case2_multidiv_batch_checks_n13_d23_f123_m80_v1.csv`
- `lrc_case2_multidiv_batch_summary_n13_d23_f123_m80_v1.md`

Results from summary:
- `n=13, |E_div|=2`: templates `660`, checks `11811`, phi violations `0`.
- `n=13, |E_div|=3`: templates `495`, checks `9063`, phi violations `0`.
- Total templates `1155`, total checks `20874`, zero phi violations in this window.

## Correctness cross-check

A brute-force validation smoke run was executed using `--validate-bruteforce`:
- tag: `n13_d23_bruteforce_smoke_v1`
- 20 templates sampled (`|E_div|=2,3`) at `m_cap=19`
- exact parity passed for all sampled checks (no mismatches, no phi violations).

## Scope note

These artifacts establish the template/checkset pipeline requested for `|E_div|>=2` and provide large-scale finite-window evidence. Remaining theorem-grade closure still needs promotion of the component-wise D.2-style bound to a formal universal statement.
