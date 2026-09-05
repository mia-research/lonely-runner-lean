# Gap 2 Widened Run Note (n=13, |E_div|=2,3, f_pool={1,2,3,4})

## Purpose
Execute the theorem-track pipeline after formalizing the sharpened component-wise D.2 statement:
1. Build widened finite-window seed checks.
2. Derive per-template `(a_F,b_F), M0(F), T(F)` via TCP-affine builder.

## Step A: Widened Finite-Window Seed
Artifacts:
- `lrc_case2_multidiv_batch_rows_n13_d23_f1234_m100_v1.csv`
- `lrc_case2_multidiv_batch_checks_n13_d23_f1234_m100_v1.csv`
- `lrc_case2_multidiv_batch_summary_n13_d23_f1234_m100_v1.md`

Configuration:
- `n=13`
- `d in {2,3}`
- `f_pool={1,2,3,4}`
- `M_cap=100`

Results:
- Templates: `3300` (`1320` with `d=2`, `1980` with `d=3`)
- Exact checks: `70,263`
- `phi(13)` violations: `0`
- `B_safe < d2_lb_floor` violations: `0`

## Step B: Widened TCP-Affine Build
Artifacts:
- `lrc_case2_multidiv_tcp_rows_n13_d23_f1234_tcp_affine_m420_v1.csv`
- `lrc_case2_multidiv_tcp_checks_n13_d23_f1234_tcp_affine_m420_v1.csv`
- `lrc_case2_multidiv_tcp_summary_n13_d23_f1234_tcp_affine_m420_v1.md`

Configuration:
- input checks: Step A checks CSV
- `m_cap_max=420`

Results:
- Templates processed: `3300`
- Template status: `3300/3300 finite_target_verified`
- `M0(F)` range: `[46, 340]`
- Target checks `|T(F)|` total: `195,448`
- `ok_phi=0` failures in target checks: `0`
- `ok_affine_lb=0` failures in target checks: `0`

## Scope Guardrail
Closed in this run:
- Widened finite-window TCP-style certification layer for multi-divisible templates in stated configuration.

Still open:
- Full asymptotic theorem closure for all multi-divisible families beyond finite cap remains a proof task.
