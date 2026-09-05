# Multi-Divisible Batch Certification Summary (Finite Window)

- Scope: finite-window exact checks per template.
- This artifact is computational certification over `M <= M_cap`, not a full asymptotic closure theorem.

## n=13, |E_div|=2
- templates: 10
- total finite checks |T|: 36
- total phi violations: 0
- min template worst_x0: 10484
- min template d2 margin (B_safe-d2_lb_floor): 25977
- max L0: 180180

## n=13, |E_div|=3
- templates: 10
- total finite checks |T|: 43
- total phi violations: 0
- min template worst_x0: 3718
- min template d2 margin (B_safe-d2_lb_floor): 7217
- max L0: 60060

## Run Notes
- n_list: `13`
- d_list: `2,3`
- f_pool: `1,2,3`
- m_cap: `19`
- workers: `1`
- validate_bruteforce: `1`
- kernel_path: `/Users/trentpalelei/Desktop/Math Ex/reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_multidiv_boundary_certifier_v1.py`
- max_templates: `10`

## Artifacts
- rows: `lrc_case2_multidiv_batch_rows_n13_d23_bruteforce_smoke_v1.csv`
- checks: `lrc_case2_multidiv_batch_checks_n13_d23_bruteforce_smoke_v1.csv`
- summary: `lrc_case2_multidiv_batch_summary_n13_d23_bruteforce_smoke_v1.md`
