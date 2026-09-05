# Multi-Divisible Batch Certification Summary (Finite Window)

- Scope: finite-window exact checks per template.
- This artifact is computational certification over `M <= M_cap`, not a full asymptotic closure theorem.

## n=13, |E_div|=2
- templates: 1320
- total finite checks |T|: 27702
- total phi violations: 0
- min template worst_x0: 3544
- min template d2 margin (B_safe-d2_lb_floor): 7365
- max L0: 360360

## n=13, |E_div|=3
- templates: 1980
- total finite checks |T|: 42561
- total phi violations: 0
- min template worst_x0: 2042
- min template d2 margin (B_safe-d2_lb_floor): 3606
- max L0: 360360

## Run Notes
- n_list: `13`
- d_list: `2,3`
- f_pool: `1,2,3,4`
- m_cap: `100`
- workers: `1`
- validate_bruteforce: `0`
- kernel_path: `/Users/trentpalelei/Desktop/Math Ex/reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_multidiv_boundary_certifier_v1.py`
- max_templates: `0`

## Artifacts
- rows: `lrc_case2_multidiv_batch_rows_n13_d23_f1234_m100_v1.csv`
- checks: `lrc_case2_multidiv_batch_checks_n13_d23_f1234_m100_v1.csv`
- summary: `lrc_case2_multidiv_batch_summary_n13_d23_f1234_m100_v1.md`
