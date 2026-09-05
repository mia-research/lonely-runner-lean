# Gap 2 Progress Note: Multi-Divisible TCP-Affine Layer (n=13, f_pool={1,2,3}, M<=340)

## Scope
This note records finite-window certification infrastructure and results for multi-divisible templates.
It does **not** claim a full asymptotic multi-divisible theorem closure.

## New Infrastructure
- Script: `lrc_case2_multidiv_tcp_affine_builder_v1.py`
- Input checks: `lrc_case2_multidiv_batch_checks_n13_d23_f123_m80_v1.csv`
- Kernel dependency: `lrc_case2_multidiv_boundary_certifier_v1.py`

The builder performs, per template:
1. Derive affine coefficients `(a_F,b_F)` from the D.2 diagnostic track (`d2_lb_floor`).
2. Compute `M0(F)` from `a_F M + b_F >= phi(n)`.
3. Build finite target checkset `T(F) = {M <= min(M0-1, m_cap_max): gcd(M,R)=1}`.
4. Extend exact checks to cover `T(F)` and validate:
   - `x0 >= phi(n)` on `T(F)`.
   - `d2_lb_floor >= floor(a_F M + b_F)` on `T(F)`.

## Run Configuration
- `n=13`
- `|E_div| in {2,3}`
- fixed pool: `{1,2,3}`
- cap: `m_cap_max=340`

## Output Artifacts
- `lrc_case2_multidiv_tcp_rows_n13_d23_f123_tcp_affine_m340_v1.csv`
- `lrc_case2_multidiv_tcp_checks_n13_d23_f123_tcp_affine_m340_v1.csv`
- `lrc_case2_multidiv_tcp_summary_n13_d23_f123_tcp_affine_m340_v1.md`

## Finite-Window Results
- Total templates: `1155` (`660` with `|E_div|=2`, `495` with `|E_div|=3`).
- Status: `1155/1155` templates are `finite_target_verified`.
- `M0(F)` range: `[46, 340]`.
- Total target checks: `68,783`.
- `x0 < phi(n)` violations in target checks: `0`.
- affine-LB violations in target checks: `0`.

## Interpretation (Strict)
Closed in this step:
- Per-template TCP-style affine/checkset layer is now implemented and executed for the above `n=13` window.
- Finite target sets `T(F)` for this run are fully validated.

Still open:
- The theorem-grade asymptotic proof that the sharpened component-wise D.2 bound is valid uniformly beyond checked caps.
- Therefore, universal multi-divisible closure remains open.
