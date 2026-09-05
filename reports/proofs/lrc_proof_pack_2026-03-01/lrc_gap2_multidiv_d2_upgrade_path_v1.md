# Gap-2 Formal Layer: D.2 Upgrade Path (v1)

Status: planning/proof-structure artifact for the next step after batch certification.

## 1. Current certified state

From `lrc_case2_multidiv_batch_*_n13_d23_f123_m80_v1`:
- finite-window template/checkset infrastructure is in place,
- `1155` templates (`|E_div|=2,3`) and `20874` exact checks were run,
- zero `phi(n)` violations in that window.

This is computational evidence, not yet an asymptotic theorem closure.

## 2. Why the current D.2 diagnostic is not theorem-grade yet

We triaged the current component-wise D.2 diagnostic using
`lrc_case2_multidiv_d2_gap_triage_v1.py`.

Summary (`n=13`, `M<=80`):
- `|E_div|=2`: 660 templates, only 3 crossed `d2_lb_floor >= phi(13)`.
- `|E_div|=3`: 495 templates, only 9 crossed `d2_lb_floor >= phi(13)`.
- Most templates remain below `phi(n)` under the current lower-bound constants by `M=80`.

So the obstacle is not exact-check failure (`x0` passes), but lower-bound sharpness.

## 3. The exact theorem target to promote

Promote the current diagnostic into a theorem-grade lemma of the form:

`B_safe(F,M) >= a_F M + b_F` with `a_F>0`, for each multi-divisible template family `F`.

Then define
`M0(F)=ceil(((n-1)-b_F)/a_F)` and finite set
`T(F)={1<=M<M0(F): gcd(M,nL0)=1}`
exactly as in one-divisible TCP.

This is the direct bridge from computational infrastructure to full template certification.

## 4. Immediate proof-engineering tasks

1. Replace the coarse additive constant in the current component D.2 bound with a sharper component-event constant that remains explicit and uniform in `M`.
2. Derive per-template `(a_F,b_F)` from interval/component geometry plus the sharpened constant.
3. Add a multidiv checkset builder that outputs `M0(F), T(F)` from those coefficients.
4. Re-run batch certification on `T(F)` (exact kernel) and report theorem-compatible artifacts.

## 5. Guardrail

No scope overclaim: this note does not assert Gap-2 closure. It defines the formal upgrade path from current evidence to a theorem-level multi-divisible TCP analogue.
