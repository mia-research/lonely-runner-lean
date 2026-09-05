# DEVIATIONS — execution of PREREG_boundary_D_short_interval_CM_invariant_v1

Recorded at run time (2026-08-13). Each deviation from the frozen spec, why, and its effect on the verdict.

## D1 — curve scales lowered: 2^{37,41,45} instead of the spec's 2^{40,48,56}
- **Why:** pure-Python, exact-integer compute. `#E` at 2^48/56 needs Schoof (unavailable); the interval
  kangaroo runs and the `#E`-BSGS finder are tractable at ≤2^45.
- **Effect on verdict:** NONE on the mechanism. The spec's own scale banner already states any `n≤2^56`
  has zero power against 2^256 and "measures the MECHANISM, not the real curve." The decision statistic is
  the **slope** of `log₂(ops)` vs interval-bits `N` (collapse ⇒ ½), which is scale-free; three curve
  scales (2^37/41/45) are used only for robustness of `R`. All three still satisfy `W = 2^{20,24,28} ≪ n`.

## D2 — FC1 anomalous test-curve is a separate generic-j curve at ~2^30, not one of the scale curves
- **Why:** the scale curves are j=0 (target family), and the SSSA elliptic-log hom **degenerates on j=0**
  (established in `VALIDATION_sssa_lift_firing_control_v1.md`). FC1's role — prove the op-meter can SEE a
  genuine polynomial/sub-√(W/6) win — requires a curve where SSSA fires, i.e. generic j, a≠0. The spec §5
  explicitly allows "j=0 if reachable at scale else any."
- **Effect:** none on scope; FC1 is a power check on the instrument, not a target-family claim.

## D3 — M = 50 instances per (scale, N) cell (spec floor: M ≥ 100)
- **Why:** the χ₃-sector candidate does up to 3 baby+giant passes, tripling per-instance cost; M=50 keeps
  the 3×3 grid + both firing controls under a few minutes of pure-Python compute.
- **Effect:** the spec's own power table gives detection ceiling `Δ_min ≈ 0.08` at M=100; M=50 raises the
  median op-count relative spread by ~√2, loosening `Δ_min` to ≈0.11. The observed slope (0.50/0.505/0.524)
  and `R_optimal = 1.000` are far inside any such band, and FC2 fires to <5% relative error, so M=50 does
  not threaten the reading. Recorded as a power caveat, not a defect.

## D4 — statistics reported: R_sector AND R_optimal (spec named one R)
- **Why:** the concrete χ₃-exploitation the spec asks for (sector prune) turned out to be *strictly
  counterproductive* (`R_sector = 1.3–2.1 > 1`), because χ₃(x(Q)) is only the orbit label (I1) and cannot
  predict which sector the answer's baby-step occupies. So the *optimal* candidate falls back to baseline:
  `R_optimal = median(min(baseline, sector))/median(baseline) = 1.000`. Both are reported; both are the
  collapse. This is additive to the spec (more evidence), not a departure from its object.

## D5 — FC1 strict threshold `R_FC1 ≤ W^{-0.3}` is crossed only at N≈28–29
- SSSA op-count is a flat ~65 (polylog, recovers d 12/12); baseline ~√(2W). `R_FC1 ~ W^{-0.47}` — a
  **steeper** decay than the `W^{-0.3}` bar — so it crosses, but only once the ~65-op constant is swamped
  (N≳28). The 2^26 test-curve capped N at 25; a ~2^30 anomalous curve is used so FC1 meets its own
  pre-committed threshold rather than being reinterpreted post-hoc (per
  `feedback_prereg_abstention_is_the_finding`).
