# DEVIATIONS — PREREG_brick_e_cd_degree_v2.md (run log 2026-08-22)

- **D1 (carried from v1):** degree is read per LARGE CRT factor of |A_new(F_p)| only; small factors
  (3 at every rung; also 7, 19 at p=163) have rep-collisions making the fit ill-posed — consistency
  flags, not degrees. Applied throughout.
- **D2 (control ii plant substitution):** the prereg's plant "c(d)=a·d^{i₀} with λ^{i₀}=κ" — **no
  exactly-covariant monomial exists on Q at p=43** (verified by exhaustive search i < 4n with the
  exact on-Q covariance check c(λd)=κ_eff·c(d); the mod-n wrap breaks monomial covariance). Substituted:
  a plain degree-2 plant c(d)=77d²+123 on the full Q, routed through the identical null+π pipeline.
  It FIRES (D=2, π=0.0005 ≤ 0.01) — the control's purpose (pipeline detects planted low-degree
  structure through the full permutation path) is served. The κ-propagation path itself is exercised
  by the null construction and verified on the real data (covariance reproduction assert).
- **D3 (κ convention):** the propagation uses the MEASURED global eigenvalue κ_eff (the consistent
  ratio e(λd)/e(d) on all invertible values; κ_eff = κ² at p=43, also a nontrivial cube root of 1 mod
  |A_new|) rather than the σ-eigenvalue κ — this is what the real data satisfies; flagged for
  transparency, no substantive change (both are primitive cube roots; the null's free structure is
  identical).
- **D4 (calibration scope):** control (iii)'s uniformity check is degenerate at the p=43 lead rung
  (5 reps → the null D-histogram is nearly constant at 14) — frac(π≤0.01) = 0.0015, conservative.
  The check is meaningful at rungs ≥ 163 (reps ≥ 23) where the null has spread, per the prereg's own
  power accounting. Not a failure; a scope note. **UPDATE (2026-08-23):** at the well-posed powered
  rungs the null degree is pinned at the CEILING (spread 0 at p=127, 0–1 at p=547), so control (iii)
  stays degenerate at every rung — a property of the statistic (a generic μ₃-covariant interpolant is
  full-degree a.s.), not of the rung. The read is unaffected (π=1.0 real-at-ceiling is not a
  false-positive artifact; power comes from control (ii)'s dynamic range). See `RESULT_..._v2.md` §4.

- **D5 (WELL-POSEDNESS — rung selection corrected; run 2026-08-23):** the degree fit over `Z/q`
  (`q | p²+p+1`) needs `q ≥ n` or the domain `d∈[1,n)` collides mod q and NO CRT factor is fittable.
  Of the frozen ladder, **only p=43 and p=547 satisfy qmax≥n**; p=67/79/163/211 are ill-posed
  (`large=[]`). The prior-session p=163/211 runs were on ill-posed rungs. Added **p=127** (qmax=5419≥127,
  reps=21) as a second well-posed powered rung, from an admissible-prime search (`p≡7 mod12`, `n` prime,
  `6∣n−1`, `qmax≥n`). The frozen statistic/controls are unchanged; this only fixes the rung SELECTION the
  spec already required ("the large factor where the Q-values are distinct").
- **D5b (Pohlig–Hellman + cyclic projection):** `p²+p+1` squarefree ⇒ `A_new(F_p)` cyclic; the runner
  (`brick_e_rung_v2.sage`) projects to the Sylow-qmax subgroup via the group cofactor `M//qmax` (dlog
  table = qmax, not the full group order) and takes `base` as the first nonzero projection — NO
  per-element `.order()` (v1's `max(cands, key=order)` hung p=547 for 4.5 h at 99% CPU).
- **D6 (control-iv `I2` bug):** v1's `Fq.gen()` is a root of GF(p²)'s default modulus, not `√−1`, so
  `assert I2²==−1` crashed p=163/211. Fixed to `I2 = Fq(-1).sqrt()`; fires 15/15 at p=43.
- **D7 (fast degree engine):** the v1 fitter climbed `D=0..|Q|−1` with a Gaussian-elimination fit per D
  (`O(|Q|⁴)`), infeasible at |Q|=273 × 2000 draws (≈ days). Replaced by Newton divided differences
  (`O(|Q|²)`, inverse denominators precomputed once) in `brick_e_analysis_v2.py`; the interpolant is
  unique so the degree matches v1 exactly (p=43 D_obs=14 reproduced). p=547 analysis: 5 s.
- **D8 (control-iv owed at powered rungs):** the `F_{p²}` ρ-identity instrument (~p² places over GF(p²))
  did not complete at p=127/547 in-budget; recorded OWED (structural, scale-independent — held 15/15 at
  p=43), not assumed. The QR-half degree read does not depend on it.
