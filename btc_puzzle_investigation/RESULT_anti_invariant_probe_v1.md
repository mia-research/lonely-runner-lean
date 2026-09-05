# #2 — anti-invariant probe: do cheap odd-y readouts concentrate over d?

Date: 2026-07-18. Pre-registered by `experiment-designer`. The faithful "outside the symmetry" test:
the ANTI-invariant readouts are the only ones that can pin d (invariant ones see only the μ6-orbit of
d). Script `scratchpad/e2anti.py`. Model curves C1 (y²=x³+7/F_2143, n=2089, L=348), C2 (y²=x³+13/F_3001,
n=3079, L=513), exhaustive d.

## Method (per pre-reg)
Readouts of exact μ6-type (0,1) = odd functions of y alone (sign y, y centered, y³) — the cleanly-typed
anti-invariant readouts. (Coordinate readouts using x transform by field-element multiplication x_{λd}=βx_d,
not a phase, so they lack clean complex type and are NOT in this test.) Statistic on the additive Z/n
spectrum folded over μ6 frequency-orbits: peak R = max P̃/ΣP̃, spread N_eff = (ΣP̃)²/ΣP̃² (E2 tested only
the peak; N_eff is the spread channel). Matched null = permute the L fundamental-domain values across
μ6-orbits and RE-INFLATE with the (0,1) phase, then recompute the spectrum (permuting the power vector is
a no-op — the deciding null-design point). B=4000.

## Results
Positive controls FIRE on both curves (Gate 0 passed): clean plant (μ3-projected sin(a₀·)) R=1.0, N_eff=1,
exc=0/4000, recovers the planted orbit; graded plant detects at φ=0.3 (exc=0), not φ=0.1 → detection floor
φ*≈L^−¼≈0.2, confirming the analytic power.

| curve | readout | R (z) | N_eff (z) | excR/4000 | excN/4000 | verdict |
|---|---|---|---|---|---|---|
| C1 | sign(y) | 0.028 (−0.1) | 123 (+0.6) | 1842 | 2884 | within null |
| C1 | y_centered | 0.026 (−0.5) | 126 (+0.9) | 2661 | 3306 | within null |
| C1 | y_centered³ | 0.032 (+0.5) | 114 (−0.4) | 1056 | 1367 | within null |
| C2 | sign(y) | 0.017 (−0.9) | 189 (+1.4) | 3324 | 3688 | within null |
| C2 | y_centered | 0.024 (+0.7) | 180 (+0.6) | 833 | 2858 | within null |
| C2 | y_centered³ | 0.016 (−1.0) | 192 (+1.6) | 3481 | 3808 | within null |

**Verdict (pre-registered): SCOPED NULL.** Every cleanly-typed anti-invariant (odd-y) readout sits at the
matched-null median (|z|<1.6, exc in bulk) on BOTH curves — spectrally featureless (Weil-random). No cheap
odd-y single-readout concentration over d above single-orbit fraction φ*≈0.2. POWER+SCOPE: single readout,
odd-y type-(0,1) only, n∈{2089,3079}, concentration ≥ φ*. NOT "no anti-invariant leak."

Contrast worth noting: the anti-invariant odd-y readouts are AT the median (Weil-random), unlike the
μ6-INVARIANT objects (#1: RESULT_outside_symmetry_v2), which were flatter-than-random (+12σ/+32σ,
hyperuniform). The invariant side is anomalously flat; the anti-invariant odd-y side is plain random.

## Scope limits (stated so this is not over-read)
- **Odd-y only.** The cleanly-typed anti-invariant readouts are functions of y alone. The JOINT (x,y)
  anti-invariant readouts — where the master's 0.93 aligned readout lives — lack clean complex type
  (β-multiplication on x), need an isotype projection, and are NOT covered here. The 0.93 aligned readout
  also requires phase alignment ≈ solving the DLP to build; it is not a cheap single readout. So this
  result does NOT touch the joint/multi-coordinate frontier.
- **Single readout, small n, φ*≈0.2.** Says nothing about multi-readout/joint leak, unbounded-degree
  readouts, or cryptographic n.

## Net across #1 and #2 ("outside the symmetry", both halves)
- Invariant side (#1): no leak-shaped CONCENTRATION (confirmed); a real flatter-than-random/hyperuniform
  departure (characterized, mechanism unpinned) — anti-leak direction. Provably cannot pin d anyway.
- Anti-invariant odd-y side (#2): featureless (Weil-random); no cheap concentration, φ*≈0.2, 2 curves.
- Anti-invariant JOINT side: UNTESTED — the isotype-projected multi-coordinate readouts, coinciding with
  the joint/two-point/unbounded-degree open frontier. Where a cheap handle, if any, would have to live.
No cheap d-handle found in the parts probed; none of this closes the joint frontier.
