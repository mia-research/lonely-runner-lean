# RESULT — Is the `C_T` inter-coordinate coupling a universal geometric constant, or the floor?

**Date 2026-07-19.** Frontier §X.6 (GLM "frontier C": *"run `ct_coupling_universality` across
generators and primes; ~constant ⇒ universal geometric coupling"*). Pre-registered in
`PREREG_ct_coupling_universality_v1.md`; deviations audited in
`..._DEVIATIONS.md`. Scripts: `ct_coupling_universality_v3.py` (end-to-end, control passes),
`ct_coupling_plant_calibration_v1.py` (empirical power), `ct_coupling_universality_v2.py` (first
run). Exact-integer state path; float only in G²/eig/z (analytic sizes). Seed 20260719.

**Anomaly-Drill protocol.** Output below is the **characterization** of the coupling — its magnitude,
the power that magnitude is measured with, and its scope. It is **not** a closure. Per the language
rule, "at/below the floor" is a *bounded, decaying magnitude*, not "no structure."

---

## The corrected control (the number the result is quoted against)

The pipeline's minimum detectable coupling was mis-stated by the prereg's analytic power table (see
D1/D2 in the deviations file). Measured empirically:

- Surrogate pooled-G² null: **df_eff ≈ 16** (mean 15.5→16.7 across n) — confirms the prereg df.
- Plant (known copy-coupling, labeled by the pipeline's own measured ε̂), `n=131072`:
  **ε̂=1.6% → z=8.1**, ε̂=2.4% → z=17.1, monotone-rising, and **silent at n=5000** (z=0.5).
- **Corrected in-scope floor: the sweep detects a coupling of ε ≳ 1.6% at n≈1.3×10⁵** (z≥5),
  down to ~2% mid-range. **No power below ~1.6%; zero power at 2²⁵⁶.**

The control fires exactly where the pre-registered §5 windows say it must once the coupling is
labeled by measured ε̂. Pipeline validated.

## The real data (8 prime-order curves × full orbit; b=7; p ≤ 2¹⁷)

| p | n=#E | z_G² | ε̂ | z_odd | z_even | dev_real/dev_surr | λ₂ | λ₃ | λ₂−λ₃ |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 5197 | 5207 | −1.17 | 0 | −0.6 | −1.4 | 0.57 | 0.376 | 0.306 | 0.070 |
| 8563 | 8465 | −0.98 | 0 | −0.8 | +0.4 | 0.84 | 0.342 | 0.330 | 0.012 |
| 14629 | 14399 | +0.17 | 0.008 | −0.8 | −1.2 | 0.67 | 0.332 | 0.315 | 0.017 |
| 25411 | 25619 | +3.07 | 0.024 | −1.3 | −1.1 | 0.60 | 0.350 | 0.320 | 0.030 |
| 42013 | 41615 | **+4.46** | 0.025 | −0.4 | +2.0 | 1.42 | 0.333 | 0.330 | 0.003 |
| 72169 | 71669 | +1.84 | 0.012 | −0.3 | +0.7 | 1.25 | 0.338 | 0.331 | 0.007 |
| 95071 | 95579 | −0.33 | 0 | −1.4 | +1.0 | 1.28 | 0.340 | 0.333 | 0.007 |
| **131251** | **130577** | **−1.03** | **0** | −0.7 | +0.7 | 1.29 | 0.336 | 0.329 | 0.007 |

Axis-1 (8 generators at p=100003, n=50000): all |z| < 1.7, ε̂ ∈ [0, 0.013], not universal.
Axis-2b (fixed n=20000): same mid-range bump shape, z<0 at the largest prime.

## Characterization — BRANCH B (universal noise floor), forced by elimination

`z_G²` fit: `log z ~ +0.225·log n`; at n_max=130577, **z_G² = −1.03** (G²_real=8.1 ≪ surrogate
99.9-pct=30.3). Branch determination (prereg §7):

- **A (universal coupling) — excluded.** Requires z rising (slope ≥+0.5) and z≥5 at n_max; observed
  slope +0.225, z_max over the whole sweep = 4.46 (<5), and **z<0 at the two largest orbits**.
- **C (generator/prime-specific) — excluded.** Requires z≥5 in some cell; **no cell reaches 5.**
- **D (underpowered) — excluded.** Requires slope ≥+0.5 or a rising swap channel; neither (swap-odd
  slope 0.000, z_odd/z_even all <2.5).
- **B (floor) — the only consistent branch.** The three decisive, df-robust facts:
  1. **Both largest orbits sit at z<0**, where the *validated* plant proves a real ε≥1.6% coupling
     would give z≥8. Neither fires.
  2. **The mid-range excursion does not persist.** z=4.46 at n=41615 would, if a real 2.4% coupling,
     scale to z≈4.46·√(130577/41615)≈7.9 at n_max. Measured: −1.03. It is an upward noise
     fluctuation, not signal — exactly what a floor produces and the plant would not.
  3. **The λ₂−λ₃ gap shrinks with n** (0.070 at n=5207 → 0.007 at n=130577), and
     dev_real/dev_surr ∈ [0.57,1.42] (centered ~1, the DRILL-01 floor ratio).

> **The `C_T` inter-coordinate coupling is bounded below ≈1.6% at n≈1.3×10⁵, for b=7, p ≤ 2¹⁷,
> across 8 prime-order curves and 8 generators, with the control fired.** A coupling below ~1.6%,
> or one switching on above 2¹⁷ / near 2²⁵⁶, is **not** excluded. This is a magnitude with its power
> and scope — **not** a closure of §X.6.

*(One literal prereg gate — the §7-B2 clause "ε̂ ~ n^(−0.5)" — does not mechanically match, because
the observed ε̂ is **pinned at 0** at the two largest n (G²_real < null mean there), i.e. *stronger*
than a clean n^(−0.5) decay, not weaker. The automated print therefore read "B*"; the manual
determination, forced by elimination above, is B. Disclosed.)*

## What this sharpens

- **Extends DRILL 01 from one prime/generator to 8×8.** DRILL 01 bounded the coupling <~2% at a single
  p=100003 orbit. This sweep shows the same across a log-spaced range of prime-order curves and
  independent generators: the "2–3% λ₂≠λ₃" the v1 master flagged as *possibly arithmetic* is the
  **estimation floor** — a universal function of `n` that decays, reproduced by the zero-coupling
  surrogate at every scale, not a generator/prime-independent geometric constant.
- **The GLM-frontier-C verdict logic would have misfired**, exactly as prereg §0 warned. `max|Tj−Tf|`
  (its statistic) *is* ~constant across generators/primes at fixed n — because the floor is a
  universal function of n — and "constant ⇒ universal geometric coupling" would have read the floor
  as the signal. The surrogate-normalized n-scaling is what separates them.

## Bearing on the GGM question

This frontier **does not move outside GGM at the tested scale.** `C_T` — the addition-rounding
covariance, a candidate concrete-arithmetic fingerprint in the one non-linear operation (point
addition) — carries **no inter-coordinate structure above ≈1.6%** that a tensor-square (independent-
coordinate) model lacks, across the sweep. The tensor law `C_T = C_1⊗C_1` holds to the measurement
floor. (Standing caveat: 239 binary orders below secp's p; a coupling switching on near 2²⁵⁶ is
untested and has zero power here.)

## Next probes (door left open, per protocol)

1. **Push n to reach below the 1.6% floor.** A new prereg extending p to 2¹⁸/2²⁰/2²⁵ reaches
   ε_detect ≈ 1%/0.5%/0.1% (prereg §5). Needs a faster orbit walk than the current O(n) modular
   inversions. Aim `‖D_odd‖_F` (the n^(−1/2)-power swap channel), not the omnibus.
2. **b ≠ 7 curves at matched n** — is even the ~1.6% floor b-independent, or does the CM (j=0) lift
   change the floor's constant? (Bounds the geometry of the floor itself, not the coupling.)
3. **The scale gap (2²⁵⁶) is §X.5 and untouched by this method.**
