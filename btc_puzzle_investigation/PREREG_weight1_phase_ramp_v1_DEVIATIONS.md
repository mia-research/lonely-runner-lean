# DEVIATIONS — `PREREG_weight1_phase_ramp_v1.md`

Run: `weight1_phase_ramp_v1.py` (gate + run modes). Exact int/Fraction signal path (point/eis/χ₂);
float carve-out = ζ₃/exp/arg in the isotype DFT and phase (spec §8).

---

## D1 — the covariant control is the PURE `(1,1)` projector, not equal-weight (spec §3c firing check)

**Spec §3c** proposes the equal-weight `M` (`w_{j,s}=1 ∀`) as the μ₆-covariant control that should give
`G≈0`. **That is wrong:** the isotype DFT collapses `Σ_{j,s} A_{j,s} = 6·φ₀(P)` (sum over `j` of `ζ₃^{-jm}`
= 3·[m=0]; over `s` of `(−1)^{-st}` = 2·[t=0]), and `φ₀` is NOT μ₆-equivariant, so equal-weight gives
`G=0.59` (p=163), not ≈0. The correct covariant control is the **pure `(1,1)` projector**
(`w_{1,1}=1`, rest 0): `Φ=arg(A_{1,1})` transforms by the single `(1,1)` character, so after removing the
`(1,1)` ramp `ℓ(g)=120°m+180°t` the circular variance is `G=0.0000` (p=163) — confirming both the ramp
and the gate discriminator. Used pure-`(1,1)` as the firing control.

## D2 — p=349 (p≡1 mod4) is INADMISSIBLE: the weight-1 `[−1]`-odd channel structurally VANISHES

**Spec §6** froze the primary ladder `{163, 349}`. **p=349 is `p≡1 mod4`**, where `χ₂(−1)=+1`, so
`φ₀([−1]P)=φ₀(P)` — `φ₀` is `[−1]`-invariant. Then `A_{j,1}=Σ_{m,t}ζ₃^{-jm}(−1)^{-st}φ₀ = 0` for all `j`
(the `Σ_t (−1)^{-t}=0`): **the `s=1` (`[−1]`-odd, weight-1) isotypes are identically zero.** The readout is
`arg(0)`=noise (`G=1.0` for BOTH pure and oblique). So the weight-1 `[−1]`-odd phase channel, via this
public per-point proxy, **exists only at `p≡3 mod4`** (secp's class), not at `p≡1 mod4`. This is a
structural fact (it mirrors M4: `V(a)` is `[−1]`-even/real at `p≡1 mod4`), not a tuning failure.

**Correction.** The run is restricted to the **secp class `p≡7 mod12` (`p≡3 mod4`)**, where the gate is
admissible (p=163: oblique `G=0.056 ≥ 0.05` PASS, pure `G=0`). `p≡1 mod12` primes are reported as
inadmissible for this channel, not as a bound. The secp-class ladder used: `163, 823, 907, 991, 1051,
1303` (163 primary + 5 OOS stratum-S primes from `RESULT_n1_120deg_exact_v1.md`).

## D3 — graded-plant `ε_min` reported analytically, not swept

**Spec §4** graded plant (250 trials/ε) not run. The HARD plant (full d-linear ramp `Φ*(d)=2πd/n`)
**fires at every prime** (`S=1.0`), confirming the pipeline detects a real ramp (power present). The
detectable amplitude is reported at the §5 analytic floor `ε_min≈2.6/√(n−1)` (≈0.20 at p=163, ≈0.07 at
p≈1300), not from the empirical sweep. Disclosed.

## D4 — secondary null (isotype-phase randomization) and full OOS not run

The primary d-label permutation null (B=2000) is a clean null on all 6 secp-class primes; the secondary
confirmatory null and a separately-drawn OOS ladder were not run (the primary ladder already includes 5
OOS stratum-S primes). Disclosed; the bounded-null claim rests on the primary null + the fired plant.

---

## Not deviations
- `φ₀`, oblique `M` weights, `a*=1`, `B=2000`, `G_min=0.05` as frozen.
- Gate run BEFORE the statistic (admissibility first). `d` never in the `Φ` path (construction audit).
- The gate's marginal `G=0.056` at p=163 (oblique barely breaks μ₆) is noted, not a deviation — the
  channel is genuinely weak, which the plant-fires-but-real-data-null result reflects.
