# CORRECTION — `RESULT_cside_nonalgebraic_correlation_v1.md`: the null was under-dispersed by √2

**Date:** 2026-08-01
**Applies to:** `RESULT_cside_nonalgebraic_correlation_v1.md` (2026-07-31) and `cside_orbitlevel_v1.py`
**Found by:** `experiment-designer`, auditing `PREREG_cside_pooled_tilt_OOS_v1.md` (layer F2).
Independently reproduced here before adoption.
**Direction of the correction: it weakens the positive lead and strengthens the null.** Recorded under
symmetric rigor — a disliked correction and a liked one get the same treatment.

---

## 1. The defect

`cside_orbitlevel_v1.py` draws its null by `rng.shuffle(vp)` — a **free permutation** of the
`μ₃`-orbit value labels. That null leaves the surface the real data is confined to.

`c(d) = χ₂(y_{[d]G})` obeys **two** forced symmetries, not one:

- **GLV** `c(λd) = c(d)` — used by v1, correctly. Free units = the `L = (n−1)/3` `μ₃` orbits.
- **Oddness** `c(−d) = −c(d)` — **not** respected by v1's null. It is forced exactly:
  `p ≡ 7 (mod 12) ⇒ p ≡ 3 (mod 4) ⇒ χ₂(−1) = −1`, and `y_{[−d]G} = −y_{[d]G}`.

Negation descends to a map `ν` on the orbits which is a **fixed-point-free involution** (an orbit
could be `ν`-fixed only if `−1 ∈ μ₃`, impossible since `2 ∤ 3`). So `val[ν(r)] = −val[r]` identically:
the data has `L/2` free signs, not `L`. A free permutation destroys that pairing.

This is the same failure class the script's own header describes correctly and the code then does not
implement — the header says the null "preserv[es] oddness sign" and that the effective sample size is
`(n−1)/6`; the code preserves nothing of the kind and uses `(n−1)/3`.

## 2. Magnitude — √2, derived and measured

Theoretically, `sd_surface/sd_free = 2√(L−F₊−F₋) / √(2(L−2)) = √2` to within 0.02% at these `L`.

Measured (structure-only; no `c` data involved — random sign vectors on each surface):

| `p` | `L` | sd, constraint surface | sd, v1 free permutation | ratio |
|---|---|---|---|---|
| 16879 | 5702 | 152.8 | 104.5 | 1.46 |
| 17959 | 6032 | 154.6 | 110.1 | 1.40 |
| 18211 | 6044 | 156.6 | 112.1 | 1.40 |

**The error is in dispersion, not location.** The mean offset is `≈ 0.007` in `z` units. So the
mis-specified null does **not** manufacture a negative sign — it inflates `|z|` symmetrically in both
directions. A nominal `α = 0.01` against it is truly `≈ 0.024`.

## 3. What changes in the reported numbers

Every per-prime `z` in the v1 result was measured against the under-dispersed null, so every `|z|`
divides by `√2`, and the Stouffer pooling of those `z`'s divides by `√2` with them:

| v1 reported | corrected |
|---|---|
| pooled Stouffer `z = −2.64`, one-sided `p ≈ 0.004` | **`z ≈ −1.87`, `p ≈ 0.03`** |
| per-prime mean effect `z = −0.622` | **`δ ≈ −0.44`** |
| "calibration-corrected pooled `z ≈ −2.1`" | **withdrawn** (§4) |
| max per-prime `|z| = 2.39` (p=11503) | **`≈ 1.69`** |

**§2 of the v1 result — the family-wise NULL — survives and is strengthened.** The largest cell moves
from `|z| = 2.39` to `≈ 1.69`, further from the Bonferroni threshold, and "0 cells clear Bonferroni"
holds a fortiori. The 15/18 negative **sign count is unaffected** (a location fact, and the error is
in dispersion).

**§3 of the v1 result — the flagged lead — survives as a lead, at reduced strength.** It is a
`p ≈ 0.03` discovery-sample observation, not `p ≈ 0.004`. It is not withdrawn, and per the
counter-prior it is still to be chased, not buried: that is what
`PREREG_cside_pooled_tilt_OOS_v3.md` does.

## 4. Two further statements withdrawn

- **"Calibration std is 0.793 … corrected pooled `z ≈ −2.1`."** Withdrawn. The `0.793` was estimated
  from 18 draws (se ≈ 0.17, entirely consistent with 1.0), on calibration data that *also* lacked
  oddness — so it could not measure the very mis-specification at issue — and it was applied in the
  shrinking direction on an inverted rationale. The correct correction is the `√2` of §2.
- **"On pure random orbit values (known `E[T] = 0` by construction)."** False as stated.
  `E[T] = F₊ − F₋`, where `F₊ = 2` orbits are inversion-fixed and `F₋ = 2` are anti-fixed when
  `n ≡ 1 (mod 4)`. So `E[T] ∈ {0, 2}`. The magnitude is negligible against `sd ≈ 150`; the statement
  is wrong and the exact constant is now carried explicitly.

## 5. A scope correction to how the statistic was framed

v1 describes `T` as measuring "the CDH/inversion channel". That is narrower than what `T` is. Since
each `μ₃` orbit contributes three equal terms, `3T = Σ_d c(d)c(d⁻¹)`, and multiplicative Fourier
inversion on `(Z/n)^×` gives

> `3T = (n−1)·Σ_χ ĉ(χ)²`   — with `ĉ(χ)²`, **not** `|ĉ(χ)|².`

So `T` aggregates **every** character-space concentration of `c`, not only an inversion-specific one.
Oddness kills even `χ`; the real character `χ₂^{(n)}` is odd exactly when `n ≡ 3 (mod 4)`, and there it
contributes `(n−1)ĉ(χ₂)² ≥ 0` — a **forced non-negative** term. Consequences:

- A Legendre-symbol-of-index effect can only push `T` **positive**. It cannot manufacture the observed
  negative tilt; it can only **mask** one. The correction again runs against the lead, not for it.
- The two channels are separable at no cost by stratifying on `n mod 4`. The v3 prereg pre-commits to
  reporting that stratification (its OOS set splits 45/45).

## 6. Disposition

- `RESULT_cside_nonalgebraic_correlation_v1.md` is **not** edited (versioning rule, CLAUDE.md §1).
  This file is the correction of record; cite them together.
- `cside_orbitlevel_v1.py` is superseded for any future use. Its null is wrong. The replacement does
  not simulate at all: on the constraint surface the null law is exactly
  `T = (F₊−F₋) + 4(2B − M)` with `B ~ Binomial(M, ½)`, `M = (L−F₊−F₋)/4`
  (`PREREG_cside_pooled_tilt_OOS_v3.md` §2.2).
- **No grade moves on the strength of this file.** It lowers a lead and leaves a null in place; it
  creates nothing.
- Standing lesson, already in the record and re-confirmed the hard way: *a null must share the
  signal's forced symmetries.* v1's calibration control could not have caught this — its calibration
  data lacked oddness too, so it was exchangeable under the wrong null by construction. The v3 spec
  adds **C-MATCH**, a control that runs on the **real** data and can fire on a mis-specified null.
