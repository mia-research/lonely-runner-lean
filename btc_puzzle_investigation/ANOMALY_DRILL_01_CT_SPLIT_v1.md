# ANOMALY DRILL #1 — the `C_T` lifted degeneracy (§X.6)  — 2026-07-17

**Protocol.** An Anomaly Drill reports the **mathematical characterization** of an anomaly. It
reports magnitudes; it may **not** convert a magnitude into a verdict ("safe / generic / bounded /
nothing here"). A bound is a statement about *size*, and structure lives in the *symmetry type,
eigenvector and subspace* — so every drill must say **where** the object lives, not merely how big
it is. A drill ends in one of: a sharper law, a bounded magnitude **with its power**, or a named
next probe. Never in a closure.

**Scripts:** `_anomaly_drill_ct_split_v1.py` (first pass, defective — see below),
`_anomaly_drill_ct_split_v2.py` (matched null). Exact integer transition counts; float only in
`eig`/log-likelihood (analytic sizes, no key in path).

---

## The anomaly as posed

`C_T` is the 9×9 transition operator on the addition-rounding state `(c₁,c₂)∈{−1,0,1}²`. The
tensor law `C_T = C_1⊗C_1` predicts the 9 eigenvalues are the pairwise products of `C_1`'s
`{1,⅓,1/9}` — a spectrum containing an **exactly degenerate pair at ⅓**, with eigenvectors `v⊗u`
and `u⊗v`. v1 master reported `λ₂=0.339 ≠ λ₃=0.328` (~3%) and asked: genuine coupling, or
finite-orbit noise?

**Why this is the right place to drill.** A degenerate pair is the most perturbation-sensitive
object in a spectrum: degenerate perturbation theory gives `δλ ~ ‖perturbation‖` at **first**
order, not second. So `λ₂−λ₃` is the highest-gain probe of an inter-coordinate coupling available
in this operator. Whatever it says, it says loudly.

## What the drill found

### 1. The tensor law's block-level predictions are CONFIRMED, at precision v1 did not claim

At `p=100003` (full orbit, `n=99666`):

| prediction of `C_T = C_1⊗C_2` | predicted | measured | agreement |
|---|---|---|---|
| degenerate-block trace `λ₂+λ₃` | `2/3 = 0.666667` | `0.666742` | **7.5e-5** |
| `Tr(S∣block)` where `S:(c₁,c₂)→(c₂,c₁)` | `0` exactly | `+0.0289` | ≈0 |

The second row is the structural one. In the exact tensor case `S` **swaps** `v⊗u` and `u⊗v`, so
`S∣block = [[0,1],[1,0]]`, eigenvalues `±1`, trace `0`. Measured `⟨v₂,Sv₂⟩+⟨v₃,Sv₃⟩ = +0.029`.
**The degenerate block decomposes into exactly one swap-EVEN and one swap-ODD channel — as the
tensor law requires.** Across all six small prime-order curves tested, `⟨v₂,Sv₂⟩` and `⟨v₃,Sv₃⟩`
carried **opposite signs 6/6** with sum ≈0. This is not evidence of a coupling; it is the tensor
structure being visible in the eigenvectors.

### 2. The ~3% splitting is at the estimator's floor — the control fires

A **matched surrogate** — two coordinates evolving *independently* with exactly the measured
marginals `T1,T2` at the same length `n`, i.e. **zero coupling by construction** — reproduces the
effect:

| statistic, `p=100003`, `n=99666` | real | surrogate (no coupling) | z |
|---|---|---|---|
| `max∣C_T − C_1⊗C_2∣` (v1's estimator) | 0.02751 | 0.02256 ± 0.00311 | **+1.59** |
| `δ = ∣λ₂−λ₃∣` | 0.01126 | 0.01060 ± 0.00500 | **+0.13** |
| swap-asymmetry of `C_T` | 0.02802 | 0.03229 ± 0.01161 | −0.37 |

Scaling across six prime-order curves (`n = 1092…5850`): `dev_real ~ n^(−0.596)`,
`dev_surrogate ~ n^(−0.584)` — **the same exponent**. Extrapolating the small-`p` fit to
`n=99666` predicts ≈0.022; measured 0.0275. The `p=100003` value is where the noise scaling puts it.

### 3. A sharpened estimator finds nothing either — and this is the load-bearing test

`max∣·∣` over 81 entries is a maximum of noisy quantities: upward-biased, low power. Replacing it
with the **pooled G² likelihood-ratio test** for the factorization (within each source state, are
the two next-coordinates independent? 9 tables, 16 df, exact integer counts):

```
REAL       G² =  16.803   df=16   p = 0.40
SURROGATE  G² =  18.096 ± 6.917   (8 draws, independent by construction)
z(real vs surrogate) = −0.19
```

Decomposing the deviation `D = C_T − C_1⊗C_2` into swap channels (the two directions the
degeneracy actually splits along, i.e. aiming the statistic where the structure would live):

```
‖D‖_F = 0.04174     ‖D_even‖_F = 0.02322  (surrogate 0.02747 ± 0.00779,  z = −0.55)
                    ‖D_odd‖_F  = 0.03469  (surrogate 0.03106 ± 0.01080,  z = +0.34)
```

Neither channel departs from a coupling-free surrogate.

---

## Characterization (the output)

**The anomaly dissolves into a sharper law, not into "nothing here."** v1 stated `C_T ≈ C_1⊗C_1`
with an unexplained ~2–3% residual. The drill's finding is the opposite of a null: **the tensor
factorization holds to the measurement floor, and its block-level consequences hold far more
tightly than v1 claimed** — the degenerate-block trace to `7.5e-5`, and the swap-even/odd
decomposition of the degenerate block confirmed in the eigenvectors. `C_T` is a cleaner tensor
square than the document said.

**The magnitude, stated as a magnitude with its power.** With the pooled 16-df test at `n≈10⁵`, a
coupling is detectable at effect size `≈ √(30/n) ≈ 1.7%`. Measured: `p=0.40`, `z=−0.19`. So:

> **Any inter-coordinate coupling in `C_T` is below ≈2% at `n≈10⁵`, for this orbit, this
> generator, this prime, and these two estimators.** Probing 0.1% requires `n ~ 10⁷`.

**What this does NOT say** (per protocol, and per the scale banner): it does not say the coupling
is zero; it does not close §X.6; it says nothing about `p≈2²⁵⁶`. `p=100003 ≈ 2¹⁷`. A coupling that
switches on near `2²⁵⁶` would not show here, and this drill has no power against that hypothesis at
all.

## Defect found in this drill's own first pass (recorded, not hidden)

`_anomaly_drill_ct_split_v1.py` fit `∣δ∣ ~ p^(−0.36)` from **three** points, two of which had
orbits of `n=146` and `n=3353` — a 9×9 operator estimated from 146 transitions is noise, and those
rows dominated the fit. The `p%3==1` filter had silently reduced 8 candidate primes to 3. Had the
drill stopped there, `p^(−0.36)` (neither `−0.5` noise nor `0` constant) would have read as an
*intermediate, therefore interesting* exponent. It was an artifact of two junk rows. **The fix that
mattered was the matched surrogate**, which requires no scaling fit at all.

## Next probes (§X.6 remains OPEN, now with a specified attack)

1. **Aim at the swap-odd channel, not the whole matrix.** The degeneracy splits along swap-even /
   swap-odd. `‖D_odd‖_F` is a 1-dim-targeted statistic with `n^(−1/2)` power instead of a max over
   81 cells. Push it to `n ~ 10⁶–10⁷` (needs a faster orbit walk; the current build is `O(n)`
   modular inversions).
2. **Vary the free parameters** before believing the bound: multiple generators per prime,
   multiple primes at fixed `n`, and `b ≠ 7` curves. A bound measured at one generator on one orbit
   is one measurement.
3. **The real gap is scale.** Every number here is at `2¹⁷`. Nothing in this drill constrains
   `2²⁵⁶`. That is §X.5, and it is not addressable by this method.

**Status for the next compile:** §X.6 → `bounded-by ANOMALY_DRILL_01 (<2% at n≈10⁵, p=100003, two
estimators, control fired)`. **Not** `resolved`. The frontier stays live; the tensor law gets
promoted from `≈` to a stated precision.
