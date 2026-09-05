# RESULT — the incomplete character sum at 2^128, first-order test: SCOPED NULL with a measured power floor

**Date:** 2026-08-01. **Script:** `incomplete_sum_2p128_firstorder_v1.py`.
**Grade:** `[EMPIRICAL — SCOPED NULL]`. The channel is **not** closed; §4 states what is untouched.

---

## 0. The object

`T(d₀) = Σ_{i<W} χ₂(x_{[d₀+i]G})` on secp256k1, `d₀` at the `2^128` scale.

Purely curve-native — no GLV, no lattice, no Voronoi coordinate, no covariate. In scope: it tests
how the **curve converts a bounded integer neighbourhood into points**, and the `d₀` are constructed
here, so nothing depends on how any scalar was selected.

**Why this before any covariate.** Every covariate test asks "does `T` correlate with X". If `T` is
distributed as an iid sum, every such correlation is bounded before you look; if it is not, that is
the finding and no covariate was needed. The regime is open precisely because complete-sum bounds
are vacuous here: Pólya–Vinogradov completion costs `√p·log p ≈ 2^128·256`, which exceeds `W` by
`~2^128`.

## 1. The null

**Marginal-exact block shuffle.** Pool every observed readout across all intervals, shuffle globally,
re-block into `M` intervals of width `W`. This preserves the empirical marginal of `χ₂(x)` **exactly**
— a global readout bias cannot manufacture a result — while destroying **within-interval**
correlation, which is what "the sequence is not random here" means.

## 2. Result

`M = 200` intervals, `W = 256`, `d₀ ∈ [2^127, 2^128)`, `R = 400` permutations:

| statistic | observed | exact perm p |
|---|---|---|
| S1 `Var(T)` | 9 338 800 | 338/401 |
| S2 `max|T|` | 44 | 313/401 |
| S3 `mean(T)` | 460 | 401/401 — **forced, see §3** |
| S4 lag-1 autocorrelation | −182 | 171/401 |

**Null on every live statistic.**

**C-MARGINAL:** readout balance `+1 × 25830`, `−1 × 25370` over 51 200 points — an excess of 460,
about `2.0σ` of `√51200 ≈ 226`. Reported, within noise, not pursued.

## 3. Measured power — and a forced statistic of my own

**C-PLANT power curve** (each interval's tail forced to a constant, i.e. injected within-interval
correlation):

| tail forced | S1 `Var(T)` | S4 lag-1 |
|---|---|---|
| 50% | **1/401 FIRES** | **1/401 FIRES** |
| 25% | **1/401 FIRES** | **1/401 FIRES** |
| 12.5% | **1/401 FIRES** | **1/401 FIRES** |
| 6.25% | **1/401 FIRES** | **1/401 FIRES** |
| 3.1% | 62/401 | **1/401 FIRES** |
| 1.6% | 279/401 | 44/401 |

> **POWER: detects within-interval correlation affecting ≳3% of the interval (lag-1), ≳6% (variance).
> BLIND below ~1.6% at `W = 256`.**

**⚠ S3 was mis-specified — by me.** `mean(T) = Σ` of the whole pool, and shuffling a pool preserves
its sum, so S3 is **exactly permutation-invariant**: all 20 null draws returned 460, identical to the
data. Zero information, no sample size helps. This is the **6th** logged forced-statistic instance and
the first one I authored — the same defect class I had just flagged in another spec (a statistic
dominated by a permutation-invariant term). The pre-screen has to be run on one's own specs too.

## 4. Scope — what is NOT closed

- **`W = 256` only.** The power floor scales with `W`; wider intervals probe different structure.
- **One readout** (`χ₂(x)`). `χ₃(x)`, `χ₆(x)`, sextant, and `y`-based readouts untested here.
- **One statistic family.** Spacings, higher-order correlations, the Katz–Sarnak family and
  small-ball statistics on `T` are untouched.
- **The pointwise inversion channel at `2^128` is untouched and remains the record's open item:**
  `Σ_i χ₂(x_{[d]G})·χ₂(x_{[d⁻¹]G})`. This is the non-algebraic map that survives the Weil closure;
  it was settled only at `p ~ 10⁴`. Note the *interval-level* version (`T(d₀)` vs `T(d₀⁻¹)`) is a
  different and much weaker object — inversion scrambles, so `(d₀+i)⁻¹ ≠ d₀⁻¹+i` and the second
  interval is merely at a pseudo-random location.
- **One scale band.** `d₀ ∈ [2^127, 2^128)` only.

Per the counter-prior, a scoped empirical null bounds a statistic at a scale and does not close a
channel. This one is offered as exactly that.
