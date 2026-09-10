# The 248/1599 factor: where it lives, and where it does not

2026-09-10. Follows `GRID_AND_PASSAGE_v1.md` §5. Scripts
`experiments/n8/ok_resonance_factor_v1.py`, `ok_pm1_families_v1.py`. All `|G|` values are
exact `Fraction`; the only floats are **checks on** exact rationals, never their source
(float audit `ok_float_audit_v1.py`).

`E* = (2,6,7,8,10,13,14)` sits five speeds on the grid `2·T₁` with `7, 13` off it. A generic
two-runner deviation would give `(3/4)²·|G(2·{1,3,4,5,7})| = 369/8960`; the actual is
`93/14560`. Exact ratio **`248/1599`**. This file asks what carries it.

---

## 1. Attribution by perturbation  `[PROVED — exact]`

The off-grid speeds carry exactly two relations to the grid: **`2·7 = 14`** (height 2) and
**`6 + 7 = 13`** (height 1). Break them by an infinitesimal perturbation (values stable at
`1/48, 1/96, 1/192`):

| perturbation | `\|G\|` | as fraction of generic |
|---|---|---|
| none — `E*` itself | `93/14560` | `248/1599 = 0.1551` |
| speed 13 (breaks `6+7=13`) | `69/2240` | `0.7480` |
| speed 7 (breaks **both**) | `1683/58240` | `0.7017` |
| **both 7 and 13** | `896783/22274560` | **`0.9776`** |

> **Breaking the off-grid speeds' resonances recovers 97.8% of the generic value.** The
> factor is carried by those resonances and by nothing else.

Note they are **not multiplicative**: the two single-break figures do not compose to
`0.1551`, because `6 + 7 = 13` involves both off-grid speeds at once.

## 2. `E*` is the unique minimiser on its grid  `[PROVED — exhaustive]`

Over **all 490** admissible pairs `(x,y)` added to the grid `{2,6,8,10,14}` (`gcd 1`, a
multiple of 8 present, `x,y ≤ 40`):

| rank | pair | `\|G\|` |
|---|---|---|
| 1 | **`(7,13)` — `E*`** | `93/14560 = 0.006387` |
| 2 | `(11,17)` | `5/476 = 0.010504` |
| 3= | `(11,22)`, `(13,22)`, `(19,22)` | `31/2464 = 0.012581` |

`E*` wins by 64%. And the runner-up shows the pattern: `6 + 11 = 17` is the same chain
shape, but `11` has no doubling into the grid, where `2·7 = 14` does.

**Relation count does not order this.** Mean `|G|` by 3-term relation count is
**non-monotonic**: 3 → `0.0405` (n=266), 4 → `0.0367` (n=160), 5 → `0.0434` (n=44),
6 → `0.0208` (n=20). Counting relations is the wrong statistic.

## 3. Every height-1 family has an exact rational value  `[PROVED — new]`

`AB_SPLIT_v1` §A3 gives closed forms for support-2 families. They exist at **every**
support. With `f̂(k) = −sin(πk/4)/(πk)`, a height-1 resonance (all coordinates `±1`,
support `k`) contributes `C_k = 2(3/4)^{7−k}·Σ_{m≥1} f̂(m)^k`, and

    Σ_{m≥1} f̂(m)^k = (−1)^k π^{−k} Σ_{m≥1} sin^k(πm/4)/m^k.

Expand `sin^k` into its finite Fourier sum: for `k` odd it is a combination of
`sin(jmπ/4)` with no constant term; for `k` even, of `cos(jmπ/4)` plus a constant. Both
`Σ_m cos(mx)/m^{2n}` and `Σ_m sin(mx)/m^{2n+1}` are Bernoulli polynomials — rational
multiples of `π^k` — and `ζ(even)` likewise. **The `π^k` cancels every time.**

| `k` | `Σ f̂(m)^k` | contribution `C_k` |
|---|---|---|
| 2 | `3/32` | `729/16384` |
| 3 | `−1/64` | `−81/8192` |
| 4 | `5/1536` | `45/16384` |
| 5 | `−67/98304` | `−201/262144` |
| 6 | `3/20480` | `9/40960` |
| 7 | `−3007/94371840` | `−3007/47185920` |

Signs alternate and the magnitude falls by roughly `4–5×` per support level. Checked
numerically to seven places (the `k = 2` check is limited by the `Σ1/m²` tail, not by the
value).

## 4. The sharp negative: low height is not the carrier  `[PROVED]`

At `E*` the deficit to explain is `ACT − GEN = −579/16640 = −0.034796`. The two named
lowest-height families evaluate exactly:

    2·7 = 14      (support 2)  →  (1/16)(3/4)^5      = +243/16384 = +0.014832
    6 + 7 = 13    (support 3)  →  2(−1/64)(3/4)^4    =  −81/8192  = −0.009888
                                              sum    =  +81/16384 = +0.004944

> **Wrong sign, and 14.2% of the magnitude.** The two lowest-height resonances at the
> extremum push `|G|` *up*, not down.

So §1 and §4 are both true and they say different things: the factor belongs to the
resonances involving `7` and `13` **collectively**, and **not** to the low-height ones.
This sharpens `WHERE_THE_PROOF_IS_v2` §4a — there the height minimum was found to be
"right in direction, nearly vacuous" because `h = 1` is generic at 98.1%; here, at the
extremum itself, the lowest-height terms point the **opposite** way. Height is not merely
a weak discriminator; as a signed quantity it is misleading at the very configuration the
whole problem turns on.

## 5. Ledger

`[PROVED — exact]` §1 perturbation table and the 97.8% recovery; §2 exhaustive minimiser
search over 490 pairs and the non-monotonic relation-count means; §3 the closed-form
argument and the six values; §4 the two contributions and the deficit.
`[EMPIRICAL]` nothing here — every number is an exact rational.

`n = 8` is **not proved.** What is settled: the extremum's deficit is a property of the
off-grid speeds' resonance with the grid (§1), it is not readable off relation counts (§2)
or off low-height Fourier terms (§4), and the height-1 families — the numerous ones — are
now all exactly computable (§3), which removes them as a source of uncertainty rather than
as a source of the deficit.
