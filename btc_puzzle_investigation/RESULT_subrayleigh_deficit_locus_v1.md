# RESULT — the sub-Rayleigh deficit: mechanism REFUTED, locus FOUND, and it is every character

**Date 2026-07-20.** Executes `PREREG_subrayleigh_deficit_locus_v1.md` (frozen pre-run).
Artifacts: `subrayleigh_deficit_locus_v1.py` / `.log` / `_srd_rows/*.json`; deviations in
`PREREG_subrayleigh_deficit_locus_v1_DEVIATIONS.md`.
Scope: enumerable model curves `E : y²=x³+7` over `F_p`, 7 primes `163 … 2089`.
`p = 2²⁵⁶−2³²−977` is not enumerable; **nothing here transfers to it.**

Target: the `0.06–0.10%` deficit in `mean|U(a₀,b,c)|` from
`RESULT_harmonic_support_pattern_v1.md`. Because `Σ|U|² = p²(n−1)` is pinned exactly, the whole
effect is one scalar, `M1 = mean r`, `r = |U|/√(mean|U|²)`, with `M2 = 1` by construction.

**All controls fired:** C-M2, C-EQ (integer pairing exact; relative equivariance `≤7.8e−13`),
C-X (`Σ|U|⁴` float-FFT vs exact-integer, `rel ≤ 1.4e−15`), P1, P2, P3 (`H[Δ]` **integer-identical**
to `O(n⁴)` brute force at `(13,7)` and `(43,31)`), P4 (`E_plant = 13.6–15.5`), P5.

---

## 1. The deficit is real, and it is NOT the value-multiset artifact

**MC2 — the primary control — does not remove it.** MC2 permutes the character's values, preserving
the exact multiset (each non-trivial `n`-th root once) and hence `Σ_d g(d) = −1` and `U(0,0) = −1`
exactly, destroying only the `d`-alignment.

| `p` | deficit vs MC1 | deficit vs MC2 | `z(M1)` vs MC2 |
|---|---|---|---|
| 163 | 0.358% | 0.351% | −3.78 |
| 211 | 0.046% | 0.045% | −0.63 |
| 349 | 0.149% | 0.145% | −3.32 |
| 433 | 0.129% | 0.131% | −4.35 |
| 577 | 0.096% | 0.097% | −3.60 |
| 991 | 0.119% | 0.118% | −8.06 |
| 2089 | 0.098% | 0.098% | **−13.27** |

MC1 and MC2 agree to the third decimal at every prime. **Pooled Stouffer `Z(M1) = −13.99`, sign
test 7/7 negative.** Sampling-without-replacement is excluded as the cause — this was the single
most likely benign explanation and it is now ruled out, not assumed away.

---

## 2. The pre-committed mechanism is REFUTED

The frozen prediction was: lower `l¹` at fixed `l²` ⇒ magnitudes more unequal ⇒ **excess fourth
moment**, carried by quadruples where the group law and naive coordinate addition coincide
(`Δ = d₁+d₂−d₃−d₄ ≡ 0`). Quantitatively frozen: `δlog M4 ≈ −4.4·δlog M1`, i.e. a `+0.35%` `M4`
excess.

**Arm 2 — no `M4` excess.** Pooled `Z(M4) = +0.95`; sign test **3/7** positive. Only `p=163`
(the smallest prime) showed `z = +4.37`.

**Arm 3 — no `Δ=0` enrichment.** `E = H_off[0]/(N_off/n)` against the label-permutation control:

| `p` | 163 | 211 | 349 | 433 | 577 | 991 | 2089 |
|---|---|---|---|---|---|---|---|
| `E` | 1.88 | 1.10 | 1.37 | 0.59 | 0.57 | 0.92 | 1.19 |
| `z` vs control | **+3.0** | +0.3 | +2.0 | −2.7 | **−4.1** | −1.1 | **+3.0** |

The sign **alternates**; there is no consistent direction. The `E = 1.88` at `p=163` is a
small-prime chance pattern of exactly the kind the drill rule ("retest out-of-sample before naming
a zero") exists to catch — and so is the `−4.1` at `p=577` in the opposite direction.

**Note that Arms 2 and 3 are one test, not two.** C-X verifies
`Σ|U|⁴ = p²·Σ_Δ H[Δ]e_n(a₀Δ)` to `1.4e−15`, so the quadruple histogram *is* the fourth moment.
They agree because they are the same quantity.

**My derived candidate cause is refuted with it.** I had derived that `H[Δ]` is forced constant on
orbits of `⟨λ,−1⟩` (negation sends `Δ→−Δ`; GLV sends `Δ→λΔ`), making `Δ=0` the unique fixed point,
and that at fixed group-law sum `S` the chord relation `x₁+x₂ = m²−x_S` makes the slope involution
`m ↦ −m` preserve the x-sum automatically. **The data say this is not what carries the deficit.**

---

## 3. The locus IS found: the deficit lives in the low tail

Arm 1 decomposes the deficit into three zones that sum to it **by construction**
(`mean_char − mean_null = −∫(F_char−F_null)dt`), so this arm always localizes.

| `p` | LOW (`r<0.5`) | MID (`0.5–1.5`) | HIGH (`r>1.5`) |
|---|---|---|---|
| 349 | **+137.5%** | −64.2% | +26.7% |
| 433 | **+136.4%** | −79.0% | +42.6% |
| 577 | **+166.5%** | −140.9% | +74.4% |
| 991 | **+129.3%** | −61.3% | +32.0% |
| 2089 | **+146.0%** | −89.4% | +43.4% |

(`p=211` is uninformative here — its deficit is `z=−0.63`, i.e. no signal to decompose.)

**Reading:** the deficit is carried by the **LOW tail** (dominant) *and* the **HIGH tail**
(secondary), partly offset by an excess in the MIDDLE. Both tails are sub-Rayleigh: the character
has more near-zero harmonics *and* fewer very large ones (the latter consistent with the Weil
ceiling, which random targets do not obey).

**Direct count of the low tail** — an ~8% excess of near-zero harmonics, stabilizing:

| `p` | `#{r<0.10}` char vs MC2 | `#{r<0.05}` char vs MC2 |
|---|---|---|
| 349 | +14.3% | +6.2% |
| 433 | +7.8% | +14.1% |
| 577 | +9.2% | +7.6% |
| 991 | **+7.8%** | +8.7% |
| 2089 | **+7.9%** | +8.0% |

**This also explains why Arm 2 came back null, and the two arms are consistent rather than
contradictory:** `r⁴ ≈ 0` for `r < 0.1`, so a deficit carried by the low tail is *invisible* to the
fourth moment. The inequality increase is at the bottom of the distribution, where `M4` has no
sensitivity. The frozen `δlog M4 ≈ −4.4·δlog M1` chain assumed the extra inequality would appear in
the upper moments; it does not.

---

## 4. It is EVERY character, not `a₀`

Arm 4, over sampled orbit representatives of `⟨λ,−1⟩` (distinct configurations, not rows):

| `p` | orbits | sampled | with `z < −3` | median `z` |
|---|---|---|---|---|
| 349 | 52 | 24 | 10/24 | −2.50 |
| 433 | 66 | 24 | 15/24 | −3.78 |
| 577 | 102 | 24 | 14/24 | −3.44 |
| 991 | 168 | 24 | **24/24** | −6.77 |
| 2089 | 357 | 24 | **24/24** | **−12.58** |

At the two largest primes it is unanimous. **The finding is "characters are sub-Rayleigh relative to
random targets" — a property of the curve + character system, not of `a₀ = 1`.** The smaller primes
show fewer firings because per-character power is lower there, not because those characters differ.

`P5` (forced): an orbit-mate `a = λa₀` reproduces `a₀`'s `mean r` to `≤2.5e−16` — the equivariance
is exact, as required, and contributes zero evidence.

---

## 5. Scaling `[UNDERPOWERED — pre-declared]`

Measured slope `s = −0.163` against the four pre-committed candidates only (no free exponent was
fit): `1/log p` (`−0.15`, `Δ=0.013`), `const` (`Δ=0.163`), `1/√p` (`Δ=0.337`), `1/n` (`Δ=0.837`).

**`1/√p` and `1/n` are excluded; `const` vs `1/log p` cannot be separated** — they differ by
`0.15 ≈ 1σ_s`, which the spec declared underpowered *before* the run. No decay law is claimed.

---

## 6. What this run establishes, with scope

- **`[EMPIRICAL, 7 primes]`** The deficit is real (`Z = −13.99` pooled, 7/7), survives the exact
  value-multiset control, is carried by an **~8% excess of near-zero harmonics** plus a thinner
  high tail, and holds for **every character**, not a distinguished one.
- **`[REFUTED]`** The fourth-moment / `Δ=0` coincidence mechanism, including the slope-involution
  derivation. This is a positive result: it names what the deficit is *not*, and the refutation was
  pre-committed with a quantitative threshold rather than assessed after the fact.
- **Bounds inherit:** model curves only, `p ≤ 2089`, these statistics, these controls. No decay law.
  Nothing about `p = 2²⁵⁶−2³²−977`. No ECDLP, extraction, or security claim.

---

## 7. Next probe (named now, not chosen post hoc)

There is a **second exact conservation** that the nulls do not satisfy, and it acts along the axis
Arm 4 just showed is the relevant one. For each fixed frequency `(b,c)`:

> `Σ_{a mod n} |U(a,b,c)|² = n·Σ_d |e_p(bx_d+cy_d)|² = n(n−1)` — **exact**, since
> `Σ_a e_n(a(d−d')) = n·[d=d']`.

So at every frequency the `n` character rows share a fixed budget, of which the trivial row
`|U(0,b,c)|²` (the untwisted sum, `≤(2√p+1)²` by Weil) takes a piece. A random target is a single
draw and satisfies no such per-frequency constraint. **The decidable test:** whether the near-zero
excess at row `a₀` is compensated by an excess of *large* `|U(a,b,c)|` at other `a` for the same
`(b,c)` — i.e. whether the low tail is the shadow of this row-wise conservation. That is a
different statistic from the five frozen here (it is a joint statistic over `(a,b,c)`, not a
marginal over `(b,c)` at fixed `a`) and needs its own prereg.
