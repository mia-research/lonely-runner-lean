# RESULT — the per-harmonic profile of `|U(a₀,b,c)|`: Rayleigh at `π/4`, with a measured sub-Rayleigh deficit

**Date 2026-07-20.** Executes `PREREG_harmonic_support_pattern_v1.md` (frozen pre-run).
Artifacts: `harmonic_support_pattern_v1.py` / `.log`; deviations in
`PREREG_harmonic_support_pattern_v1_DEVIATIONS.md`.
Scope, up front: enumerable model curves `E : y²=x³+7` over `F_p`, `p = 163 … 2089`, 7 primes.
`p = 2²⁵⁶−2³²−977` is not enumerable and **nothing here transfers to it** — every object below
requires a full group sum over all `d`.

**Question this addresses.** Whether the `0.93–0.96` joint-`(x,y)` alignment is carried by a few
"active" harmonics sitting above "starved" sectors — i.e. whether there is an active/starved split
for a basis transformation to isolate.

---

## 0. Why the question is well posed, and what the per-harmonic quantity is

With the phase-only aligned readout `F̂ = U/|U|` there is **no cancellation**, so

> **`Corr(a₀) = (1/(n−1)) · Σ_{(b,c)∈S} |U(a₀,b,c)|`**

verified both ways (point-space reconstruction vs direct sum) to `rel ≤ 2.3e−16` at all 7 primes
(C1). **The alignment is an `l¹` norm over the harmonics, and the per-harmonic contribution is the
exact nonnegative number `|U(a₀,b,c)|`.** So "active vs starved" is a decidable statement about the
distribution of these numbers — which no sector total can see.

---

## 1. The measured profile `[EMPIRICAL, 7 primes]` — Rayleigh, at `π/4`

| `p` | top1% mass | floor top1% | ratio | `N_eff/|S|` | `max/√p` |
|---|---|---|---|---|---|
| 163 | 0.0274 | 0.0265 | 1.033 | 0.7805 | 3.047 |
| 211 | 0.0263 | 0.0266 | 0.989 | 0.7851 | 3.147 |
| 349 | 0.0266 | 0.0266 | 1.001 | 0.7835 | 3.250 |
| 433 | 0.0266 | 0.0266 | 0.999 | 0.7836 | 3.049 |
| 577 | 0.0268 | 0.0266 | 1.007 | 0.7840 | 3.404 |
| 991 | 0.0267 | 0.0266 | 1.005 | 0.7836 | 3.412 |
| 2089 | 0.0268 | 0.0266 | 1.007 | 0.7839 | 3.549 |

**There is no active/starved split in this basis.** The top 1% of harmonics carry 2.7% of the
alignment — `2.7×` uniform, and that is *exactly* the value the diffuse floor gives (ratio
`0.99–1.03` at every prime). The same holds within each `χ₃` sector separately (`top1% = 0.0270,
0.0275, 0.0273` at `p=163`), so this is a **within-sector** statement, not a re-measurement of the
known `1/6` equipartition.

**The positive identification.** `N_eff/|S| = 0.7805 → 0.7839`, converging to
**`π/4 = 0.785398`** — the exact value for Rayleigh-distributed magnitudes (complex-Gaussian
coefficients), for which `E|U|/√(E|U|²) = √π/2 = 0.8862`. **The harmonic profile is Rayleigh.**
That is a sharp law, not an absence: it says the alignment is an aggregate of `~p²` harmonics each
at `≈0.8√p`, with the shape fixed by the Gaussian ensemble.

**Consistent with the ceiling (forced, F2).** `max/√p` climbs `3.05 → 3.55` against the KS/Weil
ceiling `4+1/√p`. Random targets are *not* bound by it and exceed it (`max = 4.03√p` at `p=2089`).

---

## 2. Arm B — the pattern reduces to one scalar, and it is a **deficit**

**Exact conservation (forced, zero evidence, verified to machine zero).**
`Σ_{b,c}|U|² = p²(n−1)` — **identically for the character and for every random unit-phase target**
(`|char − rand|/pred ≤ 1.3e−16`). The `l²` budget is fixed, and it is *basis-invariant*: any unitary
change of basis on the frequency space preserves it.

Because the denominator is pinned, `N_eff/|S| = (mean|U|)²/mean(|U|²)` differs from the null
**only** through `mean|U|` — i.e. through `Corr(a₀)` itself. The Arm-B "pattern statistic" is
therefore one scalar, and its sign is the finding:

| `p` | `N_eff/|S|` char | null mean | null sd | deviation | `mean|U|` deficit |
|---|---|---|---|---|---|
| 163 | 0.78054 | 0.78621 | 0.00152 | **−3.7 σ** | 0.097% |
| 349 | 0.78345 | 0.78567 | 0.00065 | **−3.4 σ** | 0.070% |
| 577 | 0.78403 | 0.78561 | 0.00042 | **−3.8 σ** | 0.058% |
| 991 | 0.78363 | 0.78549 | 0.00023 | **−8.1 σ** | 0.089% |
| 2089 | 0.78391 | 0.78544 | 0.00011 | **−13.9 σ** | — |

**The character's harmonics are on average slightly *smaller* than a random target's** — a `0.06–0.10%`
deficit, one-directional at all 7 primes, with significance growing in `p` (the deficit shrinks slower
than the null spread). This is the opposite direction from an "active harmonic": the true character
is very slightly **sub**-Rayleigh, not super-Rayleigh.

Two candidate causes are **excluded** numerically: the `(0,0)` exclusion (`|U(0,0)|²` is `1` for the
character vs `~n` for random — a `2.3e−7` relative effect, four orders too small), and the ceiling
(which bounds the max, not the mean). **The deficit is unexplained and is the one live magnitude
this run produces.**

**The active *set* is not shared.** Top-5% support Jaccard between the character and random targets
is `0.0256 ± 0.0003`, and chance for two independent 5% subsets is `0.05/1.95 = 0.02564` — equal to
three decimals. No common active set exists to isolate.

---

## 3. Arm C — no `d`-free selector predicts the active set

Six selectors, tautology-guard asserted at runtime (`args ⊆ {b,c,p,n}`; none may read `a₀`, `d`,
`xs`, `ys`, or `U`), against a permutation null with `R=200`.

| selector | outcome across the 7 primes |
|---|---|
| `s1_legendre(b)` | in-band 7/7 (AUC `0.498–0.502`) |
| `s2_chi3(b)` | **H = 27.9 at `p=163` (`p=0.005`) — dies at every larger prime:** `5.05, 5.84, 5.00, 5.35, 1.12, 2.22` against null mean `≈2.1` |
| `s3_small_b` | out-of-band 2/7, **opposite signs** (`0.5055` at 433, `0.4971` at 991) |
| `s4_glv_sector` | out-of-band 2/7 (`0.5087`, `0.5029`), in-band at the 3 largest primes |
| `s5_c_zero` | in-band 7/7 |
| `s6_noise` (C4 plant) | in-band 7/7 — comparator calibrated |

The `s2_chi3` hit is a **small-prime chance pattern**: it is the smallest prime in the set and it
fails to replicate at all six larger ones (drill rule: retest out-of-sample before naming a zero).
The scattered `s3`/`s4` hits have no consistent sign, effect sizes `|AUC−0.5| ≤ 0.009`, and vanish
as `p` grows; 6 selectors × 7 primes at 95% bands predicts `≈2` such hits by chance and `4` were seen.

**Scoped null:** no pre-committed `d`-free selector predicts `|U(a₀,b,c)|` above the permutation
floor on these curves, at these `p`, for this selector list. Bound to method + sample + floor — this
is not a statement that no cheap selector exists.

---

## 4. What this says about the proposed basis transformation

Stated as a bound with its scope, not a verdict:

- **In the `(b,c)` frequency basis — the basis in which "harmonic" is defined — there is no
  active/starved split to isolate.** The alignment is Rayleigh-distributed across `~p²` harmonics;
  removing the top 1% removes `2.7%` of it, exactly as removing the top 1% of a random target's
  spectrum does.
- **The `l²` budget is basis-invariant.** `Σ|U|² = p²(n−1)` exactly, so *no unitary change of basis
  can create concentration* — it can only redistribute a fixed total. A basis transformation that
  concentrated the alignment would have to be non-unitary, and the run does not test that class.
- **What is untested and explicitly out of scope:** non-unitary/oblique transformations; bases other
  than the `(b,c)` Fourier basis; higher-degree (non-linear) readouts; concentration below the power
  floor; selectors outside the pre-committed list; `p` beyond 2089. A flat pattern statistic here is
  a **bounded magnitude in the tested basis**, not an absence of structure.

**The one thing that did not dissolve** is the `0.06–0.10%` sub-Rayleigh deficit in `mean|U|` — real,
one-directional at 7/7 primes, `−13.9σ` at `p=2089`, and unexplained by the two mechanisms checked.
It is small, and it is a magnitude rather than a lever, but it is the live item.

No ECDLP, extraction, or security claim is made or implied. Nulls above are conditional on
method + sample + floor.

---

## 5. Next probe (named now, not chosen post hoc)

The deficit is a statement about `Σ|U|`, i.e. about `Corr(a₀)` — the `l¹` norm under a pinned `l²`.
The decidable follow-up is whether the deficit is carried by a **specific `(b,c)` locus** or is
uniform across the spectrum: compute the character-minus-null magnitude difference as a function of
`(b,c)` and test whether its support is equivariant under the exact `(a,b) ↦ (λa, βb)` action
(C2 holds to `1e-12`, so the map is available as an exact partition). That is a different statistic
from the ones frozen here and needs its own prereg.
