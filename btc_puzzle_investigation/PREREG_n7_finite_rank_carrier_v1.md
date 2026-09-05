# PREREG — N7's carrier is FINITE RANK: the character's `U` is a sum of `r ≤ 4` Weil numbers, the null is a sum of `n ≈ p` random phases

**Date 2026-09-02, written BEFORE the run.** Advances **N7** (open since v12). Builds on
`RESULT_subrayleigh_deficit_locus_v1.md` (the low-tail localisation, the ~8% near-zero excess, the
M4-blindness) and `NOTE_n7_xy_axis_localization_v1.md` (the x/y stratum asymmetry). Model scale only;
**no transfer to secp claimed**.

## The hypothesis

`U(b,c) = Σ_{P∈E(F_p)} g(d_P) e_p(b x_P + c y_P)` with `g` a character of the group.

- **Character arm:** by Grothendieck–Lefschetz + Ogg–Shafarevich + Weil II (record **P6a/P6b**),
  `U` is a sum of a **bounded** number of Frobenius eigenvalues of modulus `√p`:
  `|U| ≤ (1+ord_O(f))√p + 1` — **`r = 4` for `c ≠ 0`**, **`r = 3` for `c = 0`**.
- **Null arm:** a random Hermitian unit-phase weight makes `U` a sum of `n ≈ p` independent terms ⇒
  CLT ⇒ complex Gaussian ⇒ `|U|²` exponential ⇒ **Rayleigh**.

> **A finite-`r` random walk has more near-zero mass and a hard ceiling relative to a Rayleigh of the
> same second moment.** That is exactly the measured signature: low-tail excess (dominant), high-tail
> deficit (secondary), `Σ|U|²` exactly conserved, `M4` blind, and **constant in `p`** — because `r`
> does not grow with `p`.

## Pre-registered predictions

| # | prediction | falsifier |
|---|---|---|
| **N7-A** | The **null** arm matches Rayleigh: its near-zero counts agree with the exponential prediction to within MC error at every tested prime. | null itself deviates from Rayleigh ⇒ the baseline is not what the mechanism assumes |
| **N7-B** | The **character** arm's low tail matches a **finite-`r` random walk with `r` in the range 3–5**, and **not** Rayleigh. Fitted `r̂` from the low tail lands in `[3,5]` at every tested prime. | `r̂` outside `[3,5]`, or `r̂` drifting systematically with `p` |
| **N7-C** | The predicted near-zero excess of `r=4` over matched Rayleigh reproduces the measured **~8%** to within a factor ~2 (i.e. lands in 4–16%). | predicted excess outside 4–16% |
| **N7-D** | **`r̂` is SMALLER on `c=0` than on the bulk** (3 vs 4), and the `c=0` stratum's deviation has the **opposite sign** to the bulk — reproducing the measured super-Rayleigh at `c=0` (−1.96%…−0.04%) vs sub-Rayleigh in the bulk (+0.076%…+0.145%). | `r̂(c=0) ≥ r̂(bulk)`, or the sign does not flip |

**N7-D is the discriminating arm.** A generic "the character is just less random" story predicts the
same sign everywhere. Only a *rank* story predicts a sign flip tied to a stratum whose rank the
cohomology independently fixes at 3 rather than 4.

## Method

For each prime: build `U` exactly as the frozen instrument does (`subrayleigh_deficit_scaling_v1.py`
signal path; exact-int EC arithmetic, the sanctioned FFT float carve-out). Extract `ρ = |U|/√(E|U|²)`
for (i) the character, (ii) `K` Hermitian-null draws. Compare the low-tail CDF against Rayleigh and
against Monte-Carlo `r`-step unit random walks for `r = 2…8`; fit `r̂` by low-tail CDF distance.
Report per stratum: bulk (`b≠0, c≠0`), `c=0`, `b=0`.

## Scope

`E : y²=x³+7`; model primes only. `r` here is the count of Frobenius eigenvalues contributing to a
single `U(b,c)` — an upper bound from the record's own theorem, not a fitted parameter of the effect.
Nothing in this prereg claims transfer to `p ≈ 2²⁵⁶`.
