# RESULT — N1 reframed: BOTH quadratic readouts cap at `2√p`; the `½` is a non-tight ceiling, not starvation (v1, 2026-07-23)

> ## ⚠ STATUS CORRECTION (2026-07-23, filed same day)
> **§2 and §3 of this document are WITHDRAWN as N1 findings.** See
> `PREREG_N1_eigenvalue_starvation_v1_DEVIATIONS.md`. `PREREG_N1_eigenvalue_starvation_v1.md` is
> *"Binding on: any run reporting results for finding N1"*; this run was bound by it and did not
> conform — its §1 primary statistic is the **pooled** 4th spectral moment, explicitly *"not a max"*,
> and §1b files the saturation-max as secondary, *"reported, never a verdict."* This run used the
> excluded max statistic with no matched null, no plant, and no regime stratification, and filed no
> deviation at the time. The §2/§3 claims are therefore an **unregistered observation**: not to be
> cited as an N1 finding, tallied, or used to reframe or reprioritise N1 until re-run under the spec.
>
> **§1 STANDS** — it is a derivation (no statistic, no null, no free parameter) and does not depend on
> any withdrawn number. The refutation of the author's own integrality hypothesis also stands.

**Status of the remainder: unregistered observation.** Script: `n1_exact_saturation_v1.py`.

---

## 1. The candidate mechanism in §A2.6 is structurally unavailable as stated `[DERIVED]`

§A2.6 §4 proposes: *"the involution `[−1] : P ↦ −P` splits `A_new`'s 4-dimensional `H¹` into 2+2 by
parity, and a definite-parity `y`-readout couples to only its own 2-dim half"*, with the decidable
test *"compute the dimensions of the `[−1] = ±1` eigenspaces on `H¹(A_new)`."*

**`[−1]` does not act on the relevant `H¹` at fixed frequency.** The sum is
`V(a) = Σ_d χ₂(y_{[d]G}) e_n(ad)`; the sheaf carries the group character `ω = e_n(a·)`, and
`[−1]` sends `ω ↦ ω⁻¹`. So `[−1]` maps `H¹(a) → H¹(−a)` — it **swaps two different cohomologies**
rather than splitting one. Since `n` is an odd prime, `a ≡ −a` only at `a = 0`, i.e. at no frequency
that carries the maximum. What `[−1]` produces is exactly `V(−a) = χ₂(−1)·V(a)` — which is **M4**, the
real/imaginary structure, already recorded.

So there is no 2+2 eigenspace split to compute at fixed `a`, and the named decidable test does not
discriminate. This does not touch M4 or the parity facts, which stand; it removes the *proposed
mechanism* built on top of them. (§A2.6 already recorded the candidate's own live counterexample:
`bx` is even-parity and saturates 0.909, not ½.)

---

## 2. The measurement that reframes it: **both χ₂ readouts cap at `2√p`** `[MEASURED, 8 primes]`

Define `Q(a) := |V(a)|² / p`, so a `k√p` bound means `Q ≤ k²`.

| p | p mod 4 | n | `χ₂(y)` max Q | `χ₂(x)` max Q | `e_p(bx+cy)` max Q | `e_p(bx)` max Q |
|---|---|---|---|---|---|---|
| 1249 | 1 | 1303 | — | 3.848 | 9.165 | 7.432 |
| 1303 | 3 | 1249 | 3.809 | 3.947 | 8.745 | 6.136 |
| 1669 | 1 | 1663 | 3.831 | 3.659 | 10.734 | 7.195 |
| 1831 | 3 | 1753 | 3.961 | 3.875 | 10.604 | 6.423 |
| 2089 | 1 | 2143 | 3.979 | 3.984 | 9.497 | 8.096 |
| 2143 | 3 | 2089 | 3.934 | 3.901 | 9.342 | 7.274 |
| 2251 | 3 | 2341 | 3.957 | 3.863 | 9.396 | 6.652 |
| 2281 | 1 | 2203 | 3.825 | 3.850 | 9.320 | 6.429 |
| 2503 | 3 | 2557 | 3.969 | 3.957 | 9.230 | 7.589 |

**Nominal ceilings (P6b):** `χ₂(x)` → `2√p` ⇒ `Q ≤ 4`; `χ₂(y)` → `4√p` ⇒ `Q ≤ 16`.

**Both land in `[3.66, 3.98]` — the same absolute magnitude `≈2√p`.** `χ₂(x)` therefore saturates its
own ceiling at ~97–99%; `χ₂(y)` reaches exactly **¼ of `16`, i.e. ½ in amplitude**. The ½ is not a
property of `y`: **both quadratic-character readouts cap at `2√p`, and only `y`'s nominal ceiling is
`4√p`.**

**The cap is real, not a fluctuation.** `Σ_a|V(a)|² = n(n−1)` forces `E[Q] ≈ 1`. For a *real* `V` (M4)
the half-spectrum is ~`n/2` samples of `χ²₁`, whose maximum has expectation **11.0 / 11.6 / 11.8 /
12.3** at `n = 1249/1663/2089/2557` (200 sims each). Observed maxima are **3.8–4.0** at every prime —
a factor ~3 below the random-real model. And the *additive* readouts do exceed 4 (up to **10.7**), so
the cap is specific to the χ₂ rows and is not an artifact of the estimator or of `n`.

**Integrality REFUTED.** If `A_new` supersingular forced `V(a)/√p` to be a sum of roots of unity with
`V` real, `Q(a)` would be a rational integer. It is not: the fraction of frequencies with `Q` within
`10⁻⁶` of an integer is **0.000** at every prime, and `max Q` misses 4 by `0.02 … 0.19`. So the ½ is
**not** an exact finite-`p` identity; the evidence is for `max_a|V(a)| ≤ 2√p` as a *bound*, with the
maximum approaching but not attaining it.

---

## 3. What N1 now is

| before | after |
|---|---|
| "`χ₂(y)` has 4 eigenvalues available and delivers the magnitude of 2" — unexplained | **`2√p` is the extremal magnitude of *both* quadratic readouts; `χ₂(y)`'s `4√p` ceiling is simply not tight** |
| mechanism candidate: `[−1]` splits `H¹` 2+2 | **structurally unavailable** — `[−1]` maps `H¹(a)→H¹(−a)`, `a ≢ −a` for `a≠0` |
| decidable test: dims of `[−1]=±1` eigenspaces | **does not discriminate**; superseded by the question below |
| `bx` at 0.909 an "unresolved tension" | **not a tension** — additive readouts are not capped at `2√p` (they reach `Q=10.7`); the cap is a χ₂ phenomenon |

**The sharp open question, restated:** *why does a quadratic-character readout on this curve cap at
`2√p` regardless of its ramification count `#R`?* The `#R = 4` count for `y` (three 2-torsion zeros
plus the order-3 pole at `O`) is correct as a dimension of `H¹`; what is not established is that all
four Frobenius eigenvalues can align. A pairing `{α, −α, β, −β}` would cap the attainable trace — and
the untwisted `A_new` char poly `t⁴ + m p t² + p²` **is even in `t`**, so its eigenvalues do pair that
way. Whether the *twisted* `H¹(a)` inherits that pairing is exactly the thing to settle, and it is a
statement about the twisted sheaf, not about `[−1]`.

---

## 4. Grades and scope

| item | grade |
|---|---|
| `[−1]` maps `H¹(a) → H¹(−a)`, so no fixed-`a` 2+2 split | `[DERIVED — UNREVIEWED]` |
| `χ₂(x)` and `χ₂(y)` share max `Q ≈ 4` at 8–9 primes | `[MEASURED]`, `p ≤ 2503`, prime-order curves |
| `Q ≤ 4` is a cap, not a fluctuation (vs `E[max χ²₁] ≈ 11–12`) | `[MEASURED + REASONED]` |
| additive readouts exceed `Q = 4` (up to 10.7) | `[MEASURED]` — `(b,c)` sampled from a small grid, so these are **lower bounds** on the true max |
| `Q(a)` integral / ½ exact at finite `p` | **`[REFUTED]`** |
| the `2√p` cap for `χ₂(y)` as a theorem | **OPEN** — not proved here |

**Scope.** Nine primes, `200 < p < 2600`, prime-order curves from `t_y_maxbound_v1.prime_order_curve`;
`(b,c)` for the additive rows sampled over `b∈{1,2,3}, c∈{0,1,2}` only. Float used for FFT magnitudes
on `±1` sequences of length `< 2⁶` bits — no key material, no exactness claim rests on it. **This is
exploratory: no confirmatory N1 verdict is issued, and the prereg has not been re-run.**

**No ECDLP content.** `max|V|` bounds a misaligned readout's correlation; per H3 point 3
`[PROVED|Weil/KS]` a misaligned readout sees `√p` noise provably. Nothing here approaches a scalar bit.
