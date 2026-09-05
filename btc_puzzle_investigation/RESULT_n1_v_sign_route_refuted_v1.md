# N1: the `v ≤ 0` route to `S_y ≤ 2` is REFUTED — exact rational counterexamples

**Date:** 2026-07-25 · Scripts: `n1_vsign_decide_v1.py` (count), `n1_vsign_exhibit_v1.py` (enclosure),
`n1_forced_identity_v1.py` (the adjudication check). Logs alongside.
**Antecedents:** `PREREG_n1_v_sign_sweep_v2.md` (frozen, never run as written),
`AUDIT_prereg_n1_v_sign_sweep_v2_v1.md` (verdict: NOT RUNNABLE; six defects; mandatory disclosure).

**No leakage, key-recovery or ECDLP content.** This is a statement about Frobenius angles of a twisted
sheaf over small model primes.

---

## 1. Result

> **There exist `μ₆` classes with `v = sinθ₁·sinθ₂ > 0`.** Exhibited with **exact rational
> enclosures** — no floating point anywhere in the decision:
>
> | `p` | `n` | `d=(n−1)/6` | stratum | offending `e₂` (exact integer interval) | **`v` enclosure (exact rationals)** |
> |---|---|---|---|---|---|
> | **127** | 127 | 21 | SIN | `[−339, −338]` | **`[21/127, 85/508]`** |
> | **163** | 139 | 23 | SIN | `[−428, −427]` | **`[101/652, 51/326]`** |
> | **211** | 199 | 33 | SIN | `[−488, −487]` | **`[65/844, 33/422]`** |
>
> Both endpoints of every enclosure are **rational and strictly positive**. The claim
> *"`v ≤ 0` for every `a`"* is **false**.
>
> ⇒ **The route to `S_y ≤ 2` via `v ≤ 0` does not survive.** `[PROVED — exact, float-free]`

**What this does NOT say.** `PREREG_v2` §6 records that **`v ≤ 0` is sufficient, not necessary**, for
`S_y ≤ 2`. So this kills the **route** and says **nothing** about whether `S_y ≤ 2` is true. The
inequality is **not refuted** — exactly the outcome `PREREG_v2` §4 pre-committed to for a `v > 0` cell
(*"route dead, inequality NOT refuted"*). `S_y ≤ 2` remains open and needs a different argument.

## 2. Why "in-sample" does not weaken this

The audit's mandatory disclosure records that `p = 127, 163, 211` were spent by its own timing check,
so their out-of-sample status is gone. **For this claim that is immaterial, and saying otherwise would
be a category error.**

The primary is a **deterministic universal statement** (`∀p ∀a : v ≤ 0`), which `PREREG_v2` §5 itself
identifies as such (*"one counterexample decides, no multiple-comparison correction, counts are scope
not significance"*). Pre-registration exists to stop selective reporting of **statistics**; a
counterexample to a universal mathematical claim is not a statistic and has no sampling distribution.
The only question a counterexample raises is **whether the computation is correct** — which is §3.

## 3. Adjudication — filling the gap the audit found

The audit's check 9 (defect **B4**) established that the frozen F5 adjudication gate has **zero
discriminating power** over the frozen scope: clause (a) re-runs an exact computation, clause (b) tests
*forced* identities that cannot fail on correct data, and clause (c) (`O(p⁴)` instrument at `p ≤ 61`)
**cannot fire at all**, since the scope starts at `p = 127`. A `v > 0` cell would pass that gate
automatically. Four independent checks are supplied instead.

**(A) A second, independent implementation of the count.** Written here from the definitions, reusing
none of the audit's decision code. Counts agree exactly:

| `p` | 13 | 43 | 127 | 163 | 211 |
|---|---|---|---|---|---|
| audit's count | 0 | 0 | 1 | 1 | 3 |
| **this implementation** | **0** | **0** | **1** | **1** | **3** |

It reproduces the frozen references on the way: `p=13` → `e₂ = −12`, `p=43` → 0 of 5 classes (the
frozen quintic's roots all `≥ −2p`).

**(B) The exactness of Descartes is self-certified, not assumed.** The count uses an integer Taylor
shift + sign count (the audit's **B1** substitution for Sturm). Descartes is exact rather than an upper
bound **only because `Q_p` is totally real** — and the run verifies that for free via
`V(g) + V(g(−Z)) = deg g`, which **PASSED at every prime**, including `21/21`, `23/23`, `33/33` at the
three counterexample primes. If total reality had failed, the certificate would have failed with it.

**(C) The `μ₆`-coset product, so no degree is asserted.** Per the audit's **B5(ii)**, the decision uses
`Q_p(Y) = ∏_{cosets}(Y − e₂(rep))`, always of degree exactly `(n−1)/6`, with counts taken with
multiplicity. Nothing aborts if the stabiliser exceeds `μ₆`.

**(D) ★ The discriminating check: a forced identity that `V₂` must satisfy and the `v` question never
touches.** This is what B4 was missing. `e₃ = (−V₁³ − 3V₁V₂ − 2V₃)/6` **contains `V₂`**, and `V₂` is
exactly what `e₂ = (V₁²+V₂)/2` — hence `v` — is built from. The identity

```
e3 = −p·e1   (SIN)        e3 = +p·e1   (COS)
```

is forced by the weight/functional-equation structure, is **independent of the sign of `v`**, and
requires `V₃`, which the `v ≤ 0` pipeline never computes. A bug in `V₂` generically breaks it.

`V₃` is computed here by a **third** implementation — a vectorized `F_{p³} = F_p[x]/(x³−c)` with a
different field model and a diagonal Frobenius (`x^p = c^{(p−1)/3}x`, using `p ≡ 1 mod 3`, which is
forced). Validated first on the two reference primes, then run:

| `p` | 13 (COS) | 43 (SIN) | **127** | **163** | **211** |
|---|---|---|---|---|---|
| `e₃ = ∓p·e₁` | **HOLDS** | **HOLDS** | **HOLDS** | **HOLDS** | **HOLDS** |

exact integer-vector identities in `ℤ[x]/Φ_n`. **`V₂` is corroborated at all three counterexample
primes by a constraint that has nothing to do with the sign of `v`.**

*(Instrument note: the first version of the vectorized adder built the element `3+3x+3x²` where the
doubling formula needs the scalar `3`. It was caught immediately by the trace failing to land in
`E(F_p)` — an assertion the script carries precisely because that landing is forced.)*

**(E)** The audit separately verified that the `p=127` offending class passes `M3a`, `M3c`, `M3d`
exactly — so the counterexample is **consistent with every Weil constraint** the spec carries, and is
not flagged as an artefact by anything in the frozen instrument.

## 4. ★ Characterization — `v > 0` is generic, and that is why the references missed it

Extended beyond the three spent primes (these are **new, out-of-sample**):

| `p` | 13 | 43 | 127 | 163 | 211 | 349 | 397 | 433 | 547 |
|---|---|---|---|---|---|---|---|---|---|
| `d` | 1 | 5 | 21 | 23 | 33 | 52 | 66 | 66 | 91 |
| stratum | COS | SIN | SIN | SIN | SIN | **COS** | **COS** | **COS** | SIN |
| **# `v>0`** | 0 | 0 | 1 | 1 | 3 | **3** | **2** | **3** | **4** |
| rate | — | 0% | 4.8% | 4.3% | 9.1% | 5.8% | 3.0% | 4.5% | 4.4% |

> **`v > 0` occurs in BOTH strata at a consistent rate of roughly 4–6% of `μ₆` classes.**
> Pooled over the seven primes with `d ≥ 21`: **17 of 352 classes**.

This explains why the conjecture looked plausible: **the two reference primes were too small to
exhibit a counterexample.** At a ~4.5% rate, a prime with `d = 5` shows none with probability
`0.955⁵ ≈ 0.79`, and `p=13` has `d = 1`. The conjecture was never tested anywhere it could fail —
`PREREG_v2`'s own frozen references are `p=13` and `p=43`, and its scope starts at `p=127`, the first
prime in the list where a counterexample in fact appears.

The rate figures are **descriptive**, with the obvious scope: nine primes, `p ≤ 547`, this curve
(`y² = x³+7`), `#E` prime. They are not needed for §1 — **one exact counterexample settles the
universal claim** — and no rate is fitted or extrapolated.

## 5. Status of `PREREG_n1_v_sign_sweep_v2.md`

- **Its primary question is ANSWERED, in the negative, and the 50-prime sweep is not needed for it.**
  The spec's own §4 outcome for a `v > 0` cell governs.
- Of the audit's six defects, this work implements **B1** (Taylor shift + Descartes, exact) and
  **B5** (coset product; strict boundary — `Q_p(∓2p) ≠ 0` at every prime here, so no boundary case
  arose) and **supplies what B4 was missing** (§3D).
- **B2** (multi-modular `m_p`) remains unimplemented here and is now needed **only** for the
  descriptive rate at large `p`: the naive coset product is `Θ(n⁴)` and cost `105 s` already at
  `p=547`. **B3** (mutation (iv) unconstructible) and **B6** (float carve-out) are moot for §1.
- **The mathematics, the seven fixes, and every frozen number in v2 verified exact** (audit §3). The
  spec was not wrong about the objects — **its conjecture was false**, which is a different thing and
  the one thing an audit of the spec could never have found.

## 6. What this licenses

- **Licenses:** *the `v ≤ 0` route to `S_y ≤ 2` is closed* `[PROVED — exact]`. Any future argument for
  `S_y ≤ 2` must not route through total non-negativity of `∓(e₂+2p)`.
- **Does NOT license:** any claim about `S_y ≤ 2` itself (still open — `v ≤ 0` was sufficient, not
  necessary); any claim about `p = 2²⁵⁶−2³²−977`; any ECDLP, leakage or security statement.
- **Names the next object:** `v ≤ 0` fails on a thin (~4–6%) set of classes. Whether the *weaker*
  statement that would still give `S_y ≤ 2` — e.g. a bound on `max_a v`, or `v ≤ 0` off an exceptional
  set — survives, is a different and untested question. **Do not treat this as evidence for or against
  it**; the exceptional classes were located, not characterized.
