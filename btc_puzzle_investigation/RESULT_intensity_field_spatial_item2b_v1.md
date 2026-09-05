# RESULT — ITEM 2 REMAINDER: spatial statistics of `|T(a,b)|²`. No structure established; THREE artifacts caught by controls.

**Date:** 2026-08-01. **Script:** `intensity_field_rmt_v1.py`. **Grade:** `[NO CLAIM — the matched null is not yet correct]`.

## 0. Object and stance on nulls

`T(a,b) = Σ_d e_p(b·x_d)·e_n(a·d)`; `I = |T|²/mean`. Porter–Thomas (the **1-point** intensity
distribution) was measured `[EMPIRICAL, p ≤ 2089]`. The **2-point / spatial** statistics never were.

**The null is built from the data, not from theory.** No Porter–Thomas, GUE or Katz–Sarnak
prediction is assumed anywhere. The null is an **orbit permutation of the observed field**: it
preserves the observed intensity marginal *exactly* — whatever that marginal is — and destroys only
spatial structure. The question is precisely *"is the field spatially structured beyond its own
marginal?"*

Note `T` uses `e_p(b·x_d)` and **no `y`**, so the `p ≡ 3 mod 4` requirement governing the
`u = V/(2i√p)` framework does **not** apply to this object.

## 1. Forced symmetries (the null must preserve them)

`x_{−d} = x_d` ⇒ `I(−a,b) = I(a,b)`; conjugation ⇒ `I(a,−b) = I(a,b)`;
`x_{λd} = βx_d` ⇒ **`I(λa, βb) = I(a,b)`** — a μ₃ symmetry linking `a` and `b`.

## 2. Three artifacts, each caught by a control

**(A) `C-ORBIT` failed — the λ/β pairing.** There are **two** nontrivial cube roots mod `n` and two
mod `p`; `x_{λd} = βx_d` holds only for the **matched** pair. Choosing each independently pairs them
wrong. `C-ORBIT` (intensity must be exactly constant on every orbit) read max spread ≈ **7.5**
instead of 0 at all five primes. After matching by direct test: spread ≈ **1e-13**. Without this
control the whole null would have been silently invalid.

**(B) The trivial frequencies dominated everything.** `I(0,0) = n` is a spike and the entire `b = 0`
row is exactly `(n, 0, 0, …, 0)`; the `a = 0` column has twice the mean. On the full grid all three
correlation statistics read `p ≈ 0.01` at **all five primes** — but the null's sd was inflated 37×
by *where the spike landed*, and the data z-scores were only ≈ −0.5. Trimming `a = 0` and `b = 0`
collapses the null sd from 0.371 to 0.0099 and removes the apparent effect from `C_b1` (p = 0.94)
and `C_a3` (p = 0.96).

**(C) The surviving `C_a1` is Parseval.** After trimming, only lag-1-in-`a` survived (p = 0.02, one
prime). But **Parseval is forced exactly**: `Σ_a |T(a,b)|² = n²` for every `b` — verified, row sums
all equal to `n` to `1e-13`. The orbit permutation moves values **across** rows and therefore breaks
this constraint; a fixed row sum induces exactly the small negative adjacent correlation observed.

Synthetic control — iid exponential rows with **only** the row-sum constraint imposed:

| `n` | synthetic `C_a1` (Parseval only) | observed `C_a1` |
|---|---|---|
| 199 | 0.99484 | 0.98140 |
| 313 | 0.99468 | 0.99503 |
| 397 | 0.99343 | 0.99505 |

At `n = 313, 397` the observed value is reproduced by the row-sum constraint alone. **The effect is
Parseval, not curve structure.**

## 3. Verdict

**No spatial structure established, and no claim made.** `C_b1`, `C_a3` and the block number-variance
are null after trimming; `C_a1` is accounted for by a forced constraint the null does not respect.

**What is owed before this object can be adjudicated:** a null that preserves **per-row Parseval**
*and* the μ₃/parity orbit structure simultaneously — i.e. a within-row, orbit-respecting permutation.
That is a specification, not a result, and it is not run here. The single residual (`n = 199`,
0.9814 vs 0.9949) is one prime, unreplicated, and cannot be assessed until that null exists.

## 4. Method note

Three artifacts in one object, all caught by controls rather than by reading: a wrong symmetry group,
trivial frequencies, and an unrespected conservation law. Each would individually have produced a
publishable-looking `p ≈ 0.01` across every prime tested. **The consistency of a result across primes
is not evidence against artifact — all three artifacts were perfectly consistent across primes.**
