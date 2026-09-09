# (A) the Fourier identity, and (B) proximity to the tight instances

2026-09-10. Follows `RELATION_DICHOTOMY_v1.md`. Scripts
`experiments/n8/ok_fourier_v{1,2,3}.py`, `ok_tightprox_v1.py`.

---

## A1. The identity  `[PROVED]`

Let `f = 1_{‖θ‖ ≥ 1/8}`, the indicator of `[1/8, 7/8]`. Then `f̂(0) = 3/4` and, for `k ≠ 0`,

    f̂(k) = (e(−k/8) − e(k/8))/(2πik) = −sin(πk/4)/(πk),

so `f̂` is **even**, `|f̂(k)| ≤ 1/(π|k|)`, and **`f̂(k) = 0` exactly when `4 | k`**. Since
`|G| = ∫ ∏_j f(e_j t) dt`, expanding and integrating gives

> **`|G| = Σ_{k ∈ ℤ⁷, k·e = 0} ∏_j f̂(k_j)`.**

The `k = 0` term is `(3/4)⁷ = 0.133484`; every other term is a resonance. Support 1 is
impossible (`k_j e_j = 0 ⟹ k_j = 0`).

## A2. The absolute bound is dead  `[PROVED — counterexample]`

Support-2 alone is misleading: `(3/4)⁷ − T₂ > 0` for ~99.9% of tuples, **but that is not a
lower bound on `|G|`** — it omits support ≥ 3. Adding the next two supports, each truncated
(so each *understates* its tail) and with supports 5–7 omitted entirely:

| `E` | `|G|` | `T₂` | `T₃ (H=30)` | `T₄ (H=14)` | `(3/4)⁷−T₂−T₃−T₄` |
|---|---|---|---|---|---|
| `(2,6,7,8,10,13,14)` | 0.006387 | 0.0652 | 0.2753 | 0.2499 | **−0.4568** |
| `(1,3,4,5,7,11,24)` | 0.007170 | 0.0502 | 0.2948 | 0.2996 | **−0.5111** |
| `(1,3,5,7,13,15,24)` | 0.071886 | 0.0695 | 0.1967 | 0.2363 | **−0.3689** |
| `(3,10,14,15,16,19,21)` | 0.117411 | 0.0360 | 0.1078 | 0.1655 | **−0.1758** |

The triangle inequality overshoots the main term by 3–4× for **every** tuple, easy ones
included. **Cancellation is not an optimisation here; it is the entire content.**

## A3. What cancels, and what does not  `[PROVED]`

Each support-2 family sums in closed form. For a pair with `g = gcd`, `a = e_i/g`,
`b = e_j/g` coprime,

    Σ_{m≠0} f̂(mb)f̂(ma) = [Cl(π(b−a)/4) − Cl(π(b+a)/4)] / (π²ab),
    Cl(x) = Σ_{m≥1} cos(mx)/m² = π²/6 − πx/2 + x²/4   on [0,2π],

so every family is an explicit **rational** multiple of `1/(ab)` — the same phenomenon as
`Ray(p)` being rational in `O_RESONANCE`. Verified against direct summation to `2·10⁻⁶`:

    (1,2) → 1/16    (1,3) → 1/48    (1,4) → 0       (1,5) → −1/80
    (1,7) → −3/112  (2,3) → 1/48    (3,4) → 0       (5,7) → 1/560

`(1,4)` and `(3,4)` vanish by the `4 | k` rule. Per tuple, **signed `T₂` is 7–45% of
absolute `T₂`, and only 1–8% of the main term** (e.g. `+0.0047` against `0.1335` at the
extremum). So with signs, **support 2 is negligible**.

At the extremum `|G| = 0.1335 + tail` with `tail = −0.1271`, of which signed support-2 is
`+0.0047`: **support ≥ 3 carries −0.1318, nearly the whole main term.** And the
lowest-height support-3 vectors are `k = (1,1,−1)` on `e_i + e_j = e_l` — so the empirical
relation count of `RELATION_DICHOTOMY_v1` **is** the Fourier support-3 structure. The two
pictures are one picture.

## B. Proximity to the tight instances beats relation count  `[EMPIRICAL — exhaustive]`

The three tight instances are `T₁ = {1,…,7}`, `T₂ = {1,2,3,4,5,7,12}`,
`T₃ = {1,4,5,6,7,11,13}`, each with `∫X = 0`. Define
`ov(E) = max over tight T and dilations λ of |E ∩ λT|`. Over all 229 061 Case-2 tuples in
`[1..24]`:

| `ov` | tuples | `min |G|` | mean `|G|` |
|---|---|---|---|
| ≤ 4 | 220 581 (96.3%) | **0.014881** | 0.117 |
| 5 | 8 238 | **0.006387** ← global min | 0.096 |
| 6 | 242 | 0.007738 | 0.059 |

Every one of the ten hardest tuples has `ov ≥ 5`; the extremum
`(2,6,7,8,10,13,14)` meets `2·T₁ = {2,4,6,8,10,12,14}` in five places.

> **Split (B).** `ov ≤ 4` — **96.3%** of Case 2, `min |G| = 0.014881`, a **2.3× margin**
> over the target `93/14560`. `ov ≥ 5` — **3.7%**, structurally pinned: five of seven speeds
> lie in `λT` for one of three explicit sets.

This supersedes the relation split, which left **40%** in the hard branch at a 5.2× margin.
Proximity leaves **3.7%**, and that remainder is described, not merely counted: it is
"five of seven speeds from a dilated tight instance, plus two free speeds".

**Scope.** `ov` was computed with `λ ≤ 30` inside the box `[1..24]`, where only `λ ≤ 3` can
contribute five elements. Larger boxes admit larger `λ`, and the `min |G|` figures are
exhaustive **for that box only**.

## Grades

A1: **PROVED** (Fourier expansion; the vanishing rule is `sin(πk/4) = 0 ⟺ 4|k`).
A2: **PROVED — counterexample**; the truncations *understate* the tails, so the negative
columns are conclusive. A3: **PROVED** — closed form checked against direct summation; the
cancellation ratios are exact computations. B: **EMPIRICAL**, exhaustive over Case 2 in
`[1..24]`, with the `λ` caveat above. Neither branch is proved; (A) now has a precise
target — the **signed** support-≥3 sum — and (B) has a described remainder.
