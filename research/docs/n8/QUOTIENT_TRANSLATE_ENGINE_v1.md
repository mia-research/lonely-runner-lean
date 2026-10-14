# The quotient–translate engine at n = 8 — analytic constraints on a counterexample from LRC(7) alone

2026-09-08. Script `experiments/n8/dyadic_engine_v1.py`. Exact `Fraction` throughout; no
float on any path. Input: `intLRC_seven` (machine-verified, axiom-clean, this project).
No prime search, no covering enumeration, nothing from Rosenfeld's computation.

## 0. What this is, and what it deliberately is not

Rosenfeld's paper was opened for exactly one purpose: to read the **statement** of his
Lemma 6, because an independently derived covering condition needed to be checked against
it. The two are not the same — his modulus is `(k+1)p = 8p`, the derived one was `p`, and
his is strictly stronger. That settled the question and the prime-covering line was
dropped: **it is his route, it is empirical, and it is not the target.** Nothing below
uses a prime, a search, or any output of his program.

What is below is a different engine. It takes one input we own — `LRC(7)` — and returns
**analytic necessary conditions on the arithmetic of a counterexample to LRC(8)**.

## 1. The engine  `[PROVED, given LRC(7)]`

**Lemma (quotient–translate).** *Let `T` be 7 distinct positive integers with `gcd(T) = 1`.
Fix `q ≥ 2` and split*

    H = {v ∈ T : q | v},   L = T \ H,   h = |H|.

*Then `h ≤ 6`. Let `Z = {v/q : v ∈ H}`, a set of `h` distinct positive integers. By
`LRC(h+1)` there is `σ₀` with `‖z σ₀‖ ≥ 1/(h+1) ≥ 1/7 > 1/8` for every `z ∈ Z`. Put*

    t_k = (σ₀ + k)/q,   k ∈ ℤ/q.

*Every `v ∈ H` is lonely at every `t_k`, since `‖v t_k‖ = ‖(v/q)(σ₀+k)‖ = ‖(v/q)σ₀‖`.
Hence if `T` is a counterexample, every `t_k` is blocked by some `v ∈ L`; writing*

    K_v = { k ∈ ℤ/q : ‖v(σ₀+k)/q‖ < 1/8 },

*we must have `⋃_{v∈L} K_v = ℤ/q`, and therefore*

    Σ_{v ∈ L}  |K_v|  ≥  q. ∎

`h ≤ 6` because `h = 7` forces `q | gcd(T) = 1`. The whole content is that the quotient
`v ↦ v/q` turns the `H`-speeds into a **smaller** LRC instance, which LRC(7) then solves
outright — and the `q` translates `t_k` cost the `H`-speeds nothing, because `(v/q)k` is an
integer.

**The size bound.** With `g = gcd(v,q)` and `q' = q/g`, the `q` numbers `v(σ₀+k)/q` mod 1
form `g` copies of a `1/q'`-spaced grid, so

    |K_v|  ≤  g · κ(q'),      κ(m) = m/4 if 4 | m,  else ⌈m/4⌉,

`κ(m)` being the largest number of points of a `1/m`-grid inside an open interval of
length `1/4`. **Verified exactly** (Part A): over every `q = 2..48` and every `v ≤ 4q`, the
true maximum of `|K_v|` over `σ₀` equals the bound and never exceeds it — **0 violations**.

Note the triangle inequality also gives `K_v − K_v ⊆ {δ : ‖vδ/q‖ < 1/4}`, which is where
the bound comes from; it is recorded because the *shape* of `K_v`, not only its size, is
what a sharper form would use (§5).

## 2. The corollaries  `[PROVED, given LRC(7)]`

Write `n_e = #{v ∈ T : v₂(v) = e}`. Each row is `Σ_{v∈L} g·κ(q') ≥ q` instantiated.

| `q` | contribution of a speed with `v₂ = e` | necessary condition |
|---|---|---|
| `2` | `e=0` : 1 | **`n₀ ≥ 2`** — at least two odd speeds |
| `4` | `e=0` : 1, `e=1` : 2 | **`n₀ + 2n₁ ≥ 4`** |
| `8` | `e=0` : 2, `e=1` : 2, `e=2` : 4 | **`n₀ + n₁ + 2n₂ ≥ 4`** |
| `2^r` | `e ≤ r−2` : `2^{r−2}`, `e = r−1` : `2^{r−1}` | **`Σ_{e≤r−2} n_e + 2n_{r−1} ≥ 4`** |

| `q` prime | `κ(q)` | forced | conclusion |
|---|---|---|---|
| `3` | 1 | `\|L\| ≥ 3` | at most **4** speeds divisible by 3 |
| `5` | 2 | `\|L\| ≥ 3` | at most **4** speeds divisible by 5 |
| `p ≥ 7` | `⌈p/4⌉` | `\|L\| ≥ 4` | **at most 3 speeds divisible by `p`** |

The last row is uniform in `p`: `3⌈p/4⌉ < p` for every prime `p ≥ 7`, so three speeds can
never supply the covering. It is an infinite family of constraints from one finite input.

**Convergence with the existing record.** `P163_ARGUMENT_v1.md` §2 and
`COLLAPSE_Z163_v1.md` reach *"`T` contains at least two odd speeds"* from inside
Rosenfeld's `p = 163` covering frame. The `q = 2` row above re-derives the same statement
from `LRC(7)` alone, with no prime and no enumeration. Two independent derivations, and
the new one is not tied to a chosen prime.

## 3. Verification  `[PROVED — exact, end-to-end]`

The corollaries are statements about counterexamples, and LRC(8) is true, so they cannot
be tested by looking for a counterexample. What is tested is the **construction**: build
tuples that violate a corollary, run the engine, and check that the `t` it returns is
lonely for all seven speeds.

| test | tuples | engine fired | witness verified exactly |
|---|---|---|---|
| `q=2`, `n₀ = 1` | 400 | 400 | **400** |
| `q=4`, `n₀+2n₁ ≤ 3` | 400 | 400 | **400** |
| `q=8`, `n₀+n₁+2n₂ ≤ 3` | 400 | 400 | **400** |
| `q=3`, five speeds divisible by 3 | 400 | 399 | **399** |
| `q=5`, five speeds divisible by 5 | 400 | 400 | **400** |
| `q=7`, four speeds divisible by 7 | 400 | 400 | **400** |
| `q=11`, four speeds divisible by 11 | 400 | 400 | **400** |

2 799 witnesses, `Fraction` arithmetic, zero failures. The script raises on the one event
that would falsify the counting bound — budget `< q` but every `k` blocked — and it never
raised.

## 4. Power  `[PROVED — exhaustive over profiles]`

Of the **56** 2-adic profiles `(n₀,n₁,n₂,n_{≥3})` with `Σ = 7`, `n₀ ≥ 1` (from `gcd = 1`)
and `n_{≥3} ≥ 1` (from the `q = 8` witness ladder), the `q = 2,4,8,16` corollaries kill
**31 — 55%**, leaving 25. What survives is forced to satisfy

    n₀ ≥ 2,   n_{≥3} ≤ 3,   #{v : 4 | v} ≤ 4.

## 5. Where the engine stops, and the next step  `[measured, not asserted]`

Sharpness probe, `q = 4`, 4 000 tuples sitting exactly at `n₀ + 2n₁ = 4`: for **292 (7%)**
of them every `k` really is blocked at the `σ₀` the engine picks. So the counting bound is
reached — `n₀ + 2n₁ ≥ 4` is the exact reach of the *counting* form at `q = 4`, and cannot
be improved by counting alone.

The other 93% is the signal. For those tuples a lonely `t_k` exists anyway, which the
counting cannot see, because counting uses only `max_{σ₀}|K_v|` and discards two things:

1. **`σ₀` is not one point.** It ranges over the whole lonely set of `Z`, which contains an
   interval of length `ℓ ≥ 2(1/(h+1) − 1/8)/max Z`. As `σ₀` sweeps that interval the phase
   `v σ₀ / q` sweeps `vℓ/q`. Once `ℓ ≥ gcd(v,q)/v` the phase completes a full period, and
   at the resonant phase `|K_v|` drops to its **minimum**, `g·⌊q'/4⌋` — possibly zero.
2. **`K_v` is an interval**, not an arbitrary set of its size; the covering is by dilated
   intervals, which is far more rigid than the cardinality count admits.

Item 1 is the quantitative statement: `Σ_v avg|K_v| ≤ |L|q/4 + Σ_v g_v²/(v ℓ)`, so the
engine concludes whenever `|L| ≤ 3` **and** `Σ_{v∈L} g_v²/v < qℓ/4`. The first factor is
already available; the second is a comparison between the `L`-speeds and the largest
`H`-speed. **That inequality is the next object**, and it is exactly the point at which
this line meets `PARITY_MECHANISM_v1.md` §5 — the floor vector's trajectory — from the
opposite side. `[OPEN]`

## 6. Scope correction to the previous session

`experiments/n8/abundance_n8_v1.py` Lemmas 1 and 2 (one interval per slot; `Σ 1/a_j ≥ 3/7`)
are correct **as stated**, but both are derived inside the sign-range box `a_j ∈ (j−1,j+1)`.
That box is not a theorem at `n = 8`. `TIGHT_INSTANCES_v1.md` §5 records it failing on both
non-AP tight instances, with the table:

> *"The naive `n = 8` analogue `a_j ∈ (j-1, j+1)`, `j = 2,…,6`, **fails on both non-AP
> tight instances**"* — `{1,2,3,4,5,7,12}` fails at `a₃,a₄,a₅,a₆`; `{1,4,5,6,7,11,13}`
> fails at `a₅`.

Both are large-ratio configurations, which is the essential case. So Lemmas 1–2 are
`[PROVED, scope: configurations satisfying the sign-range box]` — the near-AP regime — and
they do **not** cover the case an argument has to survive. Whether the box holds on the
residual class (tuples carrying a multiple of 8, which is what the ladder leaves) is
**untested**, and is a cheap and worthwhile check.

## 7. Ledger

`[PROVED, given LRC(7)]` the engine lemma, the `|K_v| ≤ g·κ(q')` bound (exact, 0
violations over `q ≤ 48`), every corollary in §2, and the profile cut in §4.
`[VERIFIED — 2 799 exact witnesses]` the construction in §3.
`[measured]` the 7% sharpness figure in §5.
`[OPEN]` the phase-sweep inequality of §5.

**`n = 8` is not proved, and no cell is decided.** What is new is an analytic pruning of
the counterexample space that costs nothing but `LRC(7)`: at least two odd speeds, at most
three speeds divisible by any prime `≥ 7`, at most four divisible by 4, and 55% of the
2-adic profiles removed. Rosenfeld's ledger is untouched and was not used.
