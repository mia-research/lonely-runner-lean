# The next cascade links at n = 8 — and why the n=11 mechanism stalls here

2026-09-08. Continues `RESONANCE_CASCADE_N8_v1.md`. Scripts
`experiments/n8/{cascade_n8_v1, cascade_n8_v2, bottleneck_n8_v1}.py`. Exact `Fraction`.

## 1. Link 2 — `I₁` pins two distinct runners  `[PROVED]`

Closing `I₁`'s left edge `9/56` needs `B_{j,0} ∋ 9/56`, i.e. `a_j ∈ [49/9, 7]`; only `k = 0`
reaches it inside any sign range, so the left closer is **`L ∈ {5,6}`**. Closing the right
edge `15/56` needs `a_j ∈ [49/15, 21/5]`, so **`R ∈ {3,4,5}`**.

Since `49/9 > 21/5`, **`L ≠ R`: slot `I₁` alone pins two of the five free runners.**

What that costs, computed across the whole ranges rather than at the resonance point:

| closer | never touches |
|---|---|
| `L = 5` or `6`, `a ∈ [49/9, …]` | `I₄` on `[49/9, 217/39]`; `I₅` on `[231/41, 273/47]`; `I₆` on `[41/7, 329/55]` |
| `R = 3`, `a ∈ [49/15, 4]` | `I₂` on `[63/17, 4]`; `I₄` on `[119/33, 4]`; `I₆` on `[25/7, 217/55]` |
| `R = 4`, `a ∈ [49/15, 21/5]` | `I₂` on `[63/17, 21/5]`; `I₄` on `[119/33, 161/39]` |
| **`R = 5`, `a ∈ [4, 21/5]`** | **`I₂` on all of `[4, 21/5]`** — it contributes nothing to `I₂` |

## 2. Two negatives, both exact

**Pinning the closers kills no boundary.** For every admissible `(L,R)` — five pairs — all
twelve slot boundaries retain at least one available coverer. `[PROVED, exhaustive]`

**No slot point is bottlenecked onto a single runner.** Scanning every slot by its exact
breakpoints `p = 7(8k+7)/c`, `7(8k+9)/c` for `c ∈ {1..7}`:

| slot | `I₁` | `I₂` | `I₃` | `I₄` | `I₅` | `I₆` |
|---|---|---|---|---|---|---|
| min able-set size | **2** | 4 | 5 | 5 | 5 | 5 |

**Not one cell of any slot is reachable by only one runner.** `[PROVED, exhaustive]`

## 3. Why this matters — the n=11 mechanism is a rigidity argument

The n=11 kill is Main Claim 5.1: *closing `I₄` forces `a₂ ≥ 20/9`, closing `I₉` forces
`a₂ ≤ 575/261`, and `20/9 > 575/261`.* Two slots squeeze **the same runner** into disjoint
windows. That presupposes each of those slots is bottlenecked onto runner 2 — i.e. that the
configuration is **critically braced**, so that pinning one runner has nowhere to give.

`n = 8` is not braced, and now that is measured three independent ways:

1. In the AP limit only 2 of 6 slots are covered with a touching point (`I₂`, `I₄`, both
   owned by the single pair `(3,5)`); the other three are covered with **strictly positive**
   overlap (`RESONANCE_CASCADE_N8_v1` §2, `AP_ROUTE_TRANSLATION_v1` §3).
2. Every slot point has **at least 2, and usually 5, able runners** (§2 above).
3. The measure budget is loose: within `W_ref` the five free runners carry `5/4` of density
   against slots occupying `5/7` of the window — a **75% overlap allowance**, the same `7/4`
   that defeats every counting argument on this problem.

> **So the n=11 proof squeezes a rigid configuration, and at `n = 8` there is nothing to
> squeeze.** The incompatibility mechanism has no unconditional analogue here — not because
> a step is missing, but because its hypothesis (bottlenecking) is false at `n = 8`.

This is the same fact that appeared earlier as the collapse of the complementary-pair table
(`(ℤ/8)ˣ` has exponent 2, one pair instead of four), seen from the geometric side rather than
the algebraic one. One pair owning two slots is exactly what "not braced" means.

## 4. What follows for technique

An argument at `n = 8` must exploit **abundance**, not rigidity: five chains, six slots,
every point multiply covered, and yet no simultaneous covering. That is a global
obstruction — periodicity or parity — rather than a local squeeze. The natural candidate is
the 2-adic structure that keeps recurring: at `n = 8` the even-indexed runners cannot sit on
an odd witness at all, which is a parity constraint on *which* runner can be tight *where*,
and it has not been brought into the `W_ref` frame.

## 5. Status

`[PROVED]` link 2 (two distinct closers, with their costs); both negatives.
`[NOT CLAIMED]` any closure. `n = 8` is not proved. The value here is that the stall is
now located: it is the bottlenecking hypothesis, and it is false at `n = 8` for a reason we
can state and measure.
