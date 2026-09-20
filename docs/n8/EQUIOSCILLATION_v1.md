# Equioscillation — moving the unknown off the time axis

2026-09-13. n = 8, individual isolation, threshold 1/8.

A different frame, after the earlier ones were exhausted. The unknown stops being *a time* and
becomes *a pair of differences*.

---

## 1. Why the earlier frames failed

| frame | why it is dead |
|---|---|
| measure / covering | the AP's good set inside a revolution is four isolated points, **measure zero** — no size bound can work at any strength |
| union bound | fails by `3/2` |
| lattice / dyadic witness | existence is forced by density plus LRC(8) — circular; closed by `DYADIC_DEPTH_RESULT_v1` on 2026-09-07 |
| closed form for the blocked case | three candidates, all `≈ 46%`; clearing one blocker hands the block to a different difference in **3,234 of 3,234** cases |

All four fix a runner and search over `t`. That is the frame this file leaves.

## 2. The theorem  `[PROVED]`

Write `f(t) = min_j ‖d_j t‖` for a runner's seven differences.

**Equioscillation.** At any interior maximum of `f`, **at least two constraints are active.**

*Proof.* Between breakpoints `f` is a minimum of linear functions, hence concave. If a single
constraint were active at an interior point, `f` would be differentiable there with
`f′ = ±d_j ≠ 0` — impossible at a maximum. ∎

**Corollary — the candidates are pairs.** If `‖d_a t‖ = ‖d_b t‖` then `d_a t ≡ ±d_b t (mod 1)`, so
`(d_a ∓ d_b)·t ∈ ℤ` and

    t = k/(d_a + d_b)      or      t = k/(d_a − d_b)

At `t = k/(d_a+d_b)` the two are automatically equal, with common value
`‖k·d_a/(d_a+d_b)‖`. ∎

## 3. What it does to the problem

| | old frame | new frame |
|---|---|---|
| the unknown | a time in a continuum | a **pair** `(a,b)` and an integer `k` |
| candidates per runner | unbounded, cascading | **21 pairs** |
| value at a candidate | evaluate and see | `‖k·d_a/(d_a+d_b)‖`, **explicit** |

**Verified on two independent routes.** Pair candidates attain the true maximum: **1,760 of
1,760** (checked against BSM breakpoints) and **4,000 of 4,000** (checked against an independent
fine scan). They reach `1/8`: **3,200 of 3,200**.

So LRC(8) for a runner becomes: *some pair of its differences, with some `k`, gives
`‖k·d_a/(d_a±d_b)‖ ≥ 1/8` while the other five stay clear.*

## 4. The AP, in the new frame

Its maximum is at `t = 1/8` where `d = 1` and `d = 7` tie. And `1 + 7 = 8`, so
`t = 1/(d_a + d_b)` with `k = 1`.

**The spine is the equioscillation point of the extreme pair.** That is why the AP attains exactly
`1/8` and not a fraction more — the tie is between the two differences whose sum is `n`. All three
pairs summing to 8 work: `(1,7)`, `(2,6)`, `(3,5)`, each giving `t = 1/8`.

## 5. A guess, refuted  `[REFUTED]`

> the carrying pair satisfies `8 │ (d_a ± d_b)`

**False.** Over 7,200 runner-instances the first pair found has a denominator divisible by 8 in
only **13.8%**. The AP's pairs do, which is what suggested it, and that generalised wrongly —
the same mistake as reading the `8/i` profile off the AP earlier in this session.

## 6. Status

`[PROVED]` §2, both statements.
`[VERIFIED — 1,760 and 4,000, two routes]` §3's reduction.
`[REFUTED]` §5.
`[OPEN]` which pair carries the witness, and why one always does.

**n = 8 is not proved here.** What is new is the location of the unknown: no longer a point on the
time axis, but a pair of differences and an integer, with the value at that candidate given in
closed form.
