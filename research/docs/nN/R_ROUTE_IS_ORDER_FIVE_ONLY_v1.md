# The `R < n−1` route is available at order five and nowhere above it

2026-09-21, version 1. Answers two questions put by the owner: whether the failed bootstrap is
*circular* or merely *`n`-dependent*, and whether a constant found cheaply at five replicates at
higher orders.

Artefacts: `experiments/nN/certificate_nN_v1.{py,out}` (the order-5 certificate parameterised in
`n`) · `order5_alpha_v1.{py,out}` · `order5_sigma_v1.{py,out}` · `order5_recursion_v1.{py,out}`

---

## 1. Not circular — a bootstrap with an `n`-dependent contraction factor  `[CORRECTION]`

`UNBOUNDED_RATIO_v1.md` §3 called the uniform-ceiling argument circular. That was wrong. It is a
**bootstrap**, and bootstraps are legitimate; what matters is whether the map contracts.

If `R < B` then a setter of reading `u` occupies only laps `Q ≤ u·B/n`, so it makes at most
`u·B/n` moves, each advancing `R` by less than `2/u` (the recursion of
`UNBOUNDED_RATIO_v1.md` §1). Its total contribution is therefore at most `2B/n`, **independent of
`u`**. With `k` setters,

> `B = 1 + 2kB/n`,  which has a fixed point iff  `2k/n < 1`.

A subject at order `n` has `k = n − 2` setters (`d_min` never sets), so the condition is
`2(n−2)/n < 1`, i.e. **`n < 4`**. The bootstrap converges at `n = 3` and diverges from `n = 4`.
That is an explicit `n`-dependent failure with a computable margin — at `n = 5` the factor is
`6/5 = 1.2` — not a logical defect.

**The quantified target it yields.** Write `α` for the fraction of its nominal budget a setter
actually uses, `α = m/(u·B/n)`. The fixed point falls below 4 iff `2kα/n < 3/4`:

| order | setters `k` | `α` must be below |
|---|---|---|
| 3 | 1 | 9/8 — always true, which is why order 3 closes |
| 5 | 3 | **5/8 = 0.625** |
| 8 | 6 | 1/2 |

Measured at `n = 5` over every realisable word (`S = 14`): **max `α = 55/72 = 0.7639`**, above
5/8. It is exceeded rarely — 42 of ~2,000 setter-instances — and the offending word
`(1,1),(2,1),(3,1),(1,2),(2,2)` has true `R = 3.3611`, well under 4. So the uniform-`α` bootstrap
fails, but only on words that are nowhere near extremal.

The companion condition `Σ_moves 1/u < 3/2` fails by a hair: **max `Σ = 113/72 = 1.5694`**
against `3/2 = 1.5`. The per-move constant `2/u` is exactly tight (the setter's own position
moves by less than `2/n` in its units, and that is attained), so no sharpening of the constant
alone will close a gap of 0.07 — the two quantities must be bounded *jointly*, since the words
that maximise `Σ` have small `R` and vice versa.

---

## 2. The constant does not replicate — `R < n−1` is order-five-only  `[PROVED at n = 5; REFUTED as a route at n = 6]`

The order-5 certificate was parameterised in `n` (`certificate_nN_v1.py`: `K = n − 2` unknowns,
lap bound `L = ⌊((n−1)S − 1)/n⌋`, threshold `n − 1`). **Control:** at `n = 5, S = 10` it
reproduces the deposited result exactly — 6,036 words, `sup R = 31/9`, the same extremal word,
the same margin `24/821`.

| order | `S` | words | realisable | sup `R` | threshold `n−1` | verdict |
|---|---|---|---|---|---|---|
| 5 | 10 | 6,036 | 402 | `31/9 = 3.4444` | 4 | **below — route live** |
| 6 | 5 | 25,804 | 3,688 | `1482/187 = 7.9251` | 5 | **above — route dead** |

At order 6 the relaxation's supremum exceeds its own threshold by more than half again. The
extremal word is long — twelve moves, all four setters, laps to 4 — where at order 5 it is six
moves and laps to 6.

**This is not an artefact of the relaxation being loose.** The certificate bounds the true
supremum from *above*, so `7.93 > 5` alone would leave room for the true value to sit below 5.
It does not: the manuscript's §8.2 annealing maxima on the nearest reading are **8.60, 9.04,
11.66, 10.66 at `n = 6, 7, 8, 9`**, and a separate search on `R` at order 8 reaches **11.96** —
all far above their thresholds `n − 1 = 5, 6, 7, 8`. Relaxation and direct search agree.

So `sup R < n − 1` is **true at `n = 5` and false from `n = 6`**, and order five is the last
order at which this sufficient condition is available at all. The manuscript's own caution —
*"`R < 4` is a stronger statement than Existence needs (audit R1)"* — is the same fact from the
other side.

---

## 3. What this means for the programme

**For order five.** The `R < 4` route is live and the remaining gap is small and explicit: the
certificate proves it for ratio `≤ 30`, and closing unbounded ratio needs a joint bound on
`(Σ, R)` rather than either alone (§1).

**For order eight — a negative worth having.** Do not look for `R < n − 1` at eight. It is false
by two independent measurements, and any argument shaped like "bound the first-isolation instant
in `d_min` laps" is bounded below by 11.96 there against a threshold of 7. Effort on `R` at
eight is effort on a statement that does not hold.

**On finding `n`-independent constants at five.** The owner's method is sound and this run is
evidence for it — the certificate ports in one afternoon and the `n = 5` control reproduces
exactly, so cross-order tests are cheap. The specific constant probed here, however, is *not*
`n`-independent: the contraction factor is `2(n−2)/n`, which rises through 1 at `n = 4` and
tends to 2. What *is* order-independent is the machinery — the recursion `R_new < R_prev + 2/u`,
the inertness of large readings, and the two-regime decomposition of the certificate
(`ORDER5_CERTIFICATE_STRUCTURE_v1.md` §4).

---

## 4. Grades

| claim | grade |
|---|---|
| the bootstrap contracts iff `2(n−2)/n < 1`, i.e. `n < 4` | `[PROVED — arithmetic]` |
| `α` threshold: 5/8 at `n = 5`, 1/2 at `n = 8`, 9/8 at `n = 3` | `[PROVED — arithmetic]` |
| max `α = 55/72` at `n = 5`, `S = 14` | `[VERIFIED — exhaustive over realisable words]` |
| max `Σ = 113/72 > 3/2` | `[VERIFIED — exhaustive]` |
| `sup R = 31/9 < 4` at `n = 5` | `[PROVED — certificate, ratio ≤ 30]` |
| `sup R = 1482/187 > 5` at `n = 6`, `S = 5` | `[VERIFIED — parameterised certificate, control passed]` |
| `R < n−1` fails from `n = 6` | `[VERIFIED — relaxation and the manuscript's annealing agree]` |
| order five, unbounded ratio | **`[OPEN]`** |

**Scope.** `n = 6` was run at `S = 5` only; the supremum there can only rise with `S`, so the
"route dead" verdict is safe in the direction claimed. `n = 7` was still running when this was
written. All arithmetic is exact rational.
