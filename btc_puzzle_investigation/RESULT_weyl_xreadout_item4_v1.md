# RESULT — ITEM 4: quadratic (Weyl) phases on the x-readout. FOUR instrument faults; result is LOW-POWER, not a null.

**Date:** 2026-08-01. **Script:** `weyl_xreadout_item4_v1.py`.
**Grade:** `[EMPIRICAL — INSUFFICIENT POWER]`. **This does not bound the channel.**

## 0. Object, and why it is not a rerun of the chirp plane

`H_F(a) = Σ_d F(x([d]G))·e_n(a·d²)`, `F ∈ {χ₂, χ₃, χ₆}` of the x-coordinate — flagged untested in
`masked_structure_findings_v5.md:137`.

The chirp-plane work used `c(d) = χ₂(y_d)`, which is **odd** in `d`, against `e_n(kd²)`, which is
**even**. That parity **mismatch** is exactly what capped the best achievable alignment at `0.16n`
and produced the record's conclusion *"a ±1 sequence cannot track a quadratic phase; the sign is all
it has."* **The x-readout is even in `d`** (`x(−d) = x(d)`), so it is **parity-matched** to the
quadratic phase: that specific obstruction does not apply here.

## 1. Four instrument faults, each caught by a control

**(a) The readout is EQUIVARIANT, not constant.** `χ₃(x(λd)) = χ₃(β)·χ₃(x_d) = ζ·χ₃(x_d)`. A
class-permutation null that assigns one value per orbit destroys the twist. Fixed by re-imposing
`c(λ^k d) = ζ^k v`. (`χ₂` is the `ζ = 1` special case, which is why only it passed initially.)

**(b) The plant was not realisable within the forced symmetry.** Under `d → λd`, `a·d² → aλ²·d²`, so
a **single-frequency** quadratic phase cannot be μ₃-invariant in `d` — the plant was structurally
incapable of aligning and fired 0/4 nearly everywhere. The realisable coherent target is the phase
**summed over the whole frequency class** of `a₀`, which *is* μ₃-invariant.

**(c) The null broke the forced evenness — and made EVERY cell fire.** Parseval gives
`Σ_a|H|² = n·Σ_{d'=±d} c(d)c̄(d')`, which doubles only when `c` is even. μ₃-only orbits put `−d` in a
*different* orbit with an independent value, so null `mean|H|² = n` against data `2n` — a `√2`
deficit that lit up every statistic at every prime at the p-value floor. **The Parseval control was
printed all along and I only ever checked it against the data, never the null draws.** Now checked on
both (`d0.996/n0.996`).

**(d) Frequency classes must match the readout's reality.** `|H(−a)| = |H(a)|` requires `c` **real**
— true for `χ₂` only. For complex `χ₃`/`χ₆` the ± frequency symmetry does not hold and the free set
is μ₃ (`(n−1)/3`), not μ₆.

## 2. Result after all four fixes

Controls pass at every prime: `C-CLASS` OK, `C-PARSEVAL` matched between data and null.

**3 starred cells out of 60 cells at primes where the plant fires — exactly the 3 expected.**
No structure at any readout.

## 3. ⚠ Power — and why this is not a null

**C-PLANT dilution** (fraction of the readout aligned with the class-summed quadratic phase):

| p, readout | 100% | 75% | 50% | 25% | 10% |
|---|---|---|---|---|---|
| 397, `χ₂` | fires | — | — | — | — |
| 433, `χ₂` | fires | fires | — | (spurious) | — |
| 577, `χ₃` | fires | fires | fires | — | — |

> **Detection requires ~50–100% coherent alignment** — as blunt as the retracted `M = 96` interval
> test. **This excludes only a near-total alignment of the readout with a class-summed quadratic
> phase.** It is an **insufficient-power result**, not a null, and it does not bound the channel.

## 4. Scope and what would be needed

`p ≤ 577`, 8 primes, `j = 0` prime-order cyclic curves, `χ₂/χ₃/χ₆` of `x`, pure quadratic phase
`e_n(ad²)`, class-permutation null respecting equivariance + evenness, `R = 300`.

To make this informative the power must be raised the way C.4 raised it — larger `n` (the free class
count grows like `n/6` or `n/3`), and a statistic aggregating across the whole frequency class rather
than order statistics of `|H|`. Until then the parity-matching advantage over the chirp plane is a
**reason to expect more power, not evidence of more power** — it has not yet been converted into a
measured floor better than the y-readout's.

## 5. Method note

Four faults in one object, all caught by controls, none by reading the code. The most dangerous was
(c): it produced `p = 0.0066` on every statistic at every prime — a maximally "significant" result
that was purely a `√2` normalisation error in the null. **A control printed but applied to only one
arm of the comparison is not a control.**
