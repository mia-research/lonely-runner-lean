# The `|J| = 3` frontier reduced to a denominator bound plus a finite list

First real work on an open frontier since the reductions. It also corrects an object I had been
measuring wrongly for several turns.

## Correction: the frontier is about flanks, not readings

`CATEGORIES_v2` and `DIFFICULTY_MAP_v1` partition profiles by `k`, the number of non-integer
**readings** `dᵢ/d_min`. **Theorem 6.9 and Proposition 6.10 are not about that.** They are about a
**flank** — a subject difference `e` — and count the non-integer **ratios** `ρⱼ = dⱼ/e` at that flank.
Call it `|J|`. The two objects are unrelated, and the target list's "3+ non-integer ratios" means
`|J| ≥ 3`, not `k ≥ 3`.

Measured on the right object, over 20,000 random 8-speed arrangements, by the minimum `|J|` over live
flanks: `|J| = 0` (all-integer ratios, decided immediately) **19.2%**; `|J| = 1` (Theorem 6.9)
**1.9%**; `|J| = 2` (Prop 6.10) **6.5%**; **`|J| ≥ 3`: 72.5%** — the open region.

## Why `|J| = 3` is not closed by counting, precisely

Each mover's bad set has density `2/n = 1/4`, so three give `3/4 < 1` and clear openings are
abundant. That is not the obstruction. **Prop 6.11 was withdrawn for naming an opening without
bounding it** — register items 4 and 27. The gap is an **index bound**.

And the density itself is conditional: `1/4` holds for an **equidistributed** fractional part. For
rational `f = p/q` the orbit is `q` points and the density can be far higher. That is exactly where
shadowing lives.

## The two-part reduction

**Part 1 — a denominator bound with an index bound.** Over 2,648 live `|J| = 3` flanks:

> **every shadowed flank has all three fractional parts of denominator `≤ 4`** — **0 exceptions**;
> and where some denominator is `≥ 5`, a clear opening exists at index **`k ≤ 8`**.

Index distribution for `max denom ≥ 5`: `k = 0` in 301 cases, `1` in 197, `2` in 110, `3` in 57,
`4` in 25, `5` in 5, and single cases at `7` and `8`. Nothing beyond 8.

Clear flanks reach denominator 30; shadowed ones never exceed 4.

**Part 2 — the residue is finite, and enumerated.** Denominators `≤ 4` means fractional parts in
`{1/2, 1/3, 2/3, 1/4, 3/4}`, and only `ρ/8 mod 1` enters, so whole parts matter only mod 8. The
configuration space is `5³ × 8³ = 64,000`, enumerated completely:

> **1,488 shadowing configurations (2.325%), in exactly 12 fractional-part multisets.**

| multiset | count | | multiset | count |
|---|---|---|---|---|
| `(1/2,1/2,1/3)` | 192 | | `(1/2,1/4,1/4)` | 96 |
| `(1/2,1/2,2/3)` | 192 | | `(1/2,3/4,3/4)` | 96 |
| `(1/2,1/2,1/4)` | 192 | | `(1/3,1/3,2/3)` | 72 |
| `(1/2,1/2,3/4)` | 192 | | `(1/3,2/3,2/3)` | 72 |
| `(1/2,1/4,3/4)` | 192 | | `(1/3,1/3,1/3)` | 24 |
| `(1/2,1/2,1/2)` | 144 | | `(2/3,2/3,2/3)` | 24 |

Structure worth recording: eight multisets contain a `1/2`, four are pure thirds, **no configuration
mixes denominators 3 and 4**, and **pure quarters cannot shadow at all**. This extends the
manuscript's own half-integer enumeration at `|J| = 2` (all shadowing pairs to denominator 14 have
both parts `1/2`) to `|J| = 3`.

## What closing `|J| = 3` now requires

1. **Prove**: a live `|J| = 3` flank with some fractional part of denominator `≥ 5` has a clear
   opening at index `≤ 8`. Currently `[VERIFIED]`, 2,648 flanks, 0 exceptions.
2. **Discharge** the 12 multisets — a finite list, already enumerated.

Both are index-bounded, so neither falls foul of the withdrawal that removed Prop 6.11.

## Status

`[VERIFIED]`, not proved: the denominator bound and the index bound (2,648 flanks).
`[EXHAUSTIVE]`: the 64,000-configuration enumeration and its 12 multisets.
`[CORRECTED]`: `|J|` (flank ratios) is not `k` (profile readings); the earlier difficulty map measured
the wrong object for this frontier.
Existence at order 8 unchanged.
