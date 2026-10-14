# Referencing any arrangement to a grid — how far it actually reaches

2026-09-13. n = 8, individual isolation, threshold 1/8. Tests the founding frame of the series:
that every arrangement can be referenced to an AP or grid.

---

## 1. The theorem  `[PROVED — arithmetic]`

For runner `i`, let `m = d_min(i)`.

> **If `m` divides every difference `|v_i − v_j|`, then `s = d/m` is an integer, the band test
> collapses, and**
>
>     lonely at 1/(8m)   ⟺   no difference is ≡ 0 mod 8m
>
> Residues mod `8m` settle it. **No grid assumption.**

**Proof.** `s = d/m ∈ ℤ`, and `dist(s, 8ℤ) < 1` for integer `s` means `s ≡ 0 mod 8`, i.e.
`d ≡ 0 mod 8m`. ∎

Checks: **5,464 of 5,464** where the hypothesis holds; and in the special case `m = 1` (integer
speeds, runner with a neighbour one step away), **7,152 of 7,152** — of which **7,112 were in
non-grids**.

So the grid reference is not confined to grids. It reaches every runner whose own `d_min` divides
its difference set.

## 2. Its reach shrinks with span  `[VERIFIED]`

| speeds drawn from | `d_min` divides all | `d_min = 1` alone |
|---|---|---|
| `[1,12)` | **0.888** | 0.888 |
| `[1,16)` | 0.734 | 0.734 |
| `[1,40)` | 0.329 | 0.328 |
| `[1,200)` | 0.074 | 0.072 |
| `[1,600)` | **0.024** | 0.024 |

Two readings. The reference covers most of a tight configuration and almost none of a spread one.
And the divisibility hypothesis adds essentially nothing beyond `d_min = 1` — for a random integer
set, `m > 1` dividing every difference would force the whole configuration into `m·ℤ`, which is
rare.

## 3. But it is strongest exactly where the difficulty is  `[VERIFIED]`

The series located the low counts at small span. Sampling small spans and bucketing by the
configuration's floor:

| floor | configurations | runners settled by residues | mean span |
|---|---|---|---|
| **≤ 2** (the dangerous ones) | 835 | **0.899** | 9.2 |
| 4 | 2,427 | 0.857 | 10.5 |
| ≥ 6 (comfortable) | 2,738 | 0.663 | 13.9 |

**Lower floor ⟹ tighter configuration ⟹ more runners with a distance-1 neighbour ⟹ more of them
settled by residues alone.** The reference's coverage is not uniform, and the part it covers best
is the part that matters.

## 4. What this does and does not give

| | |
|---|---|
| any arrangement can be referenced to a grid | **yes** — and where the reference is exact (`m \| d`), residues decide, proved |
| the reference reaches beyond grids | **yes** — 7,112 of 7,152 checked cases were non-grids |
| it covers the dangerous configurations | **yes** — 0.899 at floor ≤ 2 against 0.663 at floor ≥ 6 |
| it covers everything | **no** — 2.4% of runners at span 600, and the divisibility hypothesis is what fails |
| it closes the open first-interval claim | **no** — that claim is about where the moment lands *after* blocking, which is exactly the case the reference does not reach |

## 5. Status

`[PROVED — arithmetic]` §1.
`[VERIFIED — 5,464 and 7,152]` §1's checks.
`[VERIFIED]` §2's reach table; §3's floor buckets.

**Not established.** The case `m ∤ d` — where `s` is non-integral and residues have nothing to
grip. That is the same gap as `ANALYTIC_STATUS_v1` §2 and `GRID_DENSITY_LIMIT_v1` §4, reached from
a third direction.

**n = 8 is not proved here.**
