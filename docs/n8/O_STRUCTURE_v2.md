# The measure `o`: the resonance characterisation, and (H′) reduced to one bound

2026-09-08. **Supersedes `O_STRUCTURE_v1.md`**, whose §3 claimed the translates
`8q+(1,3,5,7)` have `o = 1/4` *exactly*. That is **false** — it was a rounding artefact.
They approach `1/4` strictly from above and never attain it: `q = 1, 2, 3, 5, 10, 25,
50, 101` give `0.2775, 0.2544, 0.2523, 0.2509, 0.2505, 0.25009, 0.250011, 0.2500027`,
each verified `≠ 1/4` in exact rational arithmetic. Everything else in v1 stands.

Scripts `experiments/n8/hp_*.py`. Exact rational arithmetic; cells evaluated at their
**entry** point, never a midpoint.

## 1. Carried over from v1, unchanged  `[PROVED]`

For `ρ₀ = 4`: `[0,1)` splits into `A_even, A_odd, A_none` (densities `1/4, 1/4, 1/2`) by
`t_4 mod 8`, and `|S^c| = |A_none ∩ U| + 2|A_even ∩ O|`.

- **(B2)** `|S^c| ≤ o + min(o, 1/4)`, so **`o ≤ 1/4 ⟹ closes`**. Raises a-priori
  coverage from 97.60% to 98.36% over primitive unit 4-tuples with `q ≤ 6`.
- Sharper: `|S^c| ≤ o + α − β` with `α = |A_even ∩ O|`, `β = |A_odd ∩ O|`; since
  `β → o/4`, closure holds once **`o ≤ 1/3`**.
- **Product Law**: `x ∈ O ⟹ s_1s_3s_5s_7 ≡ 1 (mod 8)`, because `O` is exactly
  `{ρ ↦ s_ρ·ρ is a bijection of (ℤ/8)^×}` and `1·3·5·7 ≡ 1`. Verified cell by cell,
  0 violations over 1278 tuples. **Not** a route to the bound: `|Π|` reaches ≈0.64.

## 2. The resonance characterisation  `[EMPIRICAL — exhaustive over the stated range]`

Call a `±1` vector `(σ_ρ)` a **relation** for `(e_1,e_3,e_5,e_7)` if `Σ σ_ρ e_ρ = 0`.
These are exactly the smallest resonances that can obstruct equidistribution of the
joint floor vector, and they are what the extremal tuples have:

    (1,3,5,7)   :  1 − 3 − 5 + 7 = 0
    (1,11,5,7)  :  1 + 11 − 5 − 7 = 0
    8q+(1,3,5,7):  inherits (1,−1,−1,1)

Over all **2372** primitive unit 4-tuples with `q ≤ 6`:

| | count | max `o` |
|---|---|---|
| **no** `±1` relation | 1936 | **`186/595 ≈ 0.31261 ≤ 1/3`** — at `(17,3,5,7)` |
| has a `±1` relation | 436 | `16/35 ≈ 0.4571` — and only **two** exceed `1/3` |

The two are exactly `(1,3,5,7)` (`o = 16/35`, relation `(1,−1,−1,1)`) and `(1,11,5,7)`
(`o = 26/77`, relation `(1,1,−1,−1)`). The third-largest is `(1,3,13,15)` at
`58/195 ≈ 0.2974 < 1/3`.

Independently: generic large tuples give `o → 3/32 = 0.09375` (six random tuples with
speeds in the hundreds: `0.0917…0.0943`), matching the count of `4! = 24` good
`s`-vectors out of `4^4 = 256`, confirmed directly as `384/4096` over the floor states.

And: **`min(e_ρ) ≥ 3 ⟹ o ≤ 186/595 < 1/3`**. Only `e_1 = 1` — which freezes `t_1 = 0`,
hence `s_1 = 1`, removing a degree of freedom — permits `o > 1/3`. Both exceptions have
`e_1 = 1`, and max speed among them is 11.

## 3. What this reduces (H′) to

> **(H″)** `o ≤ 1/3` for every primitive unit 4-tuple other than `(1,3,5,7)` and
> `(1,11,5,7)`.

`(1,11,5,7)` has `u = 0`, so it closes by the `u = 0` bound; `(1,3,5,7)` is the
representative tuple already closed by Lemma D. So (H″) finishes the leaf.

**And (H″) now has a named mechanism.** Writing `s_ρ = 2a_ρ+1` with
`a_ρ = ⌊e_ρ x/2⌋ mod 4`, the two Klein components of `s_ρ` are `⌊e_ρx/2⌋ mod 2` and
`⌊e_ρx/4⌋ mod 2`, and

    o = Σ over the 24 good s-vectors of | ⋂_ρ {a_ρ = c_ρ} | ,

an intersection of four periodic sets of density `1/4` and periods `8/e_ρ`. Each term is
`1/256` plus an error governed by the resonances `Σ j_ρ e_ρ ≡ 0`; the `±1` relations are
the smallest, and §2 shows they are precisely where `o` departs from `3/32`. So (H″) is
a discrepancy statement whose extremal families are now identified rather than guessed.

## 4. Grades

§1 (the identity, (B2), the Product Law): **PROVED**. §2: **EMPIRICAL**, exhaustive over
primitive unit 4-tuples with `q ≤ 6` (speeds ≤ 55), plus sampling at speeds in the
hundreds. (H″): **OPEN**. The v1 claim that translates give exactly `1/4`:
**RETRACTED** — they converge to it strictly from above.
