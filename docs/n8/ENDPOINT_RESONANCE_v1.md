# The second resonance — the wolf note in the endpoint lattice

2026-09-11. Script `experiments/n8/ok_wolf_period_v1.py`. Exact `Fraction`, no float.

---

## 1. Two species of resonance, and I had been tracking only one

Everything in this project called a resonance so far has been **additive**: an integer
relation `p·e = 0` among the speeds, graded by height `∏|p_j|` or by relation count. Those
are exactly the statistics that **failed** to read the extremum's deficit —
`RESONANCE_FACTOR_v1` §2 (count non-monotonic) and §4 (the lowest-height Fourier families
give the *wrong sign*).

The statistic that does read it, `α`, is built from something else. By
`ALPHA_CLOSED_FORM_v1` §1,

    α_x = 1/4 + S_x /(x·|G|),     S_x = Σ_i [ ψ({x v_i}) − ψ({x u_i}) ]

over the **endpoints** `(u_i, v_i)` of `G(H)`. Every endpoint is `(8k±1)/(8e)` with `e ∈ H`,
so its denominator divides `8L`, `L = lcm(H)`. Therefore `{x u_i}` depends on `x` only
through `x mod 8L`:

> **`S_x` is periodic in `x`, with period dividing `8·lcm(H)`.**  `[PROVED]`

This is a **multiplicative** resonance between the speed and the grid's endpoint lattice.
It is not an additive relation, it is not graded by height, and it is invisible to relation
counting. **That is the resonance that was not being taken into account.**

**Measured periods** (exact, smallest period found):

| `H` | `L` | `8L` | period | `8L`/period |
|---|---|---|---|---|
| `{2,6,8,10,14}` (the `E*` grid) | 840 | 6720 | **2240** | 3 |
| `{1,3,4,5,7}` (its base) | 420 | 3360 | **1120** | 3 |
| `{1,2,3,4,5}` | 60 | 480 | **480** | 1 |

## 2. Free speeds are finite, with an explicit bound  `[PROVED + verified]`

`α_x = 0` means `A_x ∩ G(H) = ∅`: the speed `x` can be added to `H` at **zero cost**,
`G(H ∪ {x}) = G(H)`. From the closed form, `α_x = 0 ⟺ S_x = −x|G|/4`, and `|S_x| ≤ 3N/16`
(`|ψ| ≤ 3/32`, `N` components). Hence

> **`α_x = 0` ⟹ `x ≤ 3N/(4|G|)`** — only finitely many free speeds, with an explicit bound.

| `H` | bound `3N/(4\|G\|)` | free speeds found | max | within bound |
|---|---|---|---|---|
| `{2,6,8,10,14}` | `3360/41 = 81.95` | `2,3,6,8,10,14,16,20,28,32,42` | 42 | yes |
| `{1,3,4,5,7}` | `1680/41 = 40.98` | `1,3,4,5,7,8,10,14,16,21` | 21 | yes |
| `{1,2,3,4,5}` | `216/7 = 30.86` | `1,2,3,4,5` | 5 | yes |

The members of `H` itself are free trivially. **Self-similarity:** the `E*` grid's
non-trivial free set `{16,20,28,32,42}` is exactly `2 ×` the base's `{8,10,14,16,21}`,
matching the dilation identity of `ALPHA_v1` §4.

## 3. Where the wolf sits

`α_x − 1/4 = S_x/(x|G|)` is a **bounded periodic function under a `1/x` envelope**. So the
large deviations — the ones that produce a deficit — require `S_x` already large at **small**
`x`. `S_x` is large only when the terms align: `{x v_i}` near `1/8` (where `ψ` is maximal)
and `{x u_i}` near `7/8` (minimal) **simultaneously, for every component**. That is a
coherent simultaneous approximation of the whole endpoint lattice by `x` — the wolf note:
not one resonance, but every endpoint resonating together at one speed.

Measured for the `E*` grid: `max|S_x| = 217/160` at `x = 238`, against the a-priori
`3N/16 = 3/2` — so the bound is 90% attained, but at `x = 238` the `1/x` envelope has
already crushed it (`α − 1/4 = 0.078`). The deficit-carrying speeds are the small ones:
`α_7 − 1/4 = 0.189` from `S_7 = 31/320`, `α_22 − 1/4 = 0.406` from `S_22 = 733/1120`.

## 4. Why this reframes the earlier negatives

- Height and relation count measure **additive** resonance. `ALPHA_v1` §2 found they cannot
  order the deficit while `α` can, and §1 above says why: they are measuring a different
  species.
- `RESONANCE_FACTOR_v1` §4 found the two lowest-height families at `E*` give the **wrong
  sign**. Consistent: those are additive resonances, and the deficit is carried by the
  endpoint resonance.
- `ALPHA_CLOSED_FORM_v1` §3's a-priori criterion fired 0/509 because `C = 3N/(16|G|)` uses
  the *worst case* of `S`. §1 says `S` is periodic, so `C` is really `max|S_x|/|G|` over one
  period — an exactly computable constant, `18.52` rather than `20.49` here. A 10%
  improvement: real, and not enough.

## 5. Ledger

`[PROVED]` §1 the periodicity and its period-divides-`8L` derivation; §2 the finiteness of
free speeds and the bound `3N/(4|G|)`.
`[VERIFIED — exact]` the three period values, the three free-speed lists, the bound in each
case, and the `2 ×` self-similarity.
`[EMPIRICAL]` §3's `max|S_x|` figures, computed over one period.

`n = 8` is **not proved.** What is new is the identification of a **second, multiplicative
species of resonance** — between a speed and the grid's endpoint lattice, periodic mod
`8·lcm(H)` — which is what `α` measures and what the additive statistics could never see.
