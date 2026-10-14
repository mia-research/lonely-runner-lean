# The measure `o`, and (H′) reduced to a single bound

2026-09-08. Continues `STATUS_n8_ANALYTIC_v1.md` §3. Scripts
`experiments/n8/hp_{apriori,dichotomy,olarge,product,minspeed}_v1.py`. All exact
rational arithmetic, cells evaluated at their **entry** point, never a midpoint.

## 0. The exact identity

For the hard sub-case `ρ₀ = 4`: `e_4 = 4w` with `w` odd, and
`bad(e_4,t)` = evens if `t ≡ 0,7 (mod 8)`; odds if `t ≡ 3,4`; empty otherwise. So
`[0,1)` partitions into `A_even` (`t_4 ≡ 0,7`), `A_odd` (`t_4 ≡ 3,4`) and `A_none`
(`t_4 ≡ 1,2,5,6`), of densities `1/4, 1/4, 1/2`. With
`O = {x : the four units block all four odd residues}`, `o = |O|`; `V` likewise for
evens (`|V| = o` by `x ↦ 1−x`); `U = O ∩ V`, `u = |U|`:

    |S^c| = |A_none ∩ U| + |A_even ∩ O| + |A_odd ∩ V| = |A_none ∩ U| + 2|A_even ∩ O|.

`|S| ≥ 1/2` suffices, since the B-lemma gives `|B_{m₁} ∪ B_{m₂}| < 1/2` **strictly**.

## 1. A new a-priori bound  `[PROVED]`

> **(B2)** `|S^c| ≤ o + min(o, 1/4)`. Hence **`o ≤ 1/4 ⟹ |S^c| ≤ 2o ≤ 1/2`**.

*Proof.* `U = O ∩ V ⊆ O`, and `A_none, A_even` are disjoint, so
`|A_none ∩ U| + |A_even ∩ O| ≤ |A_none ∩ O| + |A_even ∩ O| ≤ |O| = o`; and
`|A_odd ∩ V| ≤ min(|A_odd|, |V|) = min(1/4, o)`. ∎

This is strictly weaker in hypothesis than the previously used `u + 2o ≤ 1/2` (which
forces `o ≤ 1/4`), and it closes more: over primitive unit 4-tuples with `q ≤ 6`,
a-priori coverage rises from **97.60% to 98.36%** (18 further tuples).

**Sharper form.** Writing `α = |A_even ∩ O|`, `β = |A_odd ∩ O|`, `γ = |A_none ∩ O|`
(so `α+β+γ = o`), `|A_none ∩ U| ≤ γ` gives `|S^c| ≤ γ + 2α = o + α − β`. Under
equidistribution `β → o/4` and `α ≤ min(1/4,o)`, whence `|S^c| ≲ (3/4)o + min(1/4,o)`,
which is `≤ 1/2` exactly when **`o ≤ 1/3`**.

## 2. A structural law for `O`  `[PROVED]`

By the pair rule, the unit runner of residue `ρ` blocks the odd residue `−τ_ρ ρ`, where
`τ_ρ` is the odd member of `{t_ρ, t_ρ+1}`. Put `s_ρ = τ_ρ mod 8 ∈ (ℤ/8)^×`. Then

    O = { x : ρ ↦ s_ρ·ρ is a bijection of (ℤ/8)^× }.

> **Product Law.** `x ∈ O ⟹ s_1 s_3 s_5 s_7 ≡ 1 (mod 8)`.

*Proof.* `(ℤ/8)^×` is elementary abelian, and `1·3·5·7 = 105 ≡ 1`. The image of a
bijection is the whole group, so `∏_ρ (s_ρ ρ) = ∏_ρ ρ = 1`, and `∏ρ = 1`. ∎
*Verified:* 0 violations over 1278 primitive tuples, checked cell by cell.

The bijection count is `4! = 24` of `4^4 = 256`, i.e. density `3/32`, confirmed directly
over the `8^4` floor states (384/4096 = 3/32).

**But `o ≤ |Π|` is too lossy** — `Π = {∏s_ρ = 1}` has density `1/4` under independence
and measure up to `≈ 0.64` in practice (322 of 1278 tuples have `|Π| > 1/3`). The
product law is a true structural constraint, not a route to the bound.

## 3. What `o` actually does  `[EMPIRICAL — exhaustive/­sampled over stated ranges]`

| family | `o` |
|---|---|
| generic large tuples | `→ 3/32 = 0.09375` — measured `0.0917…0.0943` on six random tuples with speeds in the hundreds |
| **translates** `8q + (1,3,5,7)`, `q ≥ 1` | `= 1/4` **exactly** (checked at `q = 50, 101`) |
| `(1,11,5,7)` | `26/77 ≈ 0.3377` |
| `(1,3,5,7)` | `16/35 ≈ 0.4571` |

So the `≈ 0.25` plateau seen when tabulating `max o` against the minimum speed is not a
failure of equidistribution — it is the translate family, which sits at exactly `1/4`.

**Two decisive facts.**

- **`min(e_1,e_3,e_5,e_7) ≥ 3 ⟹ o ≤ 186/595 ≈ 0.3126 < 1/3`** (exhaustive, primitive,
  `q ≤ 6`, speeds ≤ 55). Only `min = 1` — i.e. `e_1 = 1`, which freezes `t_1 = 0` and
  hence `s_1 = 1`, removing a degree of freedom — permits `o > 1/3`.
- Over 4036 primitive unit 4-tuples with speeds ≤ 63, **exactly two** have `o > 1/3`:
  `(1,3,5,7)` and `(1,11,5,7)`. Both have `e_1 = 1`, and max speed among them is 11.

**The dichotomy.** Over all 2372 primitive unit 4-tuples with `q ≤ 6`, exactly **one**
has `u > 0` **and** `o > 1/3`: `(1,3,5,7)`. The next largest `o` among `u > 0` tuples is
`186/595 ≈ 0.3126`, and `1/3` sits in the gap. `(1,11,5,7)` has `u = 0`, so it closes by
the `u = 0` bound.

## 4. (H′) reduced

> **(H″)** `o ≤ 1/3` for every primitive unit 4-tuple other than `(1,3,5,7)` and
> `(1,11,5,7)`.

Given (H″), plus §1's sharper bound with a controlled `β`, the leaf closes: `o ≤ 1/3`
handles everything, `(1,11,5,7)` has `u = 0`, and `(1,3,5,7)` is the representative
tuple already closed by Lemma D.

This is a **single scalar bound on one explicitly defined measure**, replacing the
earlier open statement about an infinite family of fibre checks. It is a discrepancy
statement about the joint distribution of `(⌊e_ρ x⌋ mod 8)_ρ`, with the extremal
families now identified: the translates sit at exactly `1/4`, and only the two
`e_1 = 1` tuples exceed `1/3`.

## 5. Grades

The identity of §0, bound (B2), and the Product Law: **PROVED**. The tables of §3 and
the dichotomy: **EMPIRICAL**, exhaustive over the stated ranges (primitive tuples,
speeds ≤ 63) plus sampling at speeds in the hundreds. (H″): **OPEN**.
