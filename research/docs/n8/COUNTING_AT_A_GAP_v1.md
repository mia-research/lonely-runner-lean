# The framework's proof: counting at a gap

2026-09-14. Working notes on the two remaining obligations of `PROOF_REQUIREMENTS_v2` §7.
**Nothing here is in the manuscript, which stays frozen at v7.**

---

## 1. The setting, fixed

At gap `D` the candidates are the **odd** `a` taken mod `8D` — **exactly `4D` of them**,
since the test depends only on `a mod 8D`. Difference `e` blocks candidate `a` when
`(a·e mod 8D)` falls outside the band `[D, 7D]`.

So at a chosen gap the whole question is finite: `4D` candidates, seven blocked sets, and
the construction returns iff their union misses one.

## 2. Two closed forms, one new

| | closed form | says |
|---|---|---|
| **dead** (§7c) | `Dead` = divisors of `{d/8 : 8 \| d}`; `L_0` the first live gap | this gap is hopeless |
| **free** (new) | `m = 8D/gcd(e, 8D)` is **even** and `m ≤ 8` | this difference cannot block you here |

*Derivation of the free test.* `a·e mod 8D = h·(a·(e/h) mod m)` with `h = gcd(e,8D)`. If `m`
is even, an odd `a` keeps `a·(e/h)` odd mod `m`, so the orbit is `h·{odds mod m}` — least
`h`, greatest `h(m−1)`. Requiring `h ≥ D` and `h(m−1) ≤ 7D` both reduce to `m ≤ 8`. If `m` is
odd, odd `a` reaches every residue mod `m`, so `0` is in the orbit and `e` blocks.
`[PROVED — checked over 2,600 (e,D) pairs, 0 disagreements]`

**Its usable corollary:** if `D | e` and `e/D` is **odd**, then `e` cannot block at gap `D`,
whatever candidate is taken. That is the `m = 8` case.

*Two things this corrected.* Powers of two are the wrong direction — the blocked fraction
sits at exactly `1/4` for `D = 2, 4, 8, 16`. And the natural guess `gcd(e,8D) ≥ D` is false:
at `D = 3`, `e = 8` has `gcd = 8 ≥ 3` but the candidate `a = 3` gives `8·3 ≡ 0 (mod 24)`.
**`a` is only odd, not coprime to `8D`** — the parity of `m` is what decides it.

## 3. A worked rule, proved by counting

`j = 1`, normalised `g = 1`: one difference `d₁` with `8 | d₁`, six without. At gap `D = 2`
the candidates are the eight odd residues mod 16 and the band is `a·e mod 16 ∉ {0,1,15}`.

- `d₁ = 8m` gives `a·d₁ mod 16 = 8·(am mod 2)` — always `8` when `m` is odd, always `0` when
  `m` is even. So `d₁` **clears everywhere** iff `d₁ ≡ 8 (mod 16)`.
- an **even** difference never blocks: `a·e` is even, so never `1` or `15`.
- an **odd** difference blocks **exactly two** candidates, `a ≡ ±e⁻¹ (mod 16)`.

> **Rule.** If `d₁ ≡ 8 (mod 16)` and at most three of the other six are odd, at most `6 < 8`
> candidates are blocked and one survives. `[PROVED — 2,005 runners met the hypothesis,
> conclusion held in all 2,005]`

## 4. How far counting reaches

Bounds computable from the sets, no search over candidates:

| bound | fires for |
|---|---|
| `Σ` blocked fractions `< 1` | **62.3%** |
| `Σ − max pairwise overlap` | **84.3%** |
| `Σ − (2/7)·Σ` all 21 pairwise overlaps | 85.9% |
| better of the last two | **86.8%** |

The max-overlap term is valid and elementary: candidates shared by two blocked sets are
double-counted in the sum, so `|union| ≤ Σ|Aᵢ| − max|Aᵢ ∩ Aⱼ|`. **One term closed more than
a fifth of all runners.**

## 5. Why the remaining 13.2% resists, exactly

The uncovered example `[79, 120, 159, 165, 266, 303, 323]` at its first clearing gap `D = 2`:

| | |
|---|---|
| candidates | 8 |
| `Σ` fractions | `1.250` |
| `Σ − max pair` | `1.000` — misses by a single candidate |
| true union | `0.750` — candidates `7` and `9` survive |
| multiplicity profile | `{0: 2, 1: 4, 3: 2}` |

**The overlap is concentrated, not spread.** Two candidates are blocked three times each;
four are blocked once; two not at all. The true excess is `E = Σ(m−1) = 4`, while
`Σ − (2/7)·P` credits only `1.71`.

The `2/k` factor comes from `C(m,2) ≤ (k/2)(m−1)` with `k = 7`, and the exact relation is
`E ≥ 2P/m_max`. Here `m_max = 3`, which would give `E ≥ 4` — **exactly right**. So the bound
is lossy only because it assumes the worst-case multiplicity, and the real profiles are far
from worst case.

## 6. Where this goes

The obligation is now a bound on the **excess** `E`, and there are two routes:

1. **Bound `m_max`.** If the maximum multiplicity can be bounded below 7 from the differences,
   `E ≥ 2P/m_max` sharpens immediately. Every profile observed has been far from 7.
2. **Closed forms for the intersections.** `|Aᵢ ∩ Aⱼ|` should be computable from
   `(eᵢ, eⱼ, D)` the way the single-set size is computable from `gcd(e, 8D)`. If the
   intersections have closed forms, the whole profile does, and the union is exact rather
   than bounded.

Route 2 is the one that would finish it: with exact intersections the counting is not a bound
at all but a computation in the differences, and "the construction returns" becomes a
statement about `gcd`s rather than about a search.

**Nothing here proves the claim.** It reaches 86.8% by counting alone, with two closed forms
and no search, and names precisely what the remaining cases need.
