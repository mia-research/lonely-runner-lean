# Where Existence is unsettled, and why the dyadic route's closure was an artefact

2026-09-18. Artefacts: `experiments/n8/naming_denominator_v1/`. Everything here is about
`ExistenceAt8` — **an** isolation, not the first and not all.

---

## 1. Where Existence stands

`ExistenceAt8` is **open**: `exact?` cannot close it and no term of it exists in the tree.

| | status |
|---|---|
| integer `ds`, no difference divisible by 8 | **`[PROVED]`** — `Flanks.lonely_at_inv_of_not_dvd`, witness `t = 1/8`. Coverage **0.3921** of primitive 7-sets |
| integer `ds`, some difference divisible by 8 | open — a named instant always found in practice, none proved in general |
| non-integer `ds` | open — `exists_lonely_of_smul` handles commensurable rescaling only |

So a proved, self-contained rule settles **39.2% of integer difference sets and no others**. Everything
else rests on `lonely_at_named_instant`, which is a *criterion*: it settles a set once someone supplies
the pair `(c, k)`.

## 2. The naming denominator, and the dyadic comparison

An instant is named as `(8k+1)/(8c)`. `DYADIC_DEPTH_RESULT_v1` closed the route that restricted the
denominator to a **power of two** — `t = a/2^κ`, `a` odd — because `κ` grew: `κ = 7, 8, 8, 9, 10` for
`V = 50 … 800`, i.e. `κ ≈ log₂V`, so the denominator `2^κ` grows **linearly in `V`**.

**That restriction was doing the damage.** Powers of two are the case `c = 2^j`. Comparing directly,
same sets, same criterion:

| `V` | max **general** `c` | max **power-of-two** `c` | ratio |
|---|---|---|---|
| 50 | 8 | 32 | 4.0× |
| 100 | 12 | 32 | 2.7× |
| 200 | 10 | 32 | 3.2× |
| 400 | 11 | 64 | 5.8× |
| 800 | **11** | **128** | **11.6×** |

The power-of-two denominator doubles; the general one does not move.

## 3. How the general denominator actually grows  `[EIGHTH sampler failure]`

**Random sampling says flat**, across a thousand-fold range of `V`:

| `V` | 50 | 200 | 800 | 3,200 | 12,800 | 50,000 |
|---|---|---|---|---|---|---|
| median `c` | 2 | 2 | 2 | 2 | 2 | 2 |
| 90th | 5 | 5 | 5 | 5 | 5 | 5 |
| max `c` | 10 | 10 | 11 | 13 | 11 | 13 |

**Hunting says otherwise**, and hunting is right — sampling has understated the worst case seven times
before this:

| scale | hunted max `c` |
|---|---|
| 200 | 13 |
| 2,000 | 17 |
| 20,000 | **23** |

So `c` grows at roughly **+5 per decade of `V`** — **logarithmically**, against the dyadic route's
**linear** growth. Not bounded, so **no uniform bound and no proof**; but exponentially better than
the route recorded as closed.

## 4. What this changes, stated exactly

**It does not settle Existence.** A logarithmically growing denominator is still unbounded, and
`ExistenceAt8` quantifies over difference sets of unbounded size. No route here closes it.

**It does reopen a question the record had closed.** `DYADIC_DEPTH_RESULT_v1` §2 concluded *"the
reduction survives only as a `V`-dependent statement"* — true of powers of two, and the general
denominator behaves qualitatively differently. The closure was of that restriction, not of the idea.

**The target it leaves.** If `c ≤ C` held for an absolute `C`, the condition would depend on each `a`
only through `a mod 8·lcm(1..C)` and `ExistenceAt8` over whole numbers would become a finite check.
The data says `C` does not exist but grows only like `log V`; a proved bound of the form
`c ≤ C·log(max ds)` would be a genuine theorem and is the first target here that the measurements
support rather than refute.

---

## 5. "An isolation, not the first" — why the distinction earns its keep

The target is `∃ s, 0 < s ∧ Lonely 8 ds s`: **an** isolation. Two things follow, and the second is
the useful one.

**The cascade happens to find the first.** `Iteration.first_isolation_of_fixed` proves the fixed point
is lonely *and* at or before every positive lonely time. Checked: cascade arrival equals the least
lonely opening in **3,000 of 3,000** sets. That is a property of the cascade, not a demand on us —
and describing it as what we are aiming at makes the target sound stricter than it is.

**Naming a later isolation is far easier than reaching the first.** Of the 1,580 sampled sets that
`lonely_at_inv_of_not_dvd` covers:

| | |
|---|---|
| `t = 1/8` is the **first** isolation | **158** |
| `t = 1/8` is a **later** isolation | **1,422** |

**The proved theorem names an instant that is not the first in 90% of the sets it settles.** Had the
target been "the first isolation", that theorem would settle almost nothing. The freedom to name a
late, arithmetically convenient instant is exactly what makes an exhibition possible — and it is what
the cascade, which must walk to the first, does not have.

This is the sharpest argument for attacking Existence by *naming* rather than by *terminating*: the
namer may choose its instant, the cascade may not.
