# The cascade as a rule — plan (v2)

2026-09-14. Supersedes v1, which carried three imports: a loop over the enlarged step
`k = 2, 3, …`; the question "how far does `k` have to go"; and ordering the proof cases by how many
runners they reach. None is the framework's. Nothing here touches the frozen manuscript or the
Lean trees.

**Goal.** A rule that takes the eight speeds and, for each runner, gives the time at which it is
lonely — and a proof that the rule works for every arrangement.

---

## 1. The rule, in the framework's objects

For one runner, real speeds, nothing rounded:

1. **`d_min`** — its nearest speed difference, from its two speed-neighbours. **`d_max`** — its
   largest.
2. **Readings** — every other runner read proportionately, `s = e/d_min`.
3. **AP times at scale 1** — `u = d_min·t` on the spine points `k + r/8`, `r ∈ {1,3,5,7}`, on every
   lap `k`. The time is `t = u/d_min`, irrational whenever `d_min` is.
4. **The cascade** — when the arrangement does not work to AP times at scale 1, the cascade gives
   the appropriate AP scale, and the time is read at that scale.
5. **Clearing** — every other runner at distance at least `1/8`, inclusive.

**Not yet written down anywhere, and the owner's to state:** how the cascade determines the
appropriate AP scale from `d_min` and `d_max` (and, for commensurate arrangements, the AP at the
gcd). `SKETCH_v7` §7c names the tiers (AP at the gcd, grid at `d_min`, enlarged) and the
dead-step closed form, but not how the enlarged scale is given.

## 2. What is already proved toward it

| case | time | status |
|---|---|---|
| `d_max ≤ 7·d_min` | `u = 1/8` | Theorem 4.8, Lean, over the reals |
| no reading within 1 of a multiple of 8 | `u = 1/8` | band identity, Lean, over the reals |
| some `r` clears every reading | `u = r/8` | spine row, Lean, over the reals |
| instances: `(1,2,π,4,…,8)`; `(1,1+√2/100,3,…,8)` | named per runner | Lean, `experiments/n8/Irrational*_v1.lean` |

And one fact that says exactly when scale 1 cannot work for a runner with integral readings, by
arithmetic rather than by trying laps:

> An integral reading `s` is in the way at **every** AP time of scale 1 (`u = a/8`, `a` odd, any
> lap) exactly when `8 | s`. Odd `s`, and `s ≡ 2, 4, 6 (mod 8)`, are never in the way there.

So for such a runner, scale 1 works on some lap unless a reading is a multiple of 8 — and when one
is, no lap at scale 1 helps and the cascade must change the scale. Non-integral readings are not
all-or-nothing and need their own statement.

## 3. Steps

1. **The owner states §1 item 4** — how the scale is given.
2. **Write the rule as a definition**, in the owner's terms, and in Lean over the reals.
3. **Prove it case by case.** A case is proved when every arrangement in it has its time given by
   the rule and shown to clear, in Lean.
4. **Done** when the cases cover every arrangement: one Lean theorem — for every eight distinct
   real speeds and every runner, that runner is lonely at the time the rule gives.
