# Why the census does not close Existence

Scripts: `experiments/n8/census_mismatch_v1.py`, `residual_257_v1.py`, `residual_by_s_v1.py`,
`residual_17_v1.py`.

---

## 1. Two errors of mine, corrected first

I reported a residual of **257** census families, then **17**. **Both were artefacts.**

A cover with `s = 6` pins six ratios; with `M` that is seven differences and there is **no free
parameter** — the batch machine's own verdict for those rows is
`SETTLED-all-x (no free param)`. I applied killer analysis to all 6,964 rows, including the 6,759
that have no `x` to kill, and manufactured a residual out of it.

The tell was in my own output: the "rescue" check printed difference sets of **eight** elements
(`[1,2,5,6,7,8,11,13]`) for a subject that has seven. I should have stopped there rather than
reporting 17.

## 2. The census is fully settled on its domain

| rows | verdict |
|---|---|
| **6,759** — `s = 6`, fully pinned | `SETTLED-all-x (no free param)` |
| **197** — `s = 5`, a pinned flank is always free | `SETTLED-all-x` |
| **8** — `s = 5`, no `x` kills every pinned flank | `SETTLED-all-x` |
| **6,964** | **all SETTLED** |

Independently recomputed: of the 205 free-parameter rows, 8 have no always-free flank, and
**zero** of those admit an `x` killing every usable flank. **The residual is zero.**

Also resolved: the 1,944 cross-check mismatches between the export and the machine are **all**
killers whose free parameter lies outside `0 < x < M`. Zero genuine disagreements, so the
classification driving the Lean emission is sound.

## 3. So why is Existence not closed?

Because of the census **domain**, not its residual. From the batch machine's own header:

> *"The batch family-settlement machine (order 8, **census range `c ≤ 12`**)."*

The covers are minimal `A = 0` covers whose pinned ratios have denominator at most 12. Raising
the bound produces **new covers**, and it has not stopped:

| denominator bound | covers found | run state |
|---|---|---|
| `c ≤ 12` | 78 | heartbeats present |
| `c ≤ 14` | 114 | heartbeats present |
| `c ≤ 15` | 212 | heartbeats present |
| `c ≤ 16` | 31 and counting | heartbeats present |

Every listed run carries heartbeat lines, so each is **incomplete**. The count grows with `c` and
**no bound on `c` is proved anywhere.**

## 4. The one thing that would close the census route

> **`[OPEN]`** Prove a bound `C` such that no minimal `A = 0` cover with denominator `> C` yields
> an unsettled family — a finiteness theorem for the census.

With that bound the census becomes a finite computation, and every row of it is already settled by
the machinery in `Cascade/`. Without it, enumerating further denominators produces more covers
indefinitely and the route cannot terminate.

That is why the census does not close Existence: **not a residual of hard families, but an
unbounded enumeration.**

Existence at order 8 remains open.
