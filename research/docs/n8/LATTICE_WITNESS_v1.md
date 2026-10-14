# The lattice witness — a constructive frame for the open case

2026-09-13. n = 8, individual isolation, threshold 1/8.

Written after the observation that the earlier proof attempts were reaching for covering and
measure arguments — the old machinery — when the frame built in this session is constructive.

---

## 1. The reframing

Normalise: `m = d_min`, `u = m·t`, `s_j = d_j/m`, so `s_1 = 1` and the target is
`u ∈ [1/8, 7/8]` with `‖s_j u‖ ≥ 1/8` for all `j`.

Old question: *do the bad sets fail to cover the interval?* — measure. **Dead**: the AP's good set
there is four isolated points, measure zero, so no measure bound of any strength can work.

New question: *on which lattice does the witness live?* — construction. Search
`u = p/(8L)` for `L = 1, 2, 3, …` and take the first that works.

## 2. `L = 1` is the spine, and it is exactly the unblocked case  `[PROVED]`

`L = 1` means `u = p/8`. For integer `s`, `‖s·p/8‖ ≥ 1/8` unless `s ≡ 0 mod 8`. So

> **`L = 1` works ⟺ no `s ≡ 0 mod 8` ⟺ the runner is unblocked.**

Confirmed: over 9,725 unblocked instances, `L = 1` in every one.

A single `s ≡ 0 mod 8` kills the **whole** spine at once — `‖s·p/8‖ = 0` for every `p`, not just
some. So the spine is never partially damaged.

## 3. But that same blocker is harmless one lattice down

If `s = 8σ`, then at `u = p/16` with `p` odd, `‖s u‖ = ‖σp/2‖ = 1/2` whenever `σp` is odd — the
constraint goes from maximally blocking to maximally clear. That is the constructive lever the
measure view cannot see.

Measured over 9,226 blocked instances:

| first lattice that works | count | cumulative |
|---|---|---|
| `p/16` | 7,389 | **0.801** |
| `p/24` | 1,404 | 0.953 |
| `p/32` | 310 | 0.987 |
| `p/40` | 122 | 0.9999 |
| `p/48` | 1 | 1.000 |

**80% of blocked runners are resolved by the very next lattice.**

## 4. Two candidates, both refuted  `[REFUTED]`

| candidate | killed by |
|---|---|
| `L ≤ 6` | `L = 7` at `(19,23,51,147,209,211,300,302)`, r6 |
| `L ≤ 7` | `L = 9` by hill-climbing, at `(134,206,222,301,302,353,366,524)`, r5 |

The `L = 9` case has `s = (168, 96, 80, 1, 51, 64, 222)` — **four** of those are `≡ 0 mod 8`. Many
blockers, not one.

Recorded because both candidates looked solid on thousands of random instances and fell within
minutes of an adversarial search. Random sampling was not probing this at all.

## 5. What correlates with `L`

| blockers | cases | mean `L` | max `L` |
|---|---|---|---|
| 0 | 9,725 | **1.00** | **1** |
| 1 | 5,961 | 1.46 | 7 |
| 2 | 3,220 | 1.63 | 7 |
| 3 | 935 | 1.75 | 7 |
| 4 | 149 | 1.95 | 6 |
| 5 | 10 | 2.30 | 4 |

The **mean** rises with the blocker count; the **max** does not. So the count alone does not
govern `L`.

## 6. The open question, restated

Not "do the bad sets cover the interval" (measure — dead), and not "does the iteration terminate"
(vague). It is:

> **Is `L` bounded, and by what?**

with the ceiling that at most 7 of a runner's differences can be blockers. `L = 1` is settled and
constructive. Everything unproved now sits in one integer.

## 7. Status

`[PROVED]` §2 — `L = 1` ⟺ unblocked, with the witness exhibited.
`[VERIFIED — 9,226]` §3's lattice distribution.
`[REFUTED]` §4's two candidates.
`[OPEN]` a bound on `L`.

**n = 8 is not proved here.**
