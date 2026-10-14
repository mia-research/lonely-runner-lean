# The `−7` Opening Intersected With the Blocker Count

*Version 1, 2026-09-20. Answers a direct question: is the parameter space where the largest flank
is shadowed AND at most five movers do the blocking already empty? It is not. But running the
intersection produced a floor, and the floor is not a counting fact.*

Scripts: `scratchpad/mseven_x_blockers.py`, `mseven_x2.py`, `mseven_x3.py`, `four_witness.py`.
All arithmetic is exact integer arithmetic. No sampling in the exhaustive rows.

---

## 1. The setting, in the framework's own objects

The subject has seven positive integer differences; the largest is the flank `e`; the other six are
the **movers**. Openings of flank `e` are indexed `k = 0 … e−1` (period `e`, Theorem 6.13). Mover
`d` is in the way at opening `k` exactly when

```
min( r , 8e − r ) < e ,        r = d·(8k+1)  mod  8e
```

which is `MinusSeven_v1.inWay d (8k+1) e`. The flank is **shadowed** when every `k` is blocked.

The `−7` opening is `A = 8L − 7 = 8(L−1) + 1`, index `k = L − 1`
(`minus_seven_is_opening`).

---

## 2. The `−7` half is exactly a tiny-difference condition, and it is tight

`MinusSeven_v1.flank_clear_of_no_tiny` `[PROVED]`: with `|d| ≤ e` and `e ∣ L·d` for every mover,
the `−7` opening is clear unless some mover is **tiny**, `7·|d| < e`.

Measured from the other side, over every shadowed largest flank:

| population | shadowed flanks | `min e/d_min` |
|---|---|---|
| exhaustive, `e = 2 … 26`, all 6-subsets of `[1,e]`, `gcd = 1` | 1,714 | **7.3333** |
| exhaustive, `e = 2 … 30` | 3,056 | 7.25 |

Never `≤ 7`, and the observed minimum sits just above it. **Shadowing the largest flank requires a
tiny mover**, and the threshold is exactly the theorem's. No slack either way.

---

## 3. The intersection at five blockers is NOT empty

| population | shadowed | need exactly 5 | need 6 | need ≤ 4 |
|---|---|---|---|---|
| exhaustive `e = 2 … 26` | 1,714 | 655 | 1,059 | **0** |
| exhaustive `e = 2 … 30` | 3,056 | 1,127 | 1,929 | **0** |
| random `e = 27 … 160`, 4,000,000 draws | 138 | 50 | 88 | **0** |

Smallest witness needing exactly five: `e = 8`, movers `(1, 3, 4, 5, 7)`. Others at
`e = 10, 12, 14` with `(1,2,3,5,7)` and `(1,3,4,5,7)`.

So a Lean script asked to show the five-blocker intersection empty would not close — it would find
these. **The question's premise is answered negatively, and the witness is small enough to check by
hand.**

---

## 4. What the run did produce: the floor is five

**No configuration of four movers shadows a flank.**

| check | configurations | failures |
|---|---|---|
| all 4-subsets of `[1,e]`, `e = 2 … 22` | 33,649 | **0** |
| every shadowed case found (§3) | 1,852 | **0** |

Survivors per 4-mover configuration: minimum **1**, mean 6.77. Four movers always leave at least
one opening clear.

`[EMPIRICAL — exhaustive at e ≤ 22 for the 4-mover statement; exhaustive at e ≤ 30 and sampled to
e = 160 for the shadowed population. Not proved.]`

---

## 5. The floor is not a counting fact

This is the part that matters for how it would be proved.

**Naive count.** Maximum coverage by a single mover is exactly `e/2`, attained at `d = e/2`, at
every `e` tested (`e ≤ 200`). A count of the form "each mover covers at most a fraction `f`, so at
least `⌈1/f⌉` movers are needed" therefore forbids **one** mover and nothing more.

**Refined count**, using the actual four largest coverages at each `e` rather than a uniform bound:

| `e` | four largest coverages | sum | sum / `e` |
|---|---|---|---|
| 8 | 4, 2, 2, 2 | 10 | 1.25 |
| 12 | 6, 4, 4, 4 | 18 | 1.50 |
| 32 | 16, 8, 8, 8 | 40 | 1.25 |
| 100 | 50, 40, 30, 30 | 150 | 1.50 |
| 128 | 64, 32, 32, 32 | 160 | 1.25 |

Every ratio is `≥ 1`. The four largest blocked sets carry between 1.25`e` and 1.5`e` of mass —
comfortably enough to cover `e` openings if they could be arranged disjointly. **They cannot.** What
stops four movers is the forced **overlap** of their blocked sets, not their total size.

`shadow_needs_count` (`CoverCount_v1`) is the counting statement, and this measurement says it
cannot reach the floor on its own.

---

## 6. The Lean target this changes

Not "the five-blocker intersection is empty" — §3 refutes that.

> **`four_movers_cannot_shadow`.** For a flank `e > 0` and any four movers `d₁ … d₄`, some opening
> index `k < e` has no mover in the way.

Two facts about the shape of that proof, both measured:

- **There is no uniform witness.** The surviving index depends on the configuration. In particular
  `k = e − 1`, the `−7` opening, is **not** always the survivor: at `e = 8` the movers `(1,2,3,4)`
  cover it, as do `(1,2,3,5)`, `(1,2,3,6)` and `(1,2,3,7)`. So the proof cannot supply one index and
  discharge the rest by `decide`.
- **Counting will not do it** (§5). An overlap argument is required — which pairs of movers are
  forced to block the same openings.

The per-`e` statement is decidable, so each fixed `e` closes by `decide`; the statement over all `e`
is the unbounded enumeration, the same shape as the census gap.

**Adjacent, and checked not to be the same statement**: `CardFour_v1.exists_lonely_of_card_le_four`
`[PROVED, over ℝ]` says a subject with at most four *differences in total* is lonely. Here the
subject has seven differences and we are counting how many of the six movers are needed to shadow
one flank. Neither implies the other: a five-difference subject is outside `CardFour`'s hypothesis
and inside this one's.

---

## 7. What was asked and what the answer is

> *Given that the largest flank is clear at the `−7` opening unless a tiny difference forces the
> spread, is the intersection of the `−7` opening requirements with the five-blocker maximum already
> empty?*

**No.** 705 configurations shadow the largest flank with exactly five movers, the smallest at
`e = 8`. The `−7` requirement is confirmed and tight — shadowing forces `e/d_min > 7`, minimum
observed 7.3333 — but it does not conflict with five blockers.

**At four it is empty**, in every configuration checked, and that emptiness is structural rather
than arithmetic.
