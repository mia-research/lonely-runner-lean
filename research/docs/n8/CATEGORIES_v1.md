# The correct categories

The previous question was what is wrong with the proposed list. This is the constructive answer:
what the categories actually are, and how much of the problem each holds.

## The top-level object is the speed set, not the reading type

By the classical reduction every instance at order 8 is an **integer speed set**. So
"real / irrational" cannot be a sibling category — it reduces into the others, and listing it beside
them double-counts.

Within a speed set, the framework normalises by `d_min`, so `s₁ = 1` always. The question that
actually splits the problem is **how many readings `sᵢ = dᵢ/d_min` fail to be integers.** Call it `k`,
with `0 ≤ k ≤ 6`.

## The categories, with their weights

| `k` | category | status | share of instances (speeds `< 20000`) |
|---|---|---|---|
| 0 | integer readings — `d_min` divides every disparity | Branch A **`[PROVED]`**, all magnitudes and (now) all orders; Branch B **open** | **0.04%** |
| 1 | one non-integer ratio | **`[PROVED]`**, nearest-integer walk (Thm 6.9) | 0.00% |
| 2 | two non-integer ratios | **`[PROVED]`**, lattice crossing (Thm 6.18) | 0.02% |
| **3–6** | **three or more non-integer ratios** | **OPEN** | **99.95%** |

Measured over 120,000–200,000 random speed sets per range. The shares move with the range in one
direction only:

| speeds | `k = 0` | `k = 6` |
|---|---|---|
| `< 100` | 7.18% | 46.98% |
| `< 400` | 1.71% | 75.81% |
| `< 2000` | 0.35% | 92.11% |
| `< 20000` | 0.04% | **98.72%** |

`k = 0` falls like `7/N`. **`k = 6` — every ratio non-integer — tends to 100%.**

## What that says, stated carefully

Counting measure over a box is **not** difficulty, and Existence is universally quantified: `k = 0`
must be proved however rare it is. But the weighting does say where the unexplored mass sits, and it
says something worth absorbing:

> **The proved categories together hold about `0.06%` of instances at speeds under 20,000, and that
> share falls as the range grows. The apparatus is strongest exactly where instances are rarest.**

Nearly everything in this session — divisor-closed, Branch B, the reflection and its two centres, the
witness families, the blocker count — lives in `k = 0`. That work is not wasted: 25 of 56
declarations are order-free and hypothesis-free enough to apply anywhere (`THEOREM_TIERS_v1.md`
Tier 1). But the *categories* it settles are the sliver.

## The single most valuable target

**`k = 6`: all six readings non-integer.** It is 98.72% of instances at speeds under 20,000 and
rising, and it is not a special case of anything proved. Neither `TwoWalker` (which needs `k ≤ 2`)
nor Branch A (which needs `k = 0`) reaches it.

What is known about it from this session:

- it is exactly where **band 1** of `R` is occupied — every deep case on file has non-integer readings
  (`R16_IS_RATIONAL_v1.md`), so `R < 16` is a statement about this category and no other;
- it is exactly the **no-unit-speed** frontier, and the cost relative to `k = 0` is one theorem,
  `unit_never_blocks`, worth **5.76%** of candidates — the share where the minimum speed is the sole
  blocker;
- the **Tier 1** machinery applies to it unchanged, including the whole reduction to `ℤ`, both
  witness normalisations, and `SolutionPair`.

## Rows that should not appear

- **"General real / irrational"** — not a category; it reduces to integer speed sets.
- **"`R < 16`"** — not a category; it is a property of `k ≥ 1`, and is the same problem as the rational
  frontier.
- **"Finite middle band `8 ≤ bᵢ ≤ 27`"** — not a category; it was defined by a withdrawn threshold.
- **"`s₇·R ≤ 89`"** — not a bound; exceeded 410 times in 6,000 profiles, reaching 3001.
