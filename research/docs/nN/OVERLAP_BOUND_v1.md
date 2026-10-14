# The overlap bound: the reduction, and three routes measured shut

2026-09-21, version 1. Attempt at the statement left open in `N5_LEAN_STATUS_v1.md` §4 —
that the union of the blocked sets stays below `e`.

Artefacts: `LonelyRunner/LRC/Spec/FlankFiniteN.lean` (15 declarations, all axiom-clean, no
`sorry`) · `experiments/n8/flankfinite_axioms_v1.out` · `experiments/nN/band_coverage_v1.{py,out}` ·
`regions_v1.{py,out}` · `blocking_capacity_v1.out` · `union_slack_v1.out`

**The overlap bound is NOT proved.** What follows is a proved reduction, a proved region, and
three routes ruled out by measurement rather than by opinion.

---

## 1. The reduction  `[PROVED]`

The openings of a flank `e` are `(j + 1/n)/e`, **equally spaced with gap `1/e`**. So a window
longer than `1/e` must contain one:

```lean
theorem exists_flankOpening_mem_Ioo {e : ℝ} (he : 0 < e) {x L : ℝ} (hx : 0 ≤ x)
    (hL : 1 / e < L) : ∃ j : ℕ, flankOpening n e j ∈ Set.Ioo x (x + L)

theorem exists_lonely_flankOpening_of_gap {ds : Finset ℝ} {e : ℝ} (he : 0 < e)
    {x L : ℝ} (hx : 0 ≤ x) (hL : 1 / e < L)
    (hwin : ∀ t ∈ Set.Ioo x (x + L), Lonely n ds t) :
    ∃ j : ℕ, Lonely n ds (flankOpening n e j)
```

Both axiom-clean, at every order `n ≥ 2` and any number of blockers.

**Why this is the right shape.** It replaces

> *the union of the blocked sets misses one of the `e` openings* — a statement about the openings

by

> *the lonely set of the blockers contains an interval longer than `1/e`* — a statement about the
> blockers alone, with the flank entering only through the number `1/e`.

That is what makes it useful for generalisation: nothing in it mentions four disparities or
order five.

---

## 2. The region already proved  `[PROVED]`

`clear_at_last_opening` / `lonely_last_of_ratio` settle every set inside the ratio condition
`d_max ≤ (n−1)·d_min`. Measured coverage at `n = 5`: **42.7%** of primitive 4-subsets of
`[1,60]` (194,238 of 455,041).

---

## 3. Three routes, measured shut

### 3.1 Counting / pigeonhole — **dead**

If the blocked counts summed to less than `e`, a survivor would follow with no arithmetic.
They do not. Blocking capacity (sum of blocked counts, over `e`) reaches **1.50** at `n = 5`
and exceeds 1 for **1,472,573 of 1,473,833** sets (`blocking_capacity_v1.out`). The blocked
sets must overlap heavily, and no counting argument can see that.

### 3.2 A finite cover by named band instances — **dead**

`Flanks.clear_at_opening_of_band` settles a set whenever every disparity lies in a band at one
opening `k`. Coverage by the smallest `k` that suffices, `n = 5`, exhaustive over `[1,60]`
(`band_coverage_v1.out`):

| settled by | sets | share |
|---|---|---|
| `k = e−1` (the ratio condition) | 194,238 | 42.69% |
| `k = 1` | 58,899 | 12.94% |
| `k ≤ 3` | 184,021 | 40.44% |
| `k ≤ 10` | 382,235 | 84.00% |
| `k ≤ 30` | 454,405 | **99.86%** |
| any `k < e` | 455,041 | 100% |

**The required `k` is unbounded.** `k ≤ 30` still misses 636 sets. This reproduces at `n = 5`
what the manuscript already records at `n = 8` (`experiments/n8/bounded_k_attack_v1` reaching
`k = 369`). So no finite list of named openings will close `FourClears`.

### 3.3 LRC slack through the gap criterion — **reaches 0.03%**

`intLRC_four` is axiom-clean in this tree, so for three integer blockers there is a `t` with
`‖d_i t‖ ≥ 1/4`. Staying above `1/5` then holds on a window of length
`2(1/4 − 1/5)/d_max = 1/(10 d_max)`, and §1 applies exactly when `e > 10·d_max`.

That is a genuine theorem, and it is nearly empty: **150 of 455,041 sets (0.03%)** at `[1,60]`,
disjoint from the ratio condition. Not formalised, because the region does not earn a
declaration.

The obstruction is that `1/4` is the best available floor for three speeds and it is tight
(speeds 1, 2, 3), so the slack over `1/5` is only `1/20` however the argument is arranged.

---

## 4. What is left, and what is now known about it

**Still owed: 57.3%** of the space — every set with some blocker below `e/4` and none of the
special structure above. The smallest examples are `(1,2,3,5)`, `(1,2,3,6)`, `(1,2,3,7)`.

Known constraints on any proof:

- it must be an **overlap** argument, not a counting one (§3.1);
- it cannot be a finite cover by named openings (§3.2);
- it cannot come from the LRC floor for three speeds (§3.3);
- the quantity to bound is `union/e`, which at `n = 5` never exceeds **31/33**, attained at
  `(5,15,20,33)` and unchanged from `[1,40]` to `[1,80]` across 1.47M sets, while `n = 6, 7, 8`
  all reach exactly 1 (`union_slack_v1.out`);
- the slack grows with `e` — minimum survivors rise like `e/10`, so the hard cases are small
  `e`, and those below 15 are already discharged by `four_clears_small`.

Given §1, the statement to prove is now: **the lonely set of at most three blockers contains an
interval longer than `1/e`, once `e > 15`.** That is a three-distance / continued-fraction
question about `‖d_i t‖`, with no flank and no openings in it.

---

## 5. Grades

| claim | grade |
|---|---|
| the 15 declarations of `FlankFiniteN.lean` | `[PROVED — flankfinite_axioms_v1.out, 15/15 axiom-clean, no `sorry`]` |
| the gap criterion, every `n`, any number of blockers | `[PROVED — exists_lonely_flankOpening_of_gap]` |
| ratio-condition region, 42.7% at `n = 5` | `[PROVED — clear_at_last_opening]` |
| counting cannot prove it | `[VERIFIED — capacity ≥ 1 for 1,472,573 of 1,473,833 sets]` |
| a finite named-band cover cannot prove it | `[VERIFIED — `k ≤ 30` misses 636 of 455,041; `n = 8` record reaches `k = 369`]` |
| the LRC-slack region is `e > 10 d_max` | `[PROVED as a statement; 0.03% coverage — not formalised]` |
| **the overlap bound** | **NOT PROVED** |
| `FourClears n` | **NOT PROVED** |

**Scope.** Coverage percentages are over primitive 4-subsets of `[1,60]` at `n = 5`, hence by
`lonely_flank_smul_iff` over all rational difference sets of that shape; they are not claims
about the unbounded range. The three "dead route" findings bound what those routes achieve on
the measured ranges, and §3.2's unboundedness is corroborated by the independent `n = 8` record.
