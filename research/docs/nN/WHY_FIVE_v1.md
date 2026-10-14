# Why the largest-flank door holds at five and fails at six

2026-09-21, version 1. Answers the owner's question on `SMALL_ORDER_DOORS_v3.md` §6 /
`N6_TWO_LARGEST_v1.md`: *why 5 but not 6?*

Artefacts: `experiments/nN/blocking_capacity_v1.{py,out}` · `blockers_grid_v1.{py,out}` ·
`three_blockers_v1.{py,out}` · `clearance_law_v1.{py,out}` ·
`LonelyRunner/LRC/Spec/FlankFiniteN.lean` · `experiments/n8/flankfinite_axioms_v1.out`

---

## 1. The answer

**It is not about the order. It is about the number of blockers, and `n = 5` is the last order
that stays inside the clearance threshold — by exactly one.**

At a flank opening of `e` the disparity `e` itself sits at exactly `1/n`, so it is never
blocked. A difference set of card `m` therefore has `m − 1` **blockers**. A subject at order `n`
has `n − 1` disparities, hence exactly **`n − 2` blockers**.

Measured clearance threshold `f(k)` — the least order at which `k` blockers never fail
(`clearance_law_v1.out`):

| blockers `k` | 3 | 4 | 5 | 6 |
|---|---|---|---|---|
| `f(k)` | **5** | 8 | 11 | 13 |

Rank one holds at order `n` exactly when `n ≥ f(n − 2)`:

| `n` | blockers `n−2` | needs `n ≥` | holds |
|---|---|---|---|
| **5** | 3 | **5** | **yes, with nothing to spare** |
| 6 | 4 | 8 | no |
| 7 | 5 | 11 | no |
| 8 | 6 | 13 | no |

`f` grows like `2k − 1` (5, 8, 11, 13); the diagonal can afford only `k + 2`. The two agree at
exactly `k = 3`, since `2·3 − 1 = 5 = 3 + 2`, and diverge immediately after. `n = 5` is the
crossover point, not a special case.

---

## 2. Two competing effects, separated

The grid (`blockers_grid_v1.out`) — failures of the largest flank, exhaustive, by order and card:

| order \ card | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|
| 5 | . | . | . | – | – | – | – |
| 6 | . | . | . | **52** | – | – | – |
| 7 | . | . | . | 4 | **119** | – | – |
| 8 | . | . | . | . | 34 | **179** | – |
| 9 | . | . | . | . | 7 | 57 | **71** |

(`.` = no failures; bold = the diagonal, i.e. what that order's subjects actually present.)

- **Down a column**: raising `n` helps, because the threshold `1/n` shrinks. Card 5 fails at
  `n = 6` (52) and `n = 7` (4), and is clean from `n = 8` up.
- **Across a row**: adding a blocker hurts.
- **Along the diagonal**: blockers grow in lockstep with `n`, and the blocker effect wins from
  `n = 6` onward.

**Three blockers never failed at any order tested — `n = 5` through `n = 50`**, over 62,782
exhaustive sets per order plus 369,656 random card-4 sets from `[1,4000]`
(`three_blockers_v1.out`).

---

## 3. It is not a counting argument

The obvious mechanism — that the blocked sets are too small to cover — is **false**. Blocking
capacity is the sum of blocked openings over the non-flank disparities, divided by `e`; below 1
it would force a survivor by pigeonhole (`blocking_capacity_v1.out`):

| order | max capacity | sets with capacity ≥ 1 | failures |
|---|---|---|---|
| 5 [1,80] | 1.50000 | 1,472,573 of 1,473,833 | 0 |
| 6 [1,34] | 1.80000 | all | 62 |
| 8 [1,18] | 2.11111 | all | 414 |

Capacity reaches 1.5 at `n = 5` and exceeds 1 for essentially every set, so **pigeonhole fails
everywhere** and the blocked sets must overlap heavily.

Some overlap is structural: at `j = 0` the reading for `d` is `d/(n e)`, which is below `1/n`
whenever `d < e`, so **every** non-flank disparity blocks the opening `j = 0`. What the numbers
above say is that with three blockers the overlap is always enough, and with four it need not be.

---

## 4. What this changes about the target  `[PROVED — the reduction; the candidate is not]`

The statement to aim at is **not** about `n = 5`. In `LRC/Spec/FlankFiniteN.lean`:

```lean
def FourClears (n : ℕ) : Prop :=
  ∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) → ds.card ≤ 4 → ∀ e ∈ ds, (∀ d ∈ ds, d ≤ e) →
    ∃ j : ℕ, Lonely n ds (flankOpening n e j)
```

uniform in `n`, with `n = 5` the case where `card ≤ 4` is automatic
(`LRC.SpecN.diffSet_card_le`). Proved, axiom-clean, no `sorry`:

| declaration | what it gives | axioms |
|---|---|---|
| `lonely_of_flankWorks` | the decidable integer predicate ⟹ a real lonely opening, via `clear_at_int_flank_iff_emod` | `[propext, Classical.choice, Quot.sound]` |
| `n5_finite_check` | all 1,806 primitive sets, card ≤ 4, `d_max ≤ 15`, by `decide` | **none** |
| `doorLargestFlank_of_fourClears` | `FourClears 5` ⟹ `DoorLargestFlank` at every five-runner subject | `[propext, Classical.choice, Quot.sound]` |
| `lonelyRunnerAtFive_of_fourClears` | `FourClears 5` ⟹ `LonelyRunnerAtN 5` | `[propext, Classical.choice, Quot.sound]` |

No `native_decide`, no `unsafe`, no `admit`. `FourClears` is **never assumed** — it appears only
as a hypothesis.

---

## 5. What is left

| piece | status |
|---|---|
| decidable predicate + bridge to the reals | **done** |
| finite check, integer sets, `d_max ≤ 15` | **done** (`decide`, axiom-free) |
| plumbing: a `Finset ℝ` of whole numbers ↔ the `List ℕ` form | not done — mechanical |
| **margin argument, integer sets, `d_max > 15`** | **not done — this is the mathematical gap** |
| rational sets ⟹ integer sets by scaling | not done; `Flanks.exists_lonely_of_smul` exists |
| irrational ratios | not done; `Flanks.lonely_opening_of_free_off_lattice` (`4 ≤ n`) is the route |

The margin argument is the whole of the remaining mathematics. What is known about it: the
tight family (exactly one working opening) at `n = 5` is **57 sets, all with `d_max ≤ 15`**,
stable from `[1,60]` to `[1,200]`, so above 15 there are always **two or more** working
openings. That is a statement about overlap, not about counting (§3), and no proof of it exists.

---

## 6. Grades

| claim | grade |
|---|---|
| the four Lean declarations of §4 | `[PROVED — flankfinite_axioms_v1.out]` |
| clearance law `f(3)=5, f(4)=8, f(5)=11, f(6)=13` | `[VERIFIED — exhaustive on the stated ranges; these are LOWER bounds, since a wider range can only add failures]` |
| three blockers never fail, `n = 5 … 50` | `[EMPIRICAL — 62,782 exhaustive sets per order + 369,656 random card-4 from [1,4000]]` |
| pigeonhole does not explain it | `[VERIFIED — capacity 1.5 at `n = 5`, ≥ 1 for 1,472,573 of 1,473,833 sets]` |
| every non-flank disparity blocks `j = 0` | `[PROVED — `d/(n e) < 1/n` whenever `d < e`]` |
| `FourClears n` for any `n` | **not proved** — the candidate |

**Scope.** All sweeps are over whole-number difference sets, hence by scale-invariance all
rational ones; irrational ratios are not covered by any sweep here. `f(k)` values are measured
on bounded ranges and are lower bounds on the true thresholds.
