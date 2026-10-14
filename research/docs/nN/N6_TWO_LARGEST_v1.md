# Order 6: the rank-two flank door

2026-09-21, version 1. Companion to `SMALL_ORDER_DOORS_v3.md` §6, which did the same for `n = 5`.

Artefacts: `LonelyRunner/LRC/Spec/DoorsN.lean` (`DoorTwoLargest` and the ladder, axiom-clean) ·
`experiments/n8/n6_ladder_check_v1.out` · `experiments/nN/n6_twolargest_v1.{py,out}` ·
`n6_twolargest_60.out` · `n6_rank2_family_v1.{py,out}` · `n6_structure_v1.{py,out}` ·
`collapsed_sets_v1.{py,out}`

**Grade of the headline: `[EMPIRICAL]`, not `[PROVED]`.** No Lean proof exists at `n = 5` or
`n = 6`. What exists is exhaustive evidence over bounded ranges plus a bounded tight family.

---

## 1. Why `n = 6` needs a different door from `n = 5`

`DoorLargestFlank` — the **largest** disparity hosts a lonely opening — is the `n = 5` candidate
(172,352,957 sets, no counterexample). At `n = 6` it is **false**: 72 primitive 5-subsets of
[1,80] have no lonely opening at their largest disparity, the smallest being `(1,2,3,5,6)`.

The exhaustive flank-rank sweep put the worst rank at **2** for `n = 6` (and 3 for `n = 8`), so
the `n = 6` candidate is the rank-two form.

---

## 2. The statement, in Lean  `[PROVED — the ladder, not the candidate]`

Added to `LRC/Spec/DoorsN.lean`, generic in `n`, axiom-clean
(`[propext, Classical.choice, Quot.sound]`, `n6_ladder_check_v1.out`):

```lean
def DoorTwoLargest (v : Fin n → ℝ) (k : Fin n) : Prop :=
  ∃ i : Fin n, i ≠ k ∧
    ((diffSet v k).filter (fun d => |v i - v k| < d)).card ≤ 1 ∧
    ∃ j : ℕ, LonelyAt v k (flankOpening n |v i - v k| j)
```

with the full ladder proved:

```
DoorLargestFlank  →  DoorTwoLargest  →  DoorThreeLargest  →  LonelyForSubject  →  LonelyRunnerAtN n
 doorTwoLargest_of_doorLargestFlank
        doorThreeLargest_of_doorTwoLargest
                 lonelyForSubject_of_threeLargest
                                       lonelyRunnerAtN_of_doorTwoLargest
```

So a result at any rung transfers down, and **`DoorTwoLargest` at `n = 6` closes order 6** —
no `intLRC` import, no dependence on the `sorry`'d real-speeds reduction, and no iteration, so
it sidesteps the termination diagonal entirely.

The `Prop` is order-independent; the **rank** in it is not. That is the general lesson from
`SMALL_ORDER_DOORS_v3.md` §1 showing up again.

---

## 3. The evidence  `[EMPIRICAL — exhaustive, integer sets]`

Integer form (equal to the `Fraction` form; validated against the recorded `n = 8` refutation
`(2,3,5,7,8,13,16)`, which reproduces: flank 16 fails, flank 13 works at lap 1, best rank 2):

```
flank e hosts a lonely opening  ⟺  ∃ j ∈ [0,e) : ∀ d ∈ ds,  d·(6j+1) mod 6e ∈ [e, 5e]
```

Exhaustive over primitive 5-subsets:

| range | sets | worst rank | largest alone fails | **two largest both fail** |
|---|---|---|---|---|
| [1,40] | 641,166 | 2 | 67 | **0** |
| [1,60] | 5,302,911 | 2 | 71 | **0** |
| [1,80] | 23,312,716 | 2 | 72 | **0** |

**23,312,716 sets, zero counterexamples to `DoorTwoLargest`.**

### 3.1 The tight family is bounded — the proof-shaped part

Counting working openings across the two largest flanks (`n6_structure_v1.out`):

| range | tight (≤1 opening) | with **zero** openings | max element among tight |
|---|---|---|---|
| [1,40] | 26 | 0 | 30 |
| [1,60] | 26 | 0 | 30 |
| [1,80] | **26** | **0** | **30** |

Stable at **26 sets, all with `d_max ≤ 30`**, across a 36-fold growth in the population.
Everything with `d_max > 30` has **two or more** working openings among its two largest flanks.

That is the same shape as `n = 5` (57 tight sets, all `d_max ≤ 15`): a finite check below the
bound, and a margin argument above it.

### 3.2 The rank-2 family

The sets where the largest flank *fails* (so the second is needed) number 67 → 71 → 72 across
the three ranges — nearly stable, though the largest member tracks the range boundary
(40 → 52 → 64), so it is **not established as finite**.

A conjectured infinite family `(3, 3m, 3m+3, 3m+6, b)` was tested and **refuted as a pattern**:
only 7 members for `m = 2..59`, the largest at `m = 15` (`(3,45,48,51,64)`). So the rank-2
family shows no sign of being unbounded, but that is an absence of evidence, not a bound.

This matters for proof *shape* but not for the candidate: what a proof needs bounded is the
**tight** family (§3.1), and that is bounded.

### 3.3 Collapsed difference sets

A subject can present fewer than `n − 1` disparities when two runners sit symmetrically about
it. Those were outside the full-card sweeps, and are checked separately (`collapsed_sets_v1.out`):

| order | card 1 | card 2 | card 3 | card 4 |
|---|---|---|---|---|
| 5 (claim rank ≤ 1) | rank 1 | rank 1 | rank 1 | — |
| 6 (claim rank ≤ 2) | rank 1 | rank 1 | rank 1 | **rank 1** |

Every collapsed case is settled at **rank 1**, more easily than the full-card case. At `n = 6`
only full card-5 sets ever need rank 2. The scope gap flagged in `SMALL_ORDER_DOORS_v3.md` §8
is closed for both orders.

---

## 4. Status of the two orders, side by side

| | `n = 5` | `n = 6` |
|---|---|---|
| candidate | `DoorLargestFlank` (rank 1) | `DoorTwoLargest` (rank 2) |
| rank 1 status | no counterexample | **false** (72 sets) |
| exhaustive evidence | 172,352,957 sets to [1,260] | 23,312,716 sets to [1,80] |
| counterexamples | 0 | 0 |
| tight family | 57 sets, all `d_max ≤ 15` | 26 sets, all `d_max ≤ 30` |
| tight family stable over | [1,60] → [1,200] | [1,40] → [1,80] |
| collapsed cards | rank 1 throughout | rank 1 throughout |
| Lean `Prop` + ladder to the target | yes, axiom-clean | yes, axiom-clean |
| **proof** | **none** | **none** |

---

## 5. Grades

| claim | grade |
|---|---|
| `DoorTwoLargest` and the four-rung ladder, generic in `n` | `[PROVED — axiom-clean, n6_ladder_check_v1.out]` |
| `DoorLargestFlank` is false at `n = 6` | `[VERIFIED — 72 exhaustive witnesses, smallest `(1,2,3,5,6)`]` |
| `DoorTwoLargest` at `n = 6`: no counterexample | `[EMPIRICAL — 23,312,716 exhaustive primitive 5-subsets of [1,80]; integer sets only; NOT a proof]` |
| the `n = 6` tight family is 26 sets, all `d_max ≤ 30` | `[VERIFIED — exhaustive, stable [1,40]→[1,80]]` |
| collapsed cards settle at rank 1 at `n = 5, 6` | `[VERIFIED — exhaustive]` |
| the `(3,3m,3m+3,3m+6,b)` family is infinite | `[REFUTED — 7 members only, m = 2..59]` |
| the rank-2 family is finite | **undetermined** — count nearly stable, max element still tracking the range |

**Scope of the negatives.** "No counterexample at `n = 6`" is bounded to integer (hence
rational) difference sets, card 5, exhaustive to `d_max ≤ 80`, with the opening search complete
by periodicity (`j ↦ j+e` adds the integer `d`). It does not cover irrational ratios; the
framework's `Flanks.lonely_opening_of_free_off_lattice` and `off_lattice_of_irrational_ratio`
(hypothesis `4 ≤ n`) apply at `n = 6` and are the intended route, not yet assembled.

---

## 6. Next

1. **Prove `DoorTwoLargest` at `n = 6`**: finite check on `d_max ≤ 30`, margin argument above.
   Same two-part shape as the `n = 5` target, and neither is done.
2. **Decide `n = 7`** the same way: measure the worst flank rank exhaustively (the earlier
   sweep says 2 over [1,23]) and test whether its tight family is bounded.
3. Either proof would be the first order closed inside the framework since `n = 4`.
