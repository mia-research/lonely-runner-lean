# The machinery on arrangements, without ExistenceAt8

**Date:** 2026-09-18
**Module:** `LonelyRunner/LRC/Cascade/Arrangement.lean` (new), `LRC/Spec/Target.lean` (extended)
**Build:** `lake build LonelyRunner.LRC.Spec.Target` — 2548 jobs, clean. Zero `sorry`.
**Axioms:** every theorem below `[propext, Classical.choice, Quot.sound]`.

## 1. Why the rebuild

`ExistenceAt8` quantifies over `ds : Finset ℝ` with `card ≤ 7`. It is sufficient for the target and
was proved so (`lonelyRunnerAt8_of_existence`). It is **not the same statement**, and the difference
is not cosmetic:

- `Finset ℝ` forces decidable equality;
- it **collapses duplicate differences**, destroying the indexing;
- `card ≤ 7` admits sets no arrangement produces;
- it **discards the arrangement** — and gaps, the AP structure, the coupling across the eight
  subjects and "the subject and its two neighbours" are all arrangement-level.

Every mechanism supplied for this project lives at arrangement level. The machinery now lives there
too.

## 2. What is stated on the arrangement

| Object | Statement | Grade |
|---|---|---|
| `sep v k i t` | `v i * t − v k * t`. Both runners move; nothing sits at `0`. | `[PROVED]` def |
| `disp v k i` | `v i − v k`, the disparity with the subject; `sep = disp · t`. | `[PROVED]` |
| `disp_ne_zero` | injectivity ⇒ every disparity nonzero. | `[PROVED]` |
| `InWay`, `LonelyAt` | `< 1/8` and `≥ 1/8`: exact complements. | `[PROVED]` def |
| `lonelyAt_iff_no_inWay` | lonely ⟺ nobody in the way. | `[PROVED]` |
| `lonelyAt_iff_two_sided` | one condition per side of the subject. | `[PROVED]` |
| `lonelyAt_iff_neighbours` | `inf'`/`sup'` over the other seven: only the **two neighbours** bind. | `[PROVED]` |
| `inWay_comm` | `i` is in `k`'s way ⟺ `k` is in `i`'s. **No difference-set counterpart** — it relates two subjects. | `[PROVED]` |
| `lonelyAt_add_const` | adding a constant to every speed changes nothing: `v k = 0` is a convenience, never a hypothesis. | `[PROVED]` |
| `lonelyAt_const_mul` | rescaling the speeds rescales the reading. The scale is carried by the speeds; there is no free scale. | `[PROVED]` |

## 3. The bridge

`diffSet v k = image |v i − v k|` over `univ.erase k`, with

- `diffSet_pos` (injectivity), `diffSet_nonempty`,
- **`lonelyAt_iff_lonely_diffSet` : `LonelyAt v k t ↔ Lonely 8 (diffSet v k) t`.** `[PROVED]`

For a **fixed** subject, loneliness factors through that subject's own seven disparities, so the
1140 lines of `Flanks.lean` apply verbatim — with **no appeal to `ExistenceAt8`**. Duplicate
collapse is harmless here because the predicate is a `∀` over the set; what the set cannot carry is
everything *across* subjects, which is exactly what §2's last three rows are.

Lifted through the bridge:

- `exists_lonelyAt_iff_flank` — a subject is lonely somewhere ⟺ it is lonely at an opening of one of
  **its own** disparities. The candidate instants are fixed by the speeds; nothing is searched over.
- `exists_lonelyAt_iff_bounded` — whole-number disparities: only openings `j < e` need be read.

## 4. Named instants, restated on the arrangement

- `lonelyAt_inv_of_not_dvd` — whole-number speeds, no disparity a multiple of 8 ⇒ the subject is
  lonely at `t = 1/8`. The instant is written down. `[PROVED]`
- `lonelyAt_named_instant` — choose `c ∈ ℤ₊` and a lap `j`; the subject is lonely at `(j + 1/8)/c`
  when each disparity `a` satisfies `c ≤ a(8j+1) mod 8c ≤ 7c`. `c` need not be a disparity. `[PROVED]`
- `exists_lonelyAt_of_not_dvd`, `exists_lonelyAt_of_named_instant` — the witnesses. `[PROVED]`

## 5. The obligation

```
def ExistenceOnArrangements : Prop :=
  ∀ v : Fin 8 → ℝ, Function.Injective v → ∀ k : Fin 8, ∃ t, 0 < t ∧ Arrangement.LonelyAt v k t

theorem lonelyRunnerAt8_iff_existenceOnArrangements : LonelyRunnerAt8 ↔ ExistenceOnArrangements :=
  Iff.rfl
```

`Iff.rfl`. Not a reduction, not a sufficient condition: **the obligation is now the conjecture
itself**, stated in the objects the framework works in. `lonelyRunnerAt8_of_arrangement` is the
identity.

## 6. Status of `ExistenceAt8`

Retained in `Spec/Target.lean`, marked AMENDED, still proved sufficient
(`lonelyRunnerAt8_of_existence`). It is no longer on the path to the target and no result in
`Arrangement.lean` uses it.

## 7. What this does not do

It does not close Existence. It relocates the obligation to where the mechanisms are stated, and
makes the existing flank/opening/residue library available there. The open work is unchanged: no
arrangement-level theorem here covers all injective `v`.
