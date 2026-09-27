import LonelyRunner.LRC.Spec.EndRunnerN

/-!
# The order-eight skeleton on the slowest runner, split on its own gap

2026-09-26 (proof plan `docs/n8/PROOF_PLAN_ORDER8_v1.md`, WP1).  By `lonelyRunnerAt8_of_slowest` only the slowest
runner of each arrangement of eight distinct positive whole-number speeds remains.  Its readings are the running sums
of the speed gaps, so its least reading is its own gap `g₁` and its greatest is the spread `W`.  Split on `W/g₁`:

* **Case A**, `W ≤ 7·g₁` — the first reading, R1 (`lonely_eight_of_spread`).  **Proved.**
* **Case B**, `7·g₁ < W ≤ T·g₁` — `CaseB8 T`, **OWED** (registered).  At `T = 22` it is verified by the exact
  climb-cell certificates (`experiments/nN/redo/climb_cells_v3*`, running log E49–E55); not yet in Lean.
* **Case C**, `T·g₁ < W` — `CaseC8 T`, **OWED** (registered).  The subject is in a close pair.

`lonelyRunnerAt8_of_cases` proves the conjecture at eight runners from `CaseB8 T` and `CaseC8 T`, for any `T`.  The
split is exhaustive by construction.  Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.SlowestSkeleton

open LRC.OrderEightN LRC.Order8Skeleton

/-! **Off the path (E166).**  The spread split at `T` came from the range of the old certificates; the conjecture now
follows from the single spread-free covering `RegimeSkeleton.Cover8` (`lonelyRunnerAt8_of_cover8`).  `CaseB8`, `CaseC8`
stay registered OWED for the record; nothing on the current path uses them. -/

/-- **Case B** at threshold `T`: the slowest runner whose greatest reading lies in `(7m, T·m]`, `m` its least. -/
def CaseB8 (T : ℕ) : Prop :=
  ∀ v : Fin 8 → ℕ, Arr8 v → (∀ i, v 0 ≤ v i) → ∀ m ∈ readingsOf v 0, (∀ d ∈ readingsOf v 0, m ≤ d) →
    (∃ d ∈ readingsOf v 0, 7 * m < d) → (∀ d ∈ readingsOf v 0, d ≤ T * m) → Lonely8 (readingsOf v 0)

/-- **Case C** at threshold `T`: the slowest runner with some reading above `T·m`. -/
def CaseC8 (T : ℕ) : Prop :=
  ∀ v : Fin 8 → ℕ, Arr8 v → (∀ i, v 0 ≤ v i) → ∀ m ∈ readingsOf v 0, (∀ d ∈ readingsOf v 0, m ≤ d) →
    (∃ d ∈ readingsOf v 0, T * m < d) → Lonely8 (readingsOf v 0)

/-- Every reading of a runner in an arrangement of distinct speeds is positive. -/
theorem readingsOf_pos {v : Fin 8 → ℕ} (hv : Arr8 v) (k : Fin 8) : ∀ d ∈ readingsOf v k, 0 < d := by
  intro d hd
  unfold readingsOf at hd
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
  have hik : i ≠ k := (Finset.mem_erase.mp hi).1
  have hne : v i ≠ v k := fun h => hik (hv.2 h)
  exact Nat.dist_pos_of_ne hne

theorem readingsOf_nonempty (v : Fin 8 → ℕ) (k : Fin 8) : (readingsOf v k).Nonempty := by
  unfold readingsOf
  obtain ⟨i, hi⟩ := Arrangement.others_nonempty k
  exact ⟨_, Finset.mem_image_of_mem _ hi⟩

/-- **The conjecture at eight runners from Cases B and C** (Case A is R1). -/
theorem lonelyRunnerAt8_of_cases (T : ℕ) (hB : CaseB8 T) (hC : CaseC8 T) : LRC.Spec.LonelyRunnerAt8 := by
  refine LRC.EndRunner.lonelyRunnerAt8_of_slowest fun v hv hslow => ?_
  classical
  set S := readingsOf v 0 with hS
  have hne := readingsOf_nonempty v 0
  have hpos := readingsOf_pos hv 0
  set m := S.min' hne with hm
  have hmS : m ∈ S := Finset.min'_mem S hne
  have hmin : ∀ d ∈ S, m ≤ d := fun d hd => Finset.min'_le S d hd
  have hm0 : 0 < m := hpos m hmS
  by_cases hA : ∀ d ∈ S, d ≤ 7 * m
  · exact lonely_eight_of_spread hm0 hmin hA
  push Not at hA
  by_cases hBc : ∀ d ∈ S, d ≤ T * m
  · exact hB v hv hslow m hmS hmin hA hBc
  push Not at hBc
  exact hC v hv hslow m hmS hmin hBc

end LRC.SlowestSkeleton
