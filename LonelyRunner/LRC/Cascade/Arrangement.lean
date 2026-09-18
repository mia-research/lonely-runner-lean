import LonelyRunner.LRC.Cascade.Flanks

/-!
# The framework's objects on an arrangement

Part of the cascade artefact (`LRC/Cascade/`).  Threshold `1/8`, eight runners.

Everything else in the artefact is stated on a **difference set** `ds : Finset ℝ`.  That form is
equivalent to the conjecture but demands machinery the conjecture does not: `Finset ℝ` forces
decidable equality, it **collapses duplicates** and so destroys the indexing, and `card ≤ 7` admits
difference sets no arrangement can produce.  Most importantly the **arrangement is gone** — gaps, the
AP structure, the coupling across the eight subjects, and "the subject and its two neighbours" are
arrangement-level and are not expressible in `ds` alone.

This module states the same objects on the arrangement itself, where the indexing survives.  See
`docs/n8/TARGET_AMENDMENT_2026_09_18_v1.md`.

* `sep v k i t` — the separation of runner `i` from runner `k`.  Neither is at `0`; both move.
* `InWay`, `LonelyAt` — in the way of the subject, and the subject lonely.
* `lonelyAt_iff_no_inWay`, `lonelyAt_iff_two_sided`, `lonelyAt_iff_neighbours` — loneliness is a
  statement about the subject's **two neighbours** and nothing else.
-/

set_option linter.unusedVariables false

namespace Arrangement

open ConstructionN MomentIterationN

/-- **The separation of runner `i` from runner `k` at time `t`.**  Nothing is placed at `0` and
nothing is held still: this is the gap between two moving runners. -/
def sep (v : Fin 8 → ℝ) (k i : Fin 8) (t : ℝ) : ℝ := v i * t - v k * t

/-- The separation is carried by the speed difference. -/
theorem sep_eq (v : Fin 8 → ℝ) (k i : Fin 8) (t : ℝ) : sep v k i t = (v i - v k) * t := by
  unfold sep; ring

/-- **`i` is in the way of `k` at `t`.** -/
def InWay (v : Fin 8 → ℝ) (k i : Fin 8) (t : ℝ) : Prop := circDist (sep v k i t) < (8 : ℝ)⁻¹

/-- **The subject `k` is lonely at `t`.** -/
def LonelyAt (v : Fin 8 → ℝ) (k : Fin 8) (t : ℝ) : Prop :=
  ∀ i : Fin 8, i ≠ k → (8 : ℝ)⁻¹ ≤ circDist (sep v k i t)

/-- **Lonely is exactly: nobody in the way.** -/
theorem lonelyAt_iff_no_inWay {v : Fin 8 → ℝ} {k : Fin 8} {t : ℝ} :
    LonelyAt v k t ↔ ∀ i : Fin 8, i ≠ k → ¬ InWay v k i t := by
  unfold LonelyAt InWay
  exact ⟨fun h i hi => not_lt.mpr (h i hi), fun h i hi => not_lt.mp (h i hi)⟩

/-- **Loneliness splits into one condition per side of the subject.** -/
theorem lonelyAt_iff_two_sided {v : Fin 8 → ℝ} {k : Fin 8} {t : ℝ} :
    LonelyAt v k t ↔
      (∀ i : Fin 8, i ≠ k → (8 : ℝ)⁻¹ ≤ Int.fract (sep v k i t)) ∧
      (∀ i : Fin 8, i ≠ k → Int.fract (sep v k i t) ≤ 1 - (8 : ℝ)⁻¹) := by
  unfold LonelyAt circDist
  constructor
  · intro h
    refine ⟨fun i hi => le_trans (h i hi) (min_le_left _ _), fun i hi => ?_⟩
    have := le_trans (h i hi) (min_le_right _ _); linarith
  · rintro ⟨h1, h2⟩ i hi
    exact le_min (h1 i hi) (by have := h2 i hi; linarith)

/-- The other seven runners form a nonempty set. -/
theorem others_nonempty (k : Fin 8) : (Finset.univ.erase k).Nonempty := by
  rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ k)]
  simp

/-- **Only the two neighbours matter.**  The subject is lonely exactly when the runner nearest ahead
— least fractional separation — is at least `1/8`, and the one nearest behind is at most `7/8`.  The
other five impose nothing.  This is the sense in which an isolation is affected by three speeds: the
subject's and its two neighbours'. -/
theorem lonelyAt_iff_neighbours {v : Fin 8 → ℝ} {k : Fin 8} {t : ℝ} :
    LonelyAt v k t ↔
      (8 : ℝ)⁻¹ ≤ (Finset.univ.erase k).inf' (others_nonempty k)
          (fun i => Int.fract (sep v k i t)) ∧
      (Finset.univ.erase k).sup' (others_nonempty k)
          (fun i => Int.fract (sep v k i t)) ≤ 1 - (8 : ℝ)⁻¹ := by
  rw [lonelyAt_iff_two_sided, Finset.le_inf'_iff, Finset.sup'_le_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i hi => h1 i (Finset.mem_erase.mp hi).1, fun i hi => h2 i (Finset.mem_erase.mp hi).1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i hi => h1 i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩),
           fun i hi => h2 i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)⟩

end Arrangement
