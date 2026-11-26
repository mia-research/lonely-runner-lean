import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.CascadeLanding
import Fresh.ClassInstantView

/-!
# Displacing one reading: where the landing goes (E754)

Written 2026-11-01.  New file; nothing existing is edited.  Any finite set `R` of readings is frozen (rule 3, M037)
and one reading is displaced from `f₀` to `f₁`.  `T₀` is the first lonely instant (the cascade's landing,
`cascade_landsG`) with `f₀`, `T₁` with `f₁`.  No AP, no grid, no covering or counting step.

* `displaced_freeze_iff`: the landing stays at `T₀` iff `f₁` is clear at `T₀` and `f₁` is in the way at every earlier
  instant at which the frozen readings `R` are all clear.
* `displaced_earlier`: a landing before `T₀` is an instant at which `R` is clear and `f₀` was in the way: `f₀` was the
  only blocker there.
* `displaced_le_of_clear`: if `f₁` is clear at `T₀`, the landing does not move later.
* `displaced_ne_of_blocked`: if `f₁` is in the way at `T₀`, the landing moves.
* `setter_carried`: the setter's own class-1 instant `(8M+1)/(8f₁)` puts `f₁` exactly on its leaving edge, for every
  `f₁ > 0` (the carried landing, E747's `self_at_class_instant`).

Grades: [L].
-/

namespace Fresh.OneMover

open Fresh

theorem lonelyAt_insert {R : Finset ℝ} {f s : ℝ} :
    Fresh.Cascade.LonelyAt (insert f R) s ↔ (1 / 8 : ℝ) ≤ distInt (f * s) ∧ Fresh.Cascade.LonelyAt R s := by
  unfold Fresh.Cascade.LonelyAt
  simp

/-- **The freeze rule for the landing.**  With `R` frozen and one reading displaced from `f₀` to `f₁`, the landing
stays at `T₀` iff `f₁` is clear at `T₀` and `f₁` is in the way at every earlier positive instant at which `R` is
clear. -/
theorem displaced_freeze_iff {R : Finset ℝ} {f₀ f₁ T₀ : ℝ} (hT₀ : IsFirst (insert f₀ R) T₀) :
    IsFirst (insert f₁ R) T₀ ↔
      (1 / 8 : ℝ) ≤ distInt (f₁ * T₀) ∧
        ∀ s : ℝ, 0 < s → s < T₀ → Fresh.Cascade.LonelyAt R s → distInt (f₁ * s) < 1 / 8 := by
  have hR : Fresh.Cascade.LonelyAt R T₀ := (lonelyAt_insert.mp hT₀.1).2
  constructor
  · rintro ⟨hl, hmin⟩
    refine ⟨(lonelyAt_insert.mp hl).1, fun s hs hsT hRs => ?_⟩
    by_contra hc
    push Not at hc
    exact absurd (hmin s hs (lonelyAt_insert.mpr ⟨hc, hRs⟩)) (not_le.mpr hsT)
  · rintro ⟨hc, hno⟩
    refine ⟨lonelyAt_insert.mpr ⟨hc, hR⟩, fun s hs hl => ?_⟩
    by_contra hlt
    push Not at hlt
    obtain ⟨h1, hRs⟩ := lonelyAt_insert.mp hl
    exact absurd h1 (not_le.mpr (hno s hs hlt hRs))

/-- **An earlier landing opens only where `f₀` alone blocked.** -/
theorem displaced_earlier {R : Finset ℝ} {f₀ f₁ T₀ s : ℝ} (hT₀ : IsFirst (insert f₀ R) T₀) (hs : 0 < s)
    (hsT : s < T₀) (hl : Fresh.Cascade.LonelyAt (insert f₁ R) s) :
    Fresh.Cascade.LonelyAt R s ∧ distInt (f₀ * s) < 1 / 8 := by
  have hRs := (lonelyAt_insert.mp hl).2
  refine ⟨hRs, ?_⟩
  by_contra hc
  push Not at hc
  exact absurd (hT₀.2 s hs (lonelyAt_insert.mpr ⟨hc, hRs⟩)) (not_le.mpr hsT)

/-- If `f₁` is clear at `T₀`, the new landing is not later than `T₀`. -/
theorem displaced_le_of_clear {R : Finset ℝ} {f₀ f₁ T₀ T₁ : ℝ} (hT₀ : IsFirst (insert f₀ R) T₀) (hT₀pos : 0 < T₀)
    (hT₁ : IsFirst (insert f₁ R) T₁) (hc : (1 / 8 : ℝ) ≤ distInt (f₁ * T₀)) : T₁ ≤ T₀ :=
  hT₁.2 T₀ hT₀pos (lonelyAt_insert.mpr ⟨hc, (lonelyAt_insert.mp hT₀.1).2⟩)

/-- If `f₁` is in the way at `T₀`, the landing moves. -/
theorem displaced_ne_of_blocked {R : Finset ℝ} {f₁ T₀ T₁ : ℝ} (hT₁ : IsFirst (insert f₁ R) T₁)
    (hb : distInt (f₁ * T₀) < 1 / 8) : T₁ ≠ T₀ := by
  rintro rfl
  exact absurd (lonelyAt_insert.mp hT₁.1).1 (not_le.mpr hb)

/-- **The carried landing.**  At its own class-1 instant `(8M+1)/(8f₁)` the displaced reading stands exactly on its
leaving edge, whatever `f₁ > 0` is. -/
theorem setter_carried (f₁ : ℝ) (hf : 0 < f₁) (M : ℤ) :
    distInt (f₁ * ((8 * (M : ℝ) + 1) / (8 * f₁))) = 1 / 8 :=
  self_at_class_instant f₁ hf.ne' M

#print axioms lonelyAt_insert
#print axioms displaced_freeze_iff
#print axioms displaced_earlier
#print axioms displaced_le_of_clear
#print axioms displaced_ne_of_blocked
#print axioms setter_carried

end Fresh.OneMover
