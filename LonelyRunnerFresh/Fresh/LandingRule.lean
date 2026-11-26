import Mathlib

/-!
# The landing rule: the first lonely instant is the left end of the first alive component

Written 2026-10-24.  New file; imports Mathlib only.  Abstract statement of what `experiments/n8/landing_pred_v1.c` tests.

A subject's perturbed lonely set `lonely : ℝ → Prop` sits in windows `[A c, B c]` indexed by the unperturbed components `c` in a
linear order `ι`.  Inside window `c` the lonely instants are `[mx c, mn c]` (largest exit, least entry: `Fresh.WindowFO.window_iff_maxmin`).
`alive c` means `mx c ≤ mn c`.  `landing_rule`: if no window before `c₀` is alive and `c₀` is, the first lonely instant is `mx c₀`.

**[PROVISIONAL: covering]** at `hcov` (every lonely instant lies in a window; it supports the claim that the first lonely instant is the largest exit of the first alive component).

Hypotheses (all named, none proved here): `hwin` (the first-order description of each window), `hcov` (locality: every lonely instant
lies in a window), `hsep` (windows ordered and disjoint), `hmxw` (an alive component's largest exit lies in its window).  These are
the finite checks the exact scan confirms on the stated boxes; they are [OWED] as theorems for arbitrary arrangements.  Grade: [L]
conditional on those four hypotheses.  Not claimed: that they hold for any given arrangement, any radius, or the cascade's jump rule.
-/

namespace Fresh.LandingRule

variable {ι : Type*} [LinearOrder ι]

/-- A window component is alive when its largest exit is at or before its least entry. -/
-- STANDING: DEFINITION
def Alive (mx mn : ι → ℝ) (c : ι) : Prop := mx c ≤ mn c

theorem landing_rule (lonely : ℝ → Prop) (A B mx mn : ι → ℝ)
    (hsep : ∀ c c', c < c' → B c < A c')
    (hwin : ∀ c t, A c ≤ t → t ≤ B c → (lonely t ↔ mx c ≤ t ∧ t ≤ mn c))
    -- [PROVISIONAL: covering] `hcov` supports: the first lonely instant is the largest exit of the first alive component
    (hcov : ∀ t, lonely t → ∃ c, A c ≤ t ∧ t ≤ B c)
    (hmxw : ∀ c, Alive mx mn c → A c ≤ mx c ∧ mx c ≤ B c)
    (c₀ : ι) (h₀ : Alive mx mn c₀) (hbefore : ∀ c, c < c₀ → ¬ Alive mx mn c) :
    lonely (mx c₀) ∧ ∀ t, lonely t → mx c₀ ≤ t := by
  obtain ⟨hA, hB⟩ := hmxw c₀ h₀
  refine ⟨(hwin c₀ _ hA hB).2 ⟨le_rfl, h₀⟩, fun t ht => ?_⟩
  obtain ⟨c, h1, h2⟩ := hcov t ht
  rcases lt_trichotomy c c₀ with hc | hc | hc
  · exact absurd (show Alive mx mn c from le_trans ((hwin c t h1 h2).1 ht).1 ((hwin c t h1 h2).1 ht).2) (hbefore c hc)
  · subst hc; exact ((hwin c t h1 h2).1 ht).1
  · exact le_trans hB (le_trans (le_of_lt (hsep c₀ c hc)) h1)

/-- The first lonely instant, as a least element. -/
theorem landing_isLeast (lonely : ℝ → Prop) (A B mx mn : ι → ℝ)
    (hsep : ∀ c c', c < c' → B c < A c')
    (hwin : ∀ c t, A c ≤ t → t ≤ B c → (lonely t ↔ mx c ≤ t ∧ t ≤ mn c))
    (hcov : ∀ t, lonely t → ∃ c, A c ≤ t ∧ t ≤ B c)
    (hmxw : ∀ c, Alive mx mn c → A c ≤ mx c ∧ mx c ≤ B c)
    (c₀ : ι) (h₀ : Alive mx mn c₀) (hbefore : ∀ c, c < c₀ → ¬ Alive mx mn c) :
    IsLeast {t | lonely t} (mx c₀) := by
  obtain ⟨a, b⟩ := landing_rule lonely A B mx mn hsep hwin hcov hmxw c₀ h₀ hbefore
  exact ⟨a, fun t ht => b t ht⟩

/-- Non-vacuity: one window `[1, 2]` with exit `1` and entry `2` (alive), lonely set `[1, 2]`. -/
theorem landing_nonvacuous :
    IsLeast {t : ℝ | 1 ≤ t ∧ t ≤ 2} 1 := by
  refine landing_isLeast (ι := Unit) (fun t => 1 ≤ t ∧ t ≤ 2) (fun _ => 1) (fun _ => 2) (fun _ => 1) (fun _ => 2)
    (fun c c' h => absurd h (by simp)) (fun c t h1 h2 => by simp) (fun t ht => ⟨(), ht⟩)
    (fun c _ => ⟨le_rfl, by norm_num⟩) () (by simp [Alive]) (fun c hc => absurd hc (by simp))

#print axioms landing_rule
#print axioms landing_isLeast
#print axioms landing_nonvacuous

end Fresh.LandingRule
