import LonelyRunner.LRC.Spec.OrderSixPropElevenN

/-!
# BHK Proposition 11 at named instants

`OrderSixPropElevenN` ports BHK's Proposition 11 in BHK's own form: assume the
runners cover every time (`B₀ = ℝ⁺`) and derive `False`. That form concludes by
emptiness, which the framework does not use. This file is the same proof,
lemma for lemma, with the covering removed.

Wherever BHK's argument reads the covering at an instant `τ` it now asks
whether `τ` is lonely (`found_or_blocked`): if it is, `τ` is the named instant
and the case closes; if not, some runner blocks `τ`, and BHK's argument
continues unchanged. So

* a lemma that ended in `False` now ends in `Found w`, a lonely instant, and
  every branch that produces one names it;
* a lemma with conclusion `P` now ends in `Found w ∨ P`.

Part 2 adds BHK's fictional runner of speed `2 w₀` (`Found6`).

The lemmas that do not read the covering are used from `OrderSixPropElevenN`
as they are. The names here are those of the source, in the namespace
`LRC.OrderSixN.S7.Named`.
-/

open MeasureTheory Set

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.show false
set_option linter.style.multiGoal false
set_option linter.style.setOption false
set_option linter.flexible false

namespace LRC.OrderSixN.S7.Named

open LRC.OrderSixN

/-- A lonely instant for the five speeds `w` at `1/6`. -/
def Found (w : Fin 5 → ℕ) : Prop :=
  ∃ t : ℝ, ∀ i, (1 : ℝ) / 6 ≤ circDist ((w i : ℝ) * t)

/-- A lonely instant at which BHK's fictional runner `2 w₀` is also clear. -/
def Found6 (w : Fin 5 → ℕ) : Prop :=
  ∃ t : ℝ, (∀ i, (1 : ℝ) / 6 ≤ circDist ((w i : ℝ) * t)) ∧
    (1 : ℝ) / 6 ≤ circDist (2 * ((w ⟨0, by omega⟩ : ℝ) * t))

/-- **The instant `τ` is read.** Either `τ` is lonely, and is the named instant,
    or some runner is within `1/6` of the origin at `τ`. -/
theorem found_or_blocked (w : Fin 5 → ℕ) (τ : ℝ) :
    Found w ∨ ∃ i, circDist ((w i : ℝ) * τ) < 1 / 6 := by
  by_cases h : ∀ i, (1 : ℝ) / 6 ≤ circDist ((w i : ℝ) * τ)
  · exact Or.inl ⟨τ, h⟩
  · push_neg at h
    exact Or.inr h

/-- **The instant `τ` is read, with the fictional runner.** Either `τ` is
    lonely with `2 w₀` also clear, or some runner (possibly `2 w₀`) blocks `τ`. -/
theorem found6_or_blocked (w : Fin 5 → ℕ) (τ : ℝ) :
    Found6 w ∨ (∃ i, circDist ((w i : ℝ) * τ) < 1 / 6) ∨
      circDist (2 * ((w ⟨0, by omega⟩ : ℝ) * τ)) < 1 / 6 := by
  by_cases h : ∀ i, (1 : ℝ) / 6 ≤ circDist ((w i : ℝ) * τ)
  · by_cases h0 : (1 : ℝ) / 6 ≤ circDist (2 * ((w ⟨0, by omega⟩ : ℝ) * τ))
    · exact Or.inl ⟨τ, h, h0⟩
    · exact Or.inr (Or.inr (not_le.mp h0))
  · push_neg at h
    exact Or.inr (Or.inl h)

/-- **The instants of a named set are read.** Either one of them is lonely, or
    every one is blocked by some runner. Used only on explicit sets (a named
    gap `[a, b]`, or its translates by multiples of `1/g`), never on all times. -/
theorem found_or_blocked_on (w : Fin 5 → ℕ) (S : Set ℝ) :
    Found w ∨ ∀ τ ∈ S, ∃ i, circDist ((w i : ℝ) * τ) < 1 / 6 := by
  by_cases h : ∃ τ ∈ S, ∀ i, (1 : ℝ) / 6 ≤ circDist ((w i : ℝ) * τ)
  · obtain ⟨τ, -, hτ⟩ := h
    exact Or.inl ⟨τ, hτ⟩
  · push_neg at h
    exact Or.inr h

/-- Six-runner form of `found_or_blocked_on`. -/
theorem found6_or_blocked_on (w : Fin 5 → ℕ) (S : Set ℝ) :
    Found6 w ∨ ∀ τ ∈ S, (∃ i, circDist ((w i : ℝ) * τ) < 1 / 6) ∨
      circDist (2 * ((w ⟨0, by omega⟩ : ℝ) * τ)) < 1 / 6 := by
  by_cases h : ∃ τ ∈ S, (∀ i, (1 : ℝ) / 6 ≤ circDist ((w i : ℝ) * τ)) ∧
      (1 : ℝ) / 6 ≤ circDist (2 * ((w ⟨0, by omega⟩ : ℝ) * τ))
  · obtain ⟨τ, -, hτ⟩ := h
    exact Or.inl ⟨τ, hτ⟩
  · refine Or.inr fun τ hτ => ?_
    by_cases h1 : ∀ i, (1 : ℝ) / 6 ≤ circDist ((w i : ℝ) * τ)
    · exact Or.inr (not_le.mp fun h2 => h ⟨τ, hτ, h1, h2⟩)
    · push_neg at h1
      exact Or.inl h1

