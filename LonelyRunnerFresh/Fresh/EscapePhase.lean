import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.PathLaws

/-!
# The phase law of an escape (E926)

Written 2026-11-24.  New file; nothing existing is edited.  Owner (2026-11-24): *"Resume the rule 4 step"*.

Rule 4 (M005): *"No matter how close two speeds are, they can never be the same speed.  As one is always by definition
faster, successive revolutions increasingly separate them."*  E794 left owed, in the `LeftClosed` form (E771): at a
point where approximants' lonely instants diverge, the limit has two runners at one speed.  This file proves what an
escape at a rational limit `w` with no isolation must look like, in the framework's objects.

* `phase_of_isolated`: if reading `i` of `w` is within `1/8 - δ` of the subject's slot at `t`, and `g` is isolated at
  `t`, then reading `i` of `g` and reading `i` of `w` have separated by at least `δ` laps by `t`:
  `δ ≤ |Δᵢ| · |t|`, with `Δᵢ` the difference of the two readings.
* `uniform_gap`: if every reading of `w` is a whole multiple of `1/P` and `w` has no isolation for `k`, there is one
  `δ > 0` such that at every instant some reading of `w` is within `1/8 - δ` of the subject's slot.
* `escape_phase`: together: one `δ > 0` with `δ ≤ |Δᵢ| · t` for some `i` at every isolation `t > 0` of every `g`.

Reading.  The two runners at nearly one speed in an escape are runner `i` of the approximant and runner `i` of the
limit.  Their readings differ by `Δᵢ → 0`, and an isolation of the approximant needs their phase `Δᵢ · t` to reach
`δ(w)`, so the instants grow at least like `δ / max |Δᵢ|`.  Nothing here asks two runners of `w` itself to coincide.

Grades: [L].  No counting or covering step: the compactness step is Bolzano on `[0, P]` (`tendsto_subseq_of_bounded`),
as in `PathLaws.isoSet_closed_of_bdd`.
-/

open Classical Filter Topology

namespace Fresh.EscapePhase

open Fresh Fresh.PathLaws

/-- **Phase of one reading** [L]: an isolation of `g` at `t` needs reading `i` of `g` to have moved at least `δ` laps
from reading `i` of `w`, when `w`'s reading `i` sits within `1/8 - δ` of the subject's slot at `t`. -/
theorem phase_of_isolated {w g : Fin 8 → ℝ} {k i : Fin 8} {t δ : ℝ} (hi : i ≠ k)
    (hw : distInt ((w i - w k) * t) ≤ 1 / 8 - δ) (hg : IsolatedAt g k t) :
    δ ≤ |(g i - g k) - (w i - w k)| * |t| := by
  have h1 := hg i hi
  have h2 := distInt_lipschitz ((g i - g k) * t) ((w i - w k) * t)
  have h3 : (g i - g k) * t - (w i - w k) * t = ((g i - g k) - (w i - w k)) * t := by ring
  rw [h3, abs_mul] at h2
  have h4 := (abs_le.mp h2).2
  linarith

#print axioms phase_of_isolated

/-- **A rational arrangement with no isolation misses the slot by a uniform gap** [L]. -/
theorem uniform_gap {w : Fin 8 → ℝ} {k : Fin 8} {P : ℝ} (hP : 0 < P)
    (hrat : ∀ i, ∃ n : ℤ, (w i - w k) * P = n) (hno : ¬ Isolation w k) :
    ∃ δ > 0, ∀ t : ℝ, ∃ i, i ≠ k ∧ distInt ((w i - w k) * t) ≤ 1 / 8 - δ := by
  by_contra hcon
  push Not at hcon
  have key : ∀ n : ℕ, ∃ t ∈ Set.Icc (0 : ℝ) P,
      ∀ i, i ≠ k → 1 / 8 - 1 / ((n : ℝ) + 1) < distInt ((w i - w k) * t) := by
    intro n
    obtain ⟨t, ht⟩ := hcon (1 / ((n : ℝ) + 1)) (by positivity)
    have hfl := Int.floor_le (t / P)
    have hfl2 := Int.lt_floor_add_one (t / P)
    have e1 : (⌊t / P⌋ : ℝ) * P ≤ t := by
      have := mul_le_mul_of_nonneg_right hfl hP.le
      rwa [div_mul_cancel₀ t hP.ne'] at this
    have e2 : t < ((⌊t / P⌋ : ℝ) + 1) * P := by
      have := mul_lt_mul_of_pos_right hfl2 hP
      rwa [div_mul_cancel₀ t hP.ne'] at this
    refine ⟨t - (⌊t / P⌋ : ℝ) * P, ⟨by linarith, by nlinarith⟩, fun i hi => ?_⟩
    obtain ⟨m, hm⟩ := hrat i
    have hrw : (w i - w k) * (t - (⌊t / P⌋ : ℝ) * P) =
        (w i - w k) * t + ((-(m * ⌊t / P⌋) : ℤ) : ℝ) := by
      have : (w i - w k) * ((⌊t / P⌋ : ℝ) * P) = (m : ℝ) * (⌊t / P⌋ : ℝ) := by
        rw [← hm]; ring
      push_cast
      linarith
    rw [hrw, Fresh.Localisation.distInt_add_int]
    exact ht i hi
  choose t htI hl using key
  obtain ⟨t₀, ht₀, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc (0 : ℝ) P)
    (x := t) (fun n => htI n)
  have hiso : IsolatedAt w k t₀ := by
    intro i hi
    have hc : Tendsto (fun n => distInt ((w i - w k) * t (φ n))) atTop (𝓝 (distInt ((w i - w k) * t₀))) :=
      (continuous_distInt.tendsto _).comp (tendsto_const_nhds.mul hlim)
    have hz : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    have hb : Tendsto (fun n : ℕ => 1 / 8 - 1 / ((φ n : ℝ) + 1)) atTop (𝓝 (1 / 8 - 0)) :=
      tendsto_const_nhds.sub hz
    have := le_of_tendsto_of_tendsto hb hc (Filter.Eventually.of_forall fun n => (hl (φ n) i hi).le)
    simpa using this
  have ht0 : 0 < t₀ := by
    have h0 : 0 ≤ t₀ := ge_of_tendsto hlim (Filter.Eventually.of_forall fun n => (htI (φ n)).1)
    rcases h0.lt_or_eq with h | h
    · exact h
    · exfalso
      obtain ⟨i, hi⟩ := PathLaws.exists_ne k
      have := hiso i hi
      rw [← h, mul_zero] at this
      simp [distInt] at this
      linarith
  exact hno ⟨t₀, ht0, hiso⟩

#print axioms uniform_gap

/-- **The phase law of an escape** [L]: at a rational arrangement `w` with no isolation for `k`, one `δ > 0` serves
every arrangement `g` and every isolation `t > 0` of `g`: some reading of `g` has moved at least `δ` laps from the same
reading of `w` by `t`, `δ ≤ |Δᵢ| · t`. -/
theorem escape_phase {w : Fin 8 → ℝ} {k : Fin 8} {P : ℝ} (hP : 0 < P)
    (hrat : ∀ i, ∃ n : ℤ, (w i - w k) * P = n) (hno : ¬ Isolation w k) :
    ∃ δ > 0, ∀ (g : Fin 8 → ℝ) (t : ℝ), 0 < t → IsolatedAt g k t →
      ∃ i, i ≠ k ∧ δ ≤ |(g i - g k) - (w i - w k)| * t := by
  obtain ⟨δ, hδ, hgap⟩ := uniform_gap hP hrat hno
  refine ⟨δ, hδ, fun g t ht hg => ?_⟩
  obtain ⟨i, hi, hw⟩ := hgap t
  have := phase_of_isolated hi hw hg
  rw [abs_of_pos ht] at this
  exact ⟨i, hi, this⟩

#print axioms escape_phase

end Fresh.EscapePhase
