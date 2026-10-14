import LonelyRunner.LRC.Spec.HandoffDriftN
import LonelyRunner.LRC.Spec.OneFreeN
import LonelyRunner.LRC.Spec.TwoPinnerN

/-!
# The whole arrangement constrains a zero-drift replay

A pair's period need not be a period of the remaining readings. A reading cannot
stay blocked at the same relative instant on EVERY replay unless its phase advance
is a whole lap. This follows from the existing native `OneFree.exists_clear_step`,
and does not assume that the successive blocking laps have a fixed increment.

Consequently an indefinitely repeated finite blocking schedule forces all readings
used by that schedule onto a common time lattice, not a complete residue grid mod 8.
It does not prove that such a
schedule covers the intervening times, nor rule out nonperiodic role changes.
-/

namespace LRC.HandoffResonance

open MomentIterationN

/-- An off-lattice reading eventually vacates any specified periodic blocking role. -/
theorem off_lattice_role_breaks {d t P : ℝ}
    (hoff : ∀ z : ℤ, d * P ≠ z) :
    ∃ q : ℕ, ¬ inWay 8 d (t + q * P) := by
  obtain ⟨q, hq⟩ := LRC.OneFree.exists_clear_step (d * t) hoff
  refine ⟨q, ?_⟩
  unfold inWay
  have he : d * (t + (q : ℝ) * P) = d * t + q * (d * P) := by ring
  rw [he]
  exact not_lt_of_ge hq

/-- Persistent periodic blocking forces integral phase advance, even when the
blocking lap at each replay is not specified in advance. -/
theorem persistent_role_integral {d t P : ℝ}
    (h : ∀ q : ℕ, inWay 8 d (t + q * P)) :
    ∃ z : ℤ, d * P = z := by
  by_contra hn
  push Not at hn
  obtain ⟨q, hq⟩ := off_lattice_role_breaks (t := t) hn
  exact hq (h q)

/-- Every role of a perpetual repeated schedule shares the same time lattice.
The index type may describe runner identities or individual occurrences in a word. -/
theorem persistent_schedule_common_lattice {ι : Type*} (d t : ι → ℝ) (P : ℝ)
    (h : ∀ i, ∀ q : ℕ, inWay 8 (d i) (t i + q * P)) :
    ∃ z : ι → ℤ, ∀ i, d i * P = z i := by
  have hi : ∀ i, ∃ z : ℤ, d i * P = z := fun i => persistent_role_integral (h i)
  choose z hz using hi
  exact ⟨z, hz⟩

/-- Once the phase advance is integral, all later blocking laps follow one affine
pattern. Thus varying lap labels cannot evade the preceding common-grid condition. -/
theorem integral_phase_lap_transport {d t P : ℝ} {z K : ℤ}
    (hz : d * P = z) (q : ℕ) :
    d * (t + q * P) - ((K + (q : ℤ) * z : ℤ) : ℝ) = d * t - K := by
  push_cast
  calc
    d * (t + q * P) - ((K : ℝ) + q * z) =
        d * t - K + q * (d * P - z) := by ring
    _ = d * t - K := by rw [hz]; ring

/-- The continuous scale-invariant region containing the three surviving zero-drift
returns in the exact experiment. The resonant pair is `(4D,5D)`; the other readings
clear the opening `65/(8c)` in its next-period joint gap. These explicit inequalities
cover a region of arrangements, not arbitrary seven-reading configurations. -/
theorem isolation_in_resonant_pair_gap {m p q D c f : ℝ} (hc : 0 < c)
    (hm : 9 * c ≤ 65 * m ∧ 65 * m ≤ 15 * c)
    (hp : 25 * c ≤ 65 * p ∧ 65 * p ≤ 31 * c)
    (hq : 33 * c ≤ 65 * q ∧ 65 * q ≤ 39 * c)
    (hD : 57 * c ≤ 325 * D ∧ 260 * D ≤ 47 * c)
    (hf : 81 * c ≤ 65 * f ∧ 65 * f ≤ 87 * c) :
    0 < 65 / (8 * c) ∧ ∀ x ∈ ({m, p, q, 4 * D, 5 * D, c, f} : Finset ℝ),
      (8 : ℝ)⁻¹ ≤ circDist (x * (65 / (8 * c))) := by
  have clear (v : ℝ) (N : ℤ)
      (hlo : (8 * (N : ℝ) + 1) * c ≤ 65 * v)
      (hhi : 65 * v ≤ (8 * (N : ℝ) + 7) * c) :
      (8 : ℝ)⁻¹ ≤ circDist (v * (65 / (8 * c))) := by
    rw [show v * (65 / (8 * c)) = (65 * v) / (8 * c) by ring]
    apply LRC.TwoPinner.clear_of_band (N := N)
    · apply (le_div_iff₀ (by positivity : 0 < 8 * c)).mpr
      nlinarith [hlo]
    · apply (div_le_iff₀ (by positivity : 0 < 8 * c)).mpr
      nlinarith [hhi]
  refine ⟨by positivity, ?_⟩
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx
  all_goals subst x
  · apply clear m 1 <;> norm_num <;> linarith [hm.1, hm.2]
  · apply clear p 3 <;> norm_num <;> linarith [hp.1, hp.2]
  · apply clear q 4 <;> norm_num <;> linarith [hq.1, hq.2]
  · apply clear (4 * D) 5 <;> norm_num <;> nlinarith [hD.1, hD.2]
  · apply clear (5 * D) 7 <;> norm_num <;> nlinarith [hD.1, hD.2]
  · apply clear c 8 <;> norm_num
    linarith
  · apply clear f 10 <;> norm_num <;> linarith [hf.1, hf.2]

end LRC.HandoffResonance
