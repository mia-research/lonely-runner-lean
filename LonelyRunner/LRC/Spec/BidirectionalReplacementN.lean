import LonelyRunner.LRC.Spec.DeadlineRelabelN

/-!
# Two-sided margins and forced replacement labels

If the six current clear bands are trapped inside the lone blocker's capture
slot, preserving all six labels cannot repair the event. The lower and upper
guards force different label changes on the two sides. These are local
necessary conditions, not a termination or global coverage assertion.
-/

namespace LRC.BidirectionalReplacement

/-- Exact backward counterpart of `DeadlineRelabel.forward_margin_iff`. -/
theorem backward_margin_iff {b d z g : ℝ} (hb : 0 < b) (hd : 0 ≤ d)
    (hz : -(1 / 8) ≤ z) (hg : g ≤ 7 / 8) :
    (1 / 8 ≤ g - d * ((z + 1 / 8) / b) ∧
      g - d * ((z + 1 / 8) / b) ≤ 7 / 8) ↔
      d * (z + 1 / 8) ≤ b * (g - 1 / 8) := by
  have hn : 0 ≤ d * ((z + 1 / 8) / b) :=
    mul_nonneg hd (div_nonneg (by linarith) hb.le)
  have he : d * ((z + 1 / 8) / b) = (d * (z + 1 / 8)) / b := by ring
  rw [he]
  constructor
  · intro h
    have hh : (d * (z + 1 / 8)) / b ≤ g - 1 / 8 := by linarith [h.1]
    have := (div_le_iff₀ hb).mp hh
    nlinarith
  · intro h
    have hh : (d * (z + 1 / 8)) / b ≤ g - 1 / 8 :=
      (div_le_iff₀ hb).mpr (by nlinarith)
    constructor <;> linarith

/-- A single reading that exhausts BOTH directional margins is faster than
three times the blocker. The two required displacements sum to 1/(4b). -/
theorem same_guard_fast {b d z g : ℝ}
    (hf : b * (7 / 8 - g) < d * (1 / 8 - z))
    (hb : b * (g - 1 / 8) < d * (z + 1 / 8)) : 3 * b < d := by
  nlinarith

/-- If all other disparities are at most three times the blocker, failures
in opposite directions must have distinct guarding readings. -/
theorem guards_distinct (d g : ι → ℝ) {b z : ℝ} {i j : ι}
    (hsmall : d i ≤ 3 * b)
    (hf : b * (7 / 8 - g i) < d i * (1 / 8 - z))
    (hb : b * (g j - 1 / 8) < d j * (z + 1 / 8)) : i ≠ j := by
  intro h
  subst j
  exact (not_lt_of_ge hsmall) (same_guard_fast hf hb)

/-- Opposite guards trap every time retaining their current bands between
the blocker's two capture edges. Other readings cannot remove this obstruction. -/
theorem guarded_interval_trapped {a c u l r : ℝ} {p q : ℤ}
    (ha : 0 < a) (hc : 0 < c)
    (hleft : a * l < (p : ℝ) + 1 / 8)
    (hright : (q : ℝ) + 7 / 8 < c * r)
    (hu : (p : ℝ) + 1 / 8 ≤ a * u)
    (hv : c * u ≤ (q : ℝ) + 7 / 8) : l < u ∧ u < r := by
  constructor <;> nlinarith

/-- Past the forward edge, a guard whose current band has already closed
must receive a STRICTLY larger label at any clear candidate. -/
theorem forced_forward_label {d r u : ℝ} {p q : ℤ}
    (hd : 0 < d) (hu : r ≤ u)
    (hclose : (p : ℝ) + 7 / 8 < d * r)
    (hclear : d * u ≤ (q : ℝ) + 7 / 8) : p < q := by
  have hmul := mul_le_mul_of_nonneg_left hu hd.le
  have hcast : (p : ℝ) < (q : ℝ) := by linarith
  exact_mod_cast hcast

/-- Before the backward edge, a guard whose current opening has not been
reached must receive a STRICTLY smaller label at any clear candidate. -/
theorem forced_backward_label {d l u : ℝ} {p q : ℤ}
    (hd : 0 < d) (hu : u ≤ l)
    (hopen : d * l < (p : ℝ) + 1 / 8)
    (hclear : (q : ℝ) + 1 / 8 ≤ d * u) : q < p := by
  have hmul := mul_le_mul_of_nonneg_left hu hd.le
  have hcast : (q : ℝ) < (p : ℝ) := by linarith
  exact_mod_cast hcast

/-- The first forced successor label clears the blocker exactly when its
opening lies before the blocker's closing. This is linear after cross-multiplication. -/
theorem successor_pair_iff {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (K p : ℤ) :
    (((p : ℝ) + 1 + 1 / 8) / c ≤ ((K : ℝ) + 7 / 8) / b) ↔
      b * ((p : ℝ) + 1 + 1 / 8) ≤ c * ((K : ℝ) + 7 / 8) := by
  rw [div_le_div_iff₀ hc hb]
  constructor <;> intro h <;> nlinarith

/-- A two-sided failure discovered with exact arithmetic. Entries are subject
disparities, not ordered physical speeds. -/
noncomputable def centre : Fin 7 → ℝ :=
  ![89 / 8, 127 / 8, 79 / 32, 2119 / 128, 399 / 64, 87 / 64, 153 / 64]

/-- A six-dimensional neighbourhood after fixing the new setter's scale.
At t=3 only reading 5 (zero-based) is captured, on lap 4. -/
theorem family_initial (d : Fin 7 → ℝ)
    (hbox : ∀ i, |d i - centre i| ≤ 1 / 10000) :
    (∀ i, 0 < d i) ∧
    (∀ i, i ≠ 5 →
      let q : Fin 7 → ℤ := ![33, 47, 7, 49, 18, 4, 7]
      (q i : ℝ) + 1 / 8 ≤ d i * 3 ∧ d i * 3 ≤ (q i : ℝ) + 7 / 8) ∧
    (31 / 8 < d 5 * 3 ∧ d 5 * 3 < 33 / 8) := by
  have hh (i : Fin 7) := abs_le.mp (hbox i)
  constructor
  · intro i
    have h := hh i
    fin_cases i <;> norm_num [centre] at h ⊢ <;> linarith [h.1, h.2]
  constructor
  · intro i hi
    have h := hh i
    fin_cases i <;> norm_num [centre] at h ⊢ <;> try contradiction
    all_goals constructor <;> linarith [h.1, h.2]
  · have h := hh 5
    change -(1 / 10000 : ℝ) ≤ d 5 - 87 / 64 ∧ d 5 - 87 / 64 ≤ 1 / 10000 at h
    constructor <;> linarith [h.1, h.2]

/-- The first forward exit carries exactly the new setter into capture.
The conditions are proved throughout the box, not checked at sampled points. -/
theorem family_first_exit (d : Fin 7 → ℝ)
    (hbox : ∀ i, |d i - centre i| ≤ 1 / 10000) :
    let T := (33 / 8) / d 5
    (∀ i, i ≠ 4 →
      let q : Fin 7 → ℤ := ![33, 48, 7, 50, 18, 4, 7]
      (q i : ℝ) + 1 / 8 ≤ d i * T ∧ d i * T ≤ (q i : ℝ) + 7 / 8) ∧
    (151 / 8 < d 4 * T ∧ d 4 * T < 153 / 8) := by
  have hh (i : Fin 7) := abs_le.mp (hbox i)
  have hb := (family_initial d hbox).1 5
  have h5 := hh 5
  change -(1 / 10000 : ℝ) ≤ d 5 - 87 / 64 ∧ d 5 - 87 / 64 ≤ 1 / 10000 at h5
  have hindex : d ⟨5, by decide⟩ = d 5 := rfl
  have he (i : Fin 7) : d i * ((33 / 8) / d 5) = ((33 / 8) * d i) / d 5 := by ring
  dsimp only
  constructor
  · intro i hi
    rw [he]
    rw [le_div_iff₀ hb, div_le_iff₀ hb]
    have h := hh i
    fin_cases i <;> norm_num [centre] at h ⊢ <;> try contradiction
    all_goals constructor <;> nlinarith [h.1, h.2, h5.1, h5.2, hindex]
  · rw [he, lt_div_iff₀ hb, div_lt_iff₀ hb]
    have h := hh 4
    change -(1 / 10000 : ℝ) ≤ d 4 - 399 / 64 ∧ d 4 - 399 / 64 ≤ 1 / 10000 at h
    constructor <;> nlinarith [h.1, h.2, h5.1, h5.2]

/-- The forced successor opening clears the entire six-dimensional family.
It changes the old guard's label from 18 to 19; reading 0 also changes label
between the first and second exits. No claim that it stayed clear is needed. -/
theorem family_successor_bands (d : Fin 7 → ℝ)
    (hbox : ∀ i, |d i - centre i| ≤ 1 / 10000)
    (hsetter : d 4 = 399 / 64) :
    let q : Fin 7 → ℤ := ![34, 48, 7, 50, 19, 4, 7]
    ∀ i, (q i : ℝ) + 1 / 8 ≤ d i * (408 / 133) ∧
      d i * (408 / 133) ≤ (q i : ℝ) + 7 / 8 := by
  dsimp only
  intro i
  have h := abs_le.mp (hbox i)
  have hindex : d ⟨4, by decide⟩ = 399 / 64 := hsetter
  fin_cases i <;> norm_num [centre] at h ⊢
  all_goals constructor <;> nlinarith [h.1, h.2, hindex]

/-- Positive isolation at the analytically selected second opening. -/
theorem family_successor_clear (d : Fin 7 → ℝ)
    (hbox : ∀ i, |d i - centre i| ≤ 1 / 10000)
    (hsetter : d 4 = 399 / 64) :
    (0 : ℝ) < 408 / 133 ∧
      ∀ i, (8 : ℝ)⁻¹ ≤ circDist (d i * (408 / 133)) := by
  refine ⟨by norm_num, ?_⟩
  intro i
  exact TwoPinner.clear_of_band (family_successor_bands d hbox hsetter i).1
    (family_successor_bands d hbox hsetter i).2

end LRC.BidirectionalReplacement
