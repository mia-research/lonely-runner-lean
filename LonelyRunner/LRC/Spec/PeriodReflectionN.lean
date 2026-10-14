import LonelyRunner.LRC.Spec.PinchReflectionN

/-!
# Replacement labels from the next exact return

Keep the incoming labels unchanged. At a positive clear instant `t`, reflect
at `(floor (t / H) + 1) * H`, where `H` is a common period of the current
readings. The reflected instant lies in `(0,H]`, and each replacement label
lies in `[0,E i)`, where `E i = d i * H` is an integer.

This is a bound derived from an exact return at ONE arrangement. It is not a
uniform bound along a deformation, nor an assertion of universal isolation.
No phase approximation or lower-order loneliness theorem is used.
-/

namespace LRC.PeriodReflection

/-- Exact next-return reflection data, valid for real times and readings. -/
theorem next_return_data {ι : Type*} (S : Finset ι) (d : ι → ℝ)
    (E : ι → ℤ) {H t : ℝ} (hH : 0 < H) (ht : 0 < t)
    (hE : ∀ i ∈ S, (E i : ℝ) = d i * H) :
    ∃ lam : ℝ, 0 < lam ∧ lam * t ≤ H ∧
      ∀ i ∈ S,
        (((⌊t / H⌋ + 1) * E i : ℤ) : ℝ) = (lam + 1) * d i * t := by
  let m : ℤ := ⌊t / H⌋
  have hlo : (m : ℝ) * H ≤ t := by
    exact (le_div_iff₀ hH).mp (Int.floor_le (t / H))
  have hhi : t < ((m : ℝ) + 1) * H := by
    exact (div_lt_iff₀ hH).mp (Int.lt_floor_add_one (t / H))
  let lam : ℝ := (((m : ℝ) + 1) * H - t) / t
  have hlam : 0 < lam := div_pos (sub_pos.mpr hhi) ht
  have heq : lam * t = ((m : ℝ) + 1) * H - t := by
    dsimp [lam]
    exact div_mul_cancel₀ _ ht.ne'
  refine ⟨lam, hlam, ?_, ?_⟩
  · rw [heq]
    linarith
  · intro i hi
    change (((m + 1) * E i : ℤ) : ℝ) = _
    push_cast
    rw [hE i hi]
    nlinarith [congrArg (fun x : ℝ => d i * x) heq]

/-- A common return constructs a bounded set of replacement labels from an
incoming window. The earlier-feasibility hypothesis is kept in its ORIGINAL
labels, rather than silently transferred to period-reduced labels.

The replacement window is valid on a right neighbourhood; the period bound
on the displayed instant and labels is at the current arrangement only. -/
theorem replacement_with_period_labels {ι : Type*}
    (S : Finset ι) (hS : S.Nonempty) (d v : ι → ℝ) (q E : ι → ℤ)
    {H t delta : ℝ} (hH : 0 < H) (ht : 0 < t) (hdelta : 0 < delta)
    (hd : ∀ i ∈ S, 0 < d i)
    (hE : ∀ i ∈ S, (E i : ℝ) = d i * H)
    (hband : ∀ i ∈ S, (q i : ℝ) + 1/8 ≤ d i * t ∧ d i * t ≤ q i + 7/8)
    (hleft : ∀ i ∈ S, ∀ j ∈ S,
      ((q i : ℝ) + 1/8) * (d j - delta * v j) ≤
        ((q j : ℝ) + 7/8) * (d i - delta * v i)) :
    ∃ p : ι → ℤ,
      (∀ i ∈ S, p i = (⌊t / H⌋ + 1) * E i - q i - 1) ∧
      (∀ i ∈ S, 0 ≤ p i ∧ p i < E i) ∧
      (∃ u : ℝ, 0 < u ∧ u ≤ H ∧ ∀ i ∈ S,
        (p i : ℝ) + 1/8 ≤ d i * u ∧ d i * u ≤ p i + 7/8) ∧
      ∃ e : ℝ, 0 < e ∧ ∀ h : ℝ, 0 ≤ h → h ≤ e →
        ∃ u : ℝ, 0 < u ∧ ∀ i ∈ S,
          (p i : ℝ) + 1/8 ≤ (d i + h * v i) * u ∧
            (d i + h * v i) * u ≤ p i + 7/8 := by
  obtain ⟨lam, hlam, hbound, hP⟩ := next_return_data S d E hH ht hE
  let P : ι → ℤ := fun i => (⌊t / H⌋ + 1) * E i
  let p : ι → ℤ := fun i => P i - q i - 1
  have hpband : ∀ i ∈ S,
      (p i : ℝ) + 1/8 ≤ d i * (lam * t) ∧
        d i * (lam * t) ≤ p i + 7/8 := by
    intro i hi
    exact PinchReflection.reflected_band (hP i hi) (hband i hi).1 (hband i hi).2
  refine ⟨p, fun _ _ => rfl, ?_, ⟨lam * t, mul_pos hlam ht, hbound, hpband⟩, ?_⟩
  · intro i hi
    have hb := hpband i hi
    have hpos := mul_pos (hd i hi) (mul_pos hlam ht)
    have htop : d i * (lam * t) ≤ (E i : ℝ) := by
      rw [hE i hi]
      exact mul_le_mul_of_nonneg_left hbound (hd i hi).le
    constructor
    · by_contra hn
      have hn' : (p i : ℝ) ≤ -1 := by exact_mod_cast (show p i ≤ -1 by omega)
      linarith [hb.2]
    · have : (p i : ℝ) < (E i : ℝ) := by linarith [hb.1]
      exact_mod_cast this
  · exact PinchReflection.reflected_right_windows S hS d v q P
      hd ht hlam hdelta hP hband hleft

end LRC.PeriodReflection
