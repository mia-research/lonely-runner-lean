import Fresh.Cascade

namespace Fresh.Harmonic

open Fresh.Cascade

def InWindows (t : ℝ) : Prop :=
  t ∈ Set.Icc (1/8) (7/8) ∨ t ∈ Set.Icc (9/8) (15/8)

def Buffered (t e : ℝ) : Prop :=
  t ∈ Set.Icc (1/8+e) (7/8-e) ∨ t ∈ Set.Icc (9/8+e) (15/8-e)

theorem phase_distance_le (x y : ℝ) : distInt x ≤ distInt y + |x-y| := by
  calc
    distInt x ≤ |x - (round y : ℝ)| := distInt_le _ _
    _ = |(x-y)+(y-(round y : ℝ))| := by ring_nf
    _ ≤ |x-y| + distInt y := abs_add_le _ _
    _ = distInt y + |x-y| := add_comm _ _

private theorem windows_of_close {t s e : ℝ} (h : Buffered t e)
    (hs : |s-t| ≤ e) : InWindows s := by
  obtain ⟨hl,hu⟩ := abs_le.mp hs
  rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact Or.inl ⟨by linarith, by linarith⟩
  · exact Or.inr ⟨by linarith, by linarith⟩

/-- A phase witness with a margin can be aligned with the common fast frequency. -/
theorem lift_with_margin {n : ℕ} {t e M B frequency φ margin : ℝ}
    (slow : Finset ℝ) (p : Fin n → ℕ) (b : Fin n → ℝ)
    (hfrequency : 0 < frequency) (hM : 1 ≤ M) (he : M/(2*frequency) ≤ e)
    (hB : B/(2*frequency) ≤ margin)
    (hw : Buffered t e)
    (hs : ∀ v ∈ slow, |v| ≤ M ∧ 1/8+e ≤ distInt (v*t))
    (hb : ∀ i, |b i| ≤ B)
    (hf : ∀ i, 1/8 + margin ≤ distInt ((p i : ℝ)*φ+b i*t)) :
    ∃ s, InWindows s ∧ |s-t| ≤ e ∧ (∀ v ∈ slow, (1/8 : ℝ) ≤ distInt (v*s)) ∧
      ∀ i, (1/8 : ℝ) ≤ distInt (((p i : ℝ)*frequency+b i)*s) := by
  let k : ℤ := round (frequency*t-φ)
  let s := ((k : ℝ)+φ)/frequency
  have hscale : frequency*s = (k : ℝ)+φ := by dsimp [s]; field_simp
  have hnear : |s-t| ≤ 1/(2*frequency) := by
    have hr : |frequency*t-φ-(k : ℝ)| ≤ 1/2 := abs_sub_round _
    have hh : frequency*(s-t) = -(frequency*t-φ-(k : ℝ)) := by linarith only [hscale]
    rw [show (1:ℝ)/(2*frequency) = (1/2)/frequency by ring]
    apply (le_div_iff₀ hfrequency).2
    rw [mul_comm, ← abs_of_pos hfrequency, ← abs_mul, hh, abs_neg]
    exact hr
  have hnear' : |s-t| ≤ e := hnear.trans
    ((div_le_div_of_nonneg_right hM (by positivity : 0 ≤ 2*frequency)).trans he)
  refine ⟨s, windows_of_close hw hnear', hnear', ?_, ?_⟩
  · intro v hv
    obtain ⟨hvM,hvc⟩ := hs v hv
    have herr : |v*t-v*s| ≤ e := by
      rw [show v*t-v*s = -(v*(s-t)) by ring, abs_neg, abs_mul]
      exact (mul_le_mul hvM hnear (abs_nonneg _) (by linarith)).trans
        (by rwa [mul_one_div])
    linarith [phase_distance_le (v*t) (v*s)]
  · intro i
    have htranslate : ((p i : ℝ)*frequency+b i)*s =
        ((p i : ℝ)*φ+b i*s) + (((p i : ℤ)*k : ℤ) : ℝ) := by
      push_cast
      linear_combination (p i : ℝ)*hscale
    rw [htranslate, distInt_add_int]
    have herr : |((p i : ℝ)*φ+b i*t)-((p i : ℝ)*φ+b i*s)| ≤ margin := by
      rw [show (p i : ℝ)*φ+b i*t-((p i : ℝ)*φ+b i*s) = -(b i*(s-t)) by ring,
        abs_neg, abs_mul]
      exact (mul_le_mul (hb i) hnear (abs_nonneg _) ((abs_nonneg _).trans (hb i))).trans
        (by rwa [mul_one_div])
    linarith [phase_distance_le ((p i : ℝ)*φ+b i*t) ((p i : ℝ)*φ+b i*s), hf i]

theorem lift {n : ℕ} {t e M B frequency φ : ℝ}
    (slow : Finset ℝ) (p : Fin n → ℕ) (b : Fin n → ℝ)
    (hfrequency : 0 < frequency) (hM : 1 ≤ M) (he : M/(2*frequency) ≤ e)
    (hB : B/(2*frequency) ≤ 1/200)
    (hw : Buffered t e)
    (hs : ∀ v ∈ slow, |v| ≤ M ∧ 1/8+e ≤ distInt (v*t))
    (hb : ∀ i, |b i| ≤ B)
    (hf : ∀ i, (13/100 : ℝ) ≤ distInt ((p i : ℝ)*φ+b i*t)) :
    ∃ s, InWindows s ∧ |s-t| ≤ e ∧ (∀ v ∈ slow, (1/8 : ℝ) ≤ distInt (v*s)) ∧
      ∀ i, (1/8 : ℝ) ≤ distInt (((p i : ℝ)*frequency+b i)*s) := by
  apply lift_with_margin (margin := 1/200) slow p b hfrequency hM he hB hw hs hb
  intro i
  convert hf i using 1
  norm_num

#print axioms lift
end Fresh.Harmonic
