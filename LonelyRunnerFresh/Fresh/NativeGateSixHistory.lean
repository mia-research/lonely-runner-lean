import Fresh.NativeAffineMoveFaces

/-! Past move faces forcing clearance at the lap-8 exit of reading 6.
The two branches use different historical bounds. No phase at the proposed
landing is an assumption. -/

namespace Fresh.NativeGateSixHistory

open Fresh Fresh.Cascade Fresh.Localisation

/-- Every actual move between named openings supplies the phase and
exit-order inequalities used by the history bounds. -/
theorem faces_of_move {ds : Finset ℝ} (hpos : ∀ r ∈ ds, 0 < r)
    {a b A B : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hm : IsMove ds (A / a) (B / b)) {r : ℝ} (hr : r ∈ ds) (j : ℤ)
    (hj : NativeEntryLabels.label (r * (A / a)) = j) :
    ((j : ℝ) - 1 / 8) * a < A * r ∧
    A * r ≤ ((j : ℝ) + 7 / 8) * a ∧
    ((j : ℝ) + 1 / 8) * b ≤ B * r := by
  have hphase := (NativeEntryLabels.entry_interval _ _ _).1
    ((NativeEntryLabels.entry_iff_label _ _ _).2 hj)
  rw [← mul_div_assoc, lt_div_iff₀ ha, div_le_iff₀ ha, mul_comm r A] at hphase
  have hnext := NativeOneReaderDeformation.move_passes_entry_opening hpos _ _ _ hm hr
  rw [hj, ← mul_div_assoc, le_div_iff₀ hb, mul_comm r B] at hnext
  exact ⟨hphase.1, hphase.2, hnext⟩

private theorem clear_at_65 {a d : ℝ} (ha : 0 < a) (j : ℤ)
    (hl : (8 * (j : ℝ) + 1) * a ≤ 65 * d)
    (hu : 65 * d ≤ (8 * (j : ℝ) + 7) * a) :
    (1 / 8 : ℝ) ≤ distInt (d * ((65 / 8) / a)) := by
  apply clear_of_window j
  · rw [← mul_div_assoc, le_div_iff₀ ha]
    linarith only [hl]
  · rw [← mul_div_assoc, div_le_iff₀ ha]
    linarith only [hu]

/-- History guards when reading 7 is clear on lap 12. -/
theorem lap_twelve_band {a b c d e f g : ℝ} (hf : 0 < f)
    (h1 : 7 * a ≤ f)
    (h2 : 47 * b ≤ 17 * g)
    (h3 : 7 * c ≤ 9 * b)
    (h4 : 31 * c ≤ 25 * e)
    (h5 : 7 * d ≤ 41 * a)
    (h6 : 15 * f ≤ 17 * e)
    (h7 : 63 * f ≤ 41 * g)
    (h8 : 15 * g ≤ 33 * c)
    (h9 : 31 * g ≤ 49 * f)
    (h10 : 9 * f ≤ 65 * a)
    (h11 : 33 * f ≤ 41 * d)
    (h12 : 17 * f ≤ 31 * b)
    (h13 : 33 * e ≤ 31 * f)
    (hbranch : 31 * g ≤ 57 * d ∨ 31 * e ≤ 33 * d)
    : LonelyAt ({a, b, c, d, e, f, g} : Finset ℝ) ((65 / 8) / f) := by
  classical
  intro r hr
  simp at hr
  rcases hr with h | h | h | h | h | h | h <;> subst r
  · apply clear_at_65 hf 1
    · norm_num
      linarith only [hf, h10]
    · norm_num
      linarith only [hf, h1]
  · apply clear_at_65 hf 4
    · norm_num
      linarith only [hf, h12]
    · norm_num
      linarith only [hf, h9, h2]
  · apply clear_at_65 hf 5
    · norm_num
      linarith only [hf, h8, h7]
    · rcases hbranch with h | h
      · norm_num
        linarith only [hf, h1, h5, h, h2, h3]
      · norm_num
        linarith only [hf, h1, h5, h, h4]
  · apply clear_at_65 hf 6
    · norm_num
      linarith only [hf, h11]
    · norm_num
      linarith only [hf, h1, h5]
  · apply clear_at_65 hf 7
    · norm_num
      linarith only [hf, h6]
    · norm_num
      linarith only [hf, h13]
  · apply clear_at_65 hf 8
    · norm_num
    · norm_num
      linarith only [hf]
  · apply clear_at_65 hf 12
    · norm_num
      linarith only [hf, h7]
    · norm_num
      linarith only [hf, h9]

#print axioms lap_twelve_band

/-- History guards when reading 7 is clear on lap 10. -/
theorem lap_ten_band {a b c d e f g : ℝ} (hf : 0 < f)
    (h1 : 7 * a ≤ f)
    (h2 : 15 * b ≤ 9 * d)
    (h3 : 39 * c ≤ 17 * g)
    (h4 : 47 * d ≤ 33 * f)
    (h5 : 7 * e ≤ 9 * d)
    (h6 : 15 * e ≤ 25 * c)
    (h7 : 23 * f ≤ 33 * d)
    (h8 : 63 * f ≤ 49 * g)
    (h9 : 23 * g ≤ 33 * e)
    (h10 : 9 * f ≤ 65 * a)
    (h11 : 9 * f ≤ 23 * b)
    : LonelyAt ({a, b, c, d, e, f, g} : Finset ℝ) ((65 / 8) / f) := by
  classical
  intro r hr
  simp at hr
  rcases hr with h | h | h | h | h | h | h <;> subst r
  · apply clear_at_65 hf 1
    · norm_num
      linarith only [hf, h10]
    · norm_num
      linarith only [hf, h1]
  · apply clear_at_65 hf 3
    · norm_num
      linarith only [hf, h11]
    · norm_num
      linarith only [hf, h4, h2]
  · apply clear_at_65 hf 4
    · norm_num
      linarith only [hf, h6, h9, h8]
    · norm_num
      linarith only [hf, h4, h5, h9, h3]
  · apply clear_at_65 hf 5
    · norm_num
      linarith only [hf, h7]
    · norm_num
      linarith only [hf, h4]
  · apply clear_at_65 hf 7
    · norm_num
      linarith only [hf, h9, h8]
    · norm_num
      linarith only [hf, h4, h5]
  · apply clear_at_65 hf 8
    · norm_num
    · norm_num
      linarith only [hf]
  · apply clear_at_65 hf 10
    · norm_num
      linarith only [hf, h8]
    · norm_num
      linarith only [hf, h4, h5, h9]

#print axioms lap_ten_band

#print axioms faces_of_move
#print axioms clear_at_65

end Fresh.NativeGateSixHistory
