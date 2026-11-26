import Fresh.TranslatedSix

/-!
Rules 1–4, 8–18. A translated-six block below the unit reading.
The reference reading1 is exactly at the opening T=N+1/8.
[PROVISIONAL: counting tool] the ceiling chooses N so 1/8≤aT<1/8+a.
For 0<a≤1/8 this gives aT≤1/4. Whole laps jN are retained;
the six block phases lie in [j/8+1/8,j/8+1/4], j=0,…,5.
-/
namespace Fresh.TranslatedSix
open Fresh Fresh.Localisation

noncomputable def smallTime (a : ℝ) : ℝ :=
  (⌈1 / (8 * a) - 1 / 8⌉ : ℤ) + 1 / 8

theorem smallTime_spec {a : ℝ} (ha : 0 < a) (hb : a ≤ 1 / 8) :
    0 < smallTime a ∧ (1 / 8 : ℝ) ≤ a * smallTime a ∧
      a * smallTime a ≤ 1 / 4 := by
  have h1 := Int.le_ceil (1 / (8 * a) - 1 / 8)
  have h2 := Int.ceil_lt_add_one (1 / (8 * a) - 1 / 8)
  have he : a * (1 / (8 * a)) = 1 / 8 := by field_simp
  have hlo : 1 / 8 ≤ a * smallTime a := by
    unfold smallTime
    have := mul_le_mul_of_nonneg_left h1 ha.le
    nlinarith
  have hhi : a * smallTime a < 1 / 8 + a := by
    unfold smallTime
    have := mul_lt_mul_of_pos_left h2 ha
    nlinarith
  refine ⟨?_,hlo,by linarith⟩
  by_contra hn
  have : a * smallTime a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt hn)
  linarith

/-- Every whole lap from the translated block is retained explicitly. -/
theorem translated_six_small (a : ℝ) (ha : 0 < a) (hb : a ≤ 1 / 8) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ train a, (1 / 8 : ℝ) ≤ distInt (d * t) := by
  obtain ⟨ht,hlo,hhi⟩ := smallTime_spec ha hb
  let N : ℤ := ⌈1 / (8 * a) - 1 / 8⌉
  have he : smallTime a = (N : ℝ) + 1 / 8 := rfl
  refine ⟨smallTime a,ht,fun d hd => ?_⟩
  simp only [train,Finset.mem_insert,Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_of_window N <;> rw [one_mul,he] <;> linarith
  · apply clear_of_window (0 : ℤ) <;> norm_num <;> linarith
  · apply clear_of_window N <;> nlinarith [he]
  · apply clear_of_window (2*N) <;> push_cast <;> nlinarith [he]
  · apply clear_of_window (3*N) <;> push_cast <;> nlinarith [he]
  · apply clear_of_window (4*N) <;> push_cast <;> nlinarith [he]
  · apply clear_of_window (5*N) <;> push_cast <;> nlinarith [he]

-- STANDING: DEFINITION
def TranslatedSixSmallClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ s a : ℝ, 0 < s ∧ 0 < a ∧ a ≤ 1 / 8 ∧
    ∀ d ∈ disparitySet v k, ∃ q ∈ train a, d = s * q

theorem translatedSixSmall_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : TranslatedSixSmallClass v k) : Isolation v k := by
  obtain ⟨s,a,hs,ha,hb,hmem⟩ := h
  obtain ⟨t,ht,hclear⟩ := translated_six_small a ha hb
  refine ⟨t/s,by positivity,?_⟩
  rw [isolatedAt_iff]
  intro d hd
  obtain ⟨q,hq,rfl⟩ := hmem d hd
  have he : s*q*(t/s)=q*t := by field_simp
  rw [he]
  exact hclear q hq

#print axioms smallTime_spec
#print axioms translated_six_small
#print axioms translatedSixSmall_isolation
end Fresh.TranslatedSix
