import Mathlib
import Fresh.Framework
import Fresh.Localisation

/-!
# Three movers: a common clear instant in a long enough interval

Written 2026-10-22.  New file.  The instants of `[l, r]` where `distInt (d t) < 1/8` lie in at most `d (r - l) + 5/4` open intervals of length
`1/(4 d)`, so they have measure at most `(r - l)/4 + 5/(16 d)`.  Three such sets cannot cover `[l, r]` when `r - l > 15/(4 d_min)`; in
particular `r - l ≥ 4/d_min` leaves a common clear instant.  Grades: [L].  The argument is a measure bound on a finite union of intervals
(the substrate is the length of an interval), so it is [PROVISIONAL: counting tool] in the project's sense.
-/

open Classical MeasureTheory

namespace Fresh.OneMover

open Fresh

theorem blocked_measure {d l r : ℝ} (hd : 0 < d) :
    volume {t : ℝ | t ∈ Set.Icc l r ∧ distInt (d * t) < 1 / 8} ≤ ENNReal.ofReal ((r - l) / 4 + 5 / (16 * d)) := by
  by_cases hlr : l ≤ r
  swap
  · have : {t : ℝ | t ∈ Set.Icc l r ∧ distInt (d * t) < 1 / 8} = ∅ := by
      ext t; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro ⟨h1, h2⟩; linarith
    rw [this]; simp
  set N1 : ℤ := ⌈d * l - 1 / 8⌉ with hN1
  set N2 : ℤ := ⌊d * r + 1 / 8⌋ with hN2
  have hsub : {t : ℝ | t ∈ Set.Icc l r ∧ distInt (d * t) < 1 / 8} ⊆
      ⋃ n ∈ Finset.Icc N1 N2, Set.Ioo (((n : ℝ) - 1 / 8) / d) (((n : ℝ) + 1 / 8) / d) := by
    rintro t ⟨⟨hl, hr⟩, hdist⟩
    set n : ℤ := round (d * t) with hn
    have habs : |d * t - n| < 1 / 8 := by
      have : distInt (d * t) = |d * t - n| := rfl
      rw [← this]; exact hdist
    rw [abs_lt] at habs
    obtain ⟨ha1, ha2⟩ := habs
    simp only [Set.mem_iUnion, Finset.mem_Icc, Set.mem_Ioo]
    refine ⟨n, ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hN1]; apply Int.ceil_le.2; have := mul_le_mul_of_nonneg_left hl hd.le; linarith
    · rw [hN2]; apply Int.le_floor.2; have := mul_le_mul_of_nonneg_left hr hd.le; linarith
    · rw [div_lt_iff₀ hd]; linarith
    · rw [lt_div_iff₀ hd]; linarith
  refine (measure_mono hsub).trans ?_
  refine (measure_biUnion_finset_le _ _).trans ?_
  have hlen : ∀ n : ℤ, volume (Set.Ioo (((n : ℝ) - 1 / 8) / d) (((n : ℝ) + 1 / 8) / d)) = ENNReal.ofReal (1 / (4 * d)) := by
    intro n
    rw [Real.volume_Ioo]; congr 1; field_simp; ring
  simp_rw [hlen]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.Icc N1 N2).card : ℝ) ≤ d * (r - l) + 5 / 4 := by
    rw [Int.card_Icc]
    have h1 : (N2 : ℝ) ≤ d * r + 1 / 8 := Int.floor_le _
    have h2 : d * l - 1 / 8 ≤ (N1 : ℝ) := Int.le_ceil _
    have hpos : 0 ≤ d * (r - l) + 5 / 4 := by nlinarith
    by_cases hneg : N2 + 1 - N1 ≤ 0
    · rw [Int.toNat_of_nonpos hneg]; simpa using hpos
    · push Not at hneg
      have : (((N2 + 1 - N1).toNat : ℕ) : ℝ) = ((N2 + 1 - N1 : ℤ) : ℝ) := by
        have := Int.toNat_of_nonneg hneg.le
        exact_mod_cast this
      rw [this]; push_cast; nlinarith
  calc ((Finset.Icc N1 N2).card : ENNReal) * ENNReal.ofReal (1 / (4 * d))
      = ENNReal.ofReal (((Finset.Icc N1 N2).card : ℝ) * (1 / (4 * d))) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((r - l) / 4 + 5 / (16 * d)) := by
        apply ENNReal.ofReal_le_ofReal
        have : (d * (r - l) + 5 / 4) * (1 / (4 * d)) = (r - l) / 4 + 5 / (16 * d) := by field_simp; ring
        rw [← this]
        exact mul_le_mul_of_nonneg_right hcard (by positivity)

#print axioms blocked_measure

/-- Three movers `d1 ≤ d2, d3`: an interval of length `4/d1` contains a common clear instant. -/
theorem three_clear_in {d1 d2 d3 l r : ℝ} (h1 : 0 < d1) (h12 : d1 ≤ d2) (h13 : d1 ≤ d3) (hw : l + 4 / d1 ≤ r) :
    ∃ t, l ≤ t ∧ t ≤ r ∧ (1 / 8 : ℝ) ≤ distInt (d1 * t) ∧ (1 / 8 : ℝ) ≤ distInt (d2 * t) ∧ (1 / 8 : ℝ) ≤ distInt (d3 * t) := by
  have h2 : 0 < d2 := lt_of_lt_of_le h1 h12
  have h3 : 0 < d3 := lt_of_lt_of_le h1 h13
  by_contra hno
  push Not at hno
  set B : ℝ → Set ℝ := fun d => {t : ℝ | t ∈ Set.Icc l r ∧ distInt (d * t) < 1 / 8} with hB
  have hcover : Set.Icc l r ⊆ B d1 ∪ B d2 ∪ B d3 := by
    intro t ht
    have := hno t ht.1 ht.2
    by_cases c1 : (1 / 8 : ℝ) ≤ distInt (d1 * t)
    · by_cases c2 : (1 / 8 : ℝ) ≤ distInt (d2 * t)
      · have c3 := this c1 c2
        exact Or.inr ⟨ht, c3⟩
      · exact Or.inl (Or.inr ⟨ht, not_le.1 c2⟩)
    · exact Or.inl (Or.inl ⟨ht, not_le.1 c1⟩)
  have hvol : volume (Set.Icc l r) ≤ volume (B d1) + volume (B d2) + volume (B d3) := by
    refine (measure_mono hcover).trans ?_
    refine (measure_union_le _ _).trans ?_
    gcongr
    exact measure_union_le _ _
  have hb1 := blocked_measure (l := l) (r := r) h1
  have hb2 := blocked_measure (l := l) (r := r) h2
  have hb3 := blocked_measure (l := l) (r := r) h3
  have hle : r - l ≤ ((r - l) / 4 + 5 / (16 * d1)) + ((r - l) / 4 + 5 / (16 * d2)) + ((r - l) / 4 + 5 / (16 * d3)) := by
    have hrl : 0 ≤ r - l := by
      have : 0 ≤ 4 / d1 := by positivity
      linarith
    have hp1 : 0 ≤ (r - l) / 4 + 5 / (16 * d1) := by positivity
    have hp2 : 0 ≤ (r - l) / 4 + 5 / (16 * d2) := by positivity
    have hp3 : 0 ≤ (r - l) / 4 + 5 / (16 * d3) := by positivity
    have hall : ENNReal.ofReal (r - l) ≤ ENNReal.ofReal (((r - l) / 4 + 5 / (16 * d1)) + ((r - l) / 4 + 5 / (16 * d2)) + ((r - l) / 4 + 5 / (16 * d3))) := by
      rw [ENNReal.ofReal_add (by positivity) hp3, ENNReal.ofReal_add hp1 hp2]
      calc ENNReal.ofReal (r - l) = volume (Set.Icc l r) := by rw [Real.volume_Icc]
        _ ≤ _ := hvol
        _ ≤ _ := by gcongr
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hall
  have e2 : 5 / (16 * d2) ≤ 5 / (16 * d1) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity); nlinarith
  have e3 : 5 / (16 * d3) ≤ 5 / (16 * d1) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity); nlinarith
  have q1 : 5 / (16 * d1) = (5 / 16) * (1 / d1) := by field_simp
  have q4 : 4 / d1 = 4 * (1 / d1) := by ring
  have hu : 0 < 1 / d1 := by positivity
  rw [q4] at hw
  linarith

#print axioms three_clear_in


/-- Three movers all at least `D`: an interval of length `4/D` contains a common clear instant. -/
theorem three_clear_in_all {D d1 d2 d3 l r : ℝ} (hD : 0 < D) (h1 : D ≤ d1) (h2 : D ≤ d2) (h3 : D ≤ d3) (hw : l + 4 / D ≤ r) :
    ∃ t, l ≤ t ∧ t ≤ r ∧ (1 / 8 : ℝ) ≤ distInt (d1 * t) ∧ (1 / 8 : ℝ) ≤ distInt (d2 * t) ∧ (1 / 8 : ℝ) ≤ distInt (d3 * t) := by
  have hd1 : 0 < d1 := lt_of_lt_of_le hD h1
  have hd2 : 0 < d2 := lt_of_lt_of_le hD h2
  have hd3 : 0 < d3 := lt_of_lt_of_le hD h3
  by_contra hno
  push Not at hno
  set B : ℝ → Set ℝ := fun d => {t : ℝ | t ∈ Set.Icc l r ∧ distInt (d * t) < 1 / 8} with hB
  have hcover : Set.Icc l r ⊆ B d1 ∪ B d2 ∪ B d3 := by
    intro t ht
    have := hno t ht.1 ht.2
    by_cases c1 : (1 / 8 : ℝ) ≤ distInt (d1 * t)
    · by_cases c2 : (1 / 8 : ℝ) ≤ distInt (d2 * t)
      · have c3 := this c1 c2
        exact Or.inr ⟨ht, c3⟩
      · exact Or.inl (Or.inr ⟨ht, not_le.1 c2⟩)
    · exact Or.inl (Or.inl ⟨ht, not_le.1 c1⟩)
  have hvol : volume (Set.Icc l r) ≤ volume (B d1) + volume (B d2) + volume (B d3) := by
    refine (measure_mono hcover).trans ?_
    refine (measure_union_le _ _).trans ?_
    gcongr
    exact measure_union_le _ _
  have hb1 := blocked_measure (l := l) (r := r) hd1
  have hb2 := blocked_measure (l := l) (r := r) hd2
  have hb3 := blocked_measure (l := l) (r := r) hd3
  have hle : r - l ≤ ((r - l) / 4 + 5 / (16 * d1)) + ((r - l) / 4 + 5 / (16 * d2)) + ((r - l) / 4 + 5 / (16 * d3)) := by
    have hrl : 0 ≤ r - l := by
      have : 0 ≤ 4 / D := by positivity
      linarith
    have hp1 : 0 ≤ (r - l) / 4 + 5 / (16 * d1) := by positivity
    have hp2 : 0 ≤ (r - l) / 4 + 5 / (16 * d2) := by positivity
    have hp3 : 0 ≤ (r - l) / 4 + 5 / (16 * d3) := by positivity
    have hall : ENNReal.ofReal (r - l) ≤ ENNReal.ofReal (((r - l) / 4 + 5 / (16 * d1)) + ((r - l) / 4 + 5 / (16 * d2)) + ((r - l) / 4 + 5 / (16 * d3))) := by
      rw [ENNReal.ofReal_add (by positivity) hp3, ENNReal.ofReal_add hp1 hp2]
      calc ENNReal.ofReal (r - l) = volume (Set.Icc l r) := by rw [Real.volume_Icc]
        _ ≤ _ := hvol
        _ ≤ _ := by gcongr
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hall
  have e1 : 5 / (16 * d1) ≤ 5 / (16 * D) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity); nlinarith
  have e2 : 5 / (16 * d2) ≤ 5 / (16 * D) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity); nlinarith
  have e3 : 5 / (16 * d3) ≤ 5 / (16 * D) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity); nlinarith
  have q1 : 5 / (16 * D) = (5 / 16) * (1 / D) := by field_simp
  have q4 : 4 / D = 4 * (1 / D) := by ring
  have hu : 0 < 1 / D := by positivity
  rw [q4] at hw
  linarith

#print axioms three_clear_in_all

end Fresh.OneMover
