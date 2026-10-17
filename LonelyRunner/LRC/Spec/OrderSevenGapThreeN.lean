import LonelyRunner.LRC.Spec.OrderSevenSplitN
import LonelyRunner.LRC.ConstructionN.Band

/-!
# Order seven: a uniform gap for three runners (union bound)

At most three positive whole numbers: every closed interval of length `G = 5 Σ 1/d` contains an instant at which all
of them read inside `[1/7, 6/7]`.  Each speed `d` is out of band on at most `d G + 2` open intervals of length
`2/(7d)`, total `≤ 2G/7 + 4/(7d)`; summed over three speeds this is `≤ 6G/7 + (4/5)(G/7) < G`.  Four speeds would give
`8/7 > 1`, which is why the bound stops at three.

`gap_three : GapProp F (5 Σ 1/d) 0`.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.O7Gap3

open MeasureTheory LRC.MirrorCentre LRC.O7Split

/-- The out-of-band instants of one speed inside `[a, a + G]` lie in `dG + 2` open intervals of length `2/(7d)`. -/
theorem bad_subset {d : ℕ} (hd : 0 < d) (a G : ℝ) :
    {s | s ∈ Set.Icc a (a + G) ∧ circDist ((d : ℝ) * s) < 1 / 7} ⊆
      ⋃ m ∈ Finset.Icc ⌈(d : ℝ) * a - 1 / 7⌉ ⌊(d : ℝ) * (a + G) + 1 / 7⌋,
        Set.Ioo (((m : ℝ) - 1 / 7) / d) (((m : ℝ) + 1 / 7) / d) := by
  intro s ⟨hs, hc⟩
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨m, hm⟩ := ConstructionN.circDist_eq_abs_sub_some_int ((d : ℝ) * s)
  rw [hm] at hc
  have h1 : (m : ℝ) - 1 / 7 < d * s := by have := neg_abs_le ((d : ℝ) * s - m); linarith
  have h2 : (d : ℝ) * s < m + 1 / 7 := by have := le_abs_self ((d : ℝ) * s - m); linarith
  simp only [Set.mem_iUnion, Finset.mem_Icc]
  refine ⟨m, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Int.ceil_le]; nlinarith [hs.1]
  · rw [Int.le_floor]; nlinarith [hs.2]
  · rw [div_lt_iff₀ hd']; linarith
  · rw [lt_div_iff₀ hd']; linarith

theorem bad_measure {d : ℕ} (hd : 0 < d) (a G : ℝ) (hG : 0 ≤ G) :
    volume {s | s ∈ Set.Icc a (a + G) ∧ circDist ((d : ℝ) * s) < 1 / 7} ≤
      ENNReal.ofReal (2 * G / 7 + 4 / (7 * d)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  refine le_trans (measure_mono (bad_subset hd a G)) (le_trans (measure_biUnion_finset_le _ _) ?_)
  simp only [Real.volume_Ioo]
  have hlen : ∀ m : ℤ, ((m : ℝ) + 1 / 7) / d - ((m : ℝ) - 1 / 7) / d = 2 / (7 * d) := by
    intro m; field_simp; ring
  simp only [hlen, Finset.sum_const, nsmul_eq_mul]
  set lo := ⌈(d : ℝ) * a - 1 / 7⌉
  set hi := ⌊(d : ℝ) * (a + G) + 1 / 7⌋
  have hcard : ((Finset.Icc lo hi).card : ℝ) ≤ d * G + 2 := by
    rw [Int.card_Icc]
    have hl : (d : ℝ) * a - 1 / 7 ≤ lo := Int.le_ceil _
    have hh : (hi : ℝ) ≤ d * (a + G) + 1 / 7 := Int.floor_le _
    rcases le_or_gt lo (hi + 1) with h | h
    · have : ((hi + 1 - lo).toNat : ℝ) = (hi : ℝ) + 1 - lo := by
        rw [show ((hi + 1 - lo).toNat : ℝ) = (((hi + 1 - lo).toNat : ℤ) : ℝ) by norm_cast,
          Int.toNat_of_nonneg (by omega)]; push_cast; ring
      rw [this]; nlinarith
    · rw [show (hi + 1 - lo).toNat = 0 by omega]; push_cast; nlinarith
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc ((Finset.Icc lo hi).card : ℝ) * (2 / (7 * d)) ≤ (d * G + 2) * (2 / (7 * d)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 2 * G / 7 + 4 / (7 * d) := by field_simp; ring

/-- **Uniform gap for at most three runners.** -/
theorem gap_three {F : Finset ℕ} (hpos : ∀ d ∈ F, 0 < d) (hcard : F.card ≤ 3) :
    GapProp F (5 * ∑ d ∈ F, (1 : ℝ) / d) 0 := by
  intro a
  set G := 5 * ∑ d ∈ F, (1 : ℝ) / d with hGdef
  have hG0 : 0 ≤ G := by
    rw [hGdef]; exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun d _ => by positivity))
  by_contra hno
  simp only [not_exists, not_and] at hno
  -- every instant of `[a, a + G]` is out of band for some speed
  have hcover : Set.Icc a (a + G) ⊆
      ⋃ d ∈ F, {s | s ∈ Set.Icc a (a + G) ∧ circDist ((d : ℝ) * s) < 1 / 7} := by
    intro s hs
    have h := hno s hs.1 (by linarith [hs.2])
    simp only [InBandOn, not_forall, not_le] at h
    obtain ⟨t, ht, d, hd, h7⟩ := h
    have hts : t = s := le_antisymm (by linarith [ht.2]) ht.1
    subst hts
    simp only [Set.mem_iUnion]; exact ⟨d, hd, hs, h7⟩
  have hmeas := le_trans (measure_mono (μ := (volume : Measure ℝ)) hcover) (measure_biUnion_finset_le _ _)
  rw [Real.volume_Icc, show a + G - a = G by ring] at hmeas
  have hsum : ∑ d ∈ F, volume {s | s ∈ Set.Icc a (a + G) ∧ circDist ((d : ℝ) * s) < 1 / 7} ≤
      ∑ d ∈ F, ENNReal.ofReal (2 * G / 7 + 4 / (7 * d)) :=
    Finset.sum_le_sum (fun d hd => bad_measure (hpos d hd) a G hG0)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun d hd => by have := hpos d hd; positivity)] at hsum
  have htot := le_trans hmeas hsum
  rw [ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg (fun d hd => by have := hpos d hd; positivity))] at htot
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at htot
  have hS : ∑ d ∈ F, (4 : ℝ) / (7 * d) = 4 / 35 * G := by
    rw [hGdef, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun d hd => by have := hpos d hd; field_simp; ring)
  rw [hS] at htot
  have hc3 : (F.card : ℝ) ≤ 3 := by exact_mod_cast hcard
  have hGpos : 0 < G := by
    rcases F.eq_empty_or_nonempty with he | hne
    · exact absurd (fun t _ d hd => by simp [he] at hd) (hno a le_rfl (by linarith))
    · obtain ⟨d, hd⟩ := hne
      rw [hGdef]
      exact mul_pos (by norm_num) (Finset.sum_pos (fun d hd => by have := hpos d hd; positivity) ⟨d, hd⟩)
  nlinarith

/-! ### The union bound with a window -/

/-- Window starts in `[a, a + L]` whose window `[s, s + w]` meets an out-of-band instant of `d` lie in `dL + dw + 2`
open intervals of length `2/(7d) + w`. -/
theorem bad_subset_w {d : ℕ} (hd : 0 < d) (a L w : ℝ) (hw : 0 ≤ w) :
    {s | s ∈ Set.Icc a (a + L) ∧ ∃ τ ∈ Set.Icc s (s + w), circDist ((d : ℝ) * τ) < 1 / 7} ⊆
      ⋃ m ∈ Finset.Icc ⌈(d : ℝ) * a - 1 / 7⌉ ⌊(d : ℝ) * (a + L + w) + 1 / 7⌋,
        Set.Ioo (((m : ℝ) - 1 / 7) / d - w) (((m : ℝ) + 1 / 7) / d) := by
  intro s ⟨hs, τ, hτ, hc⟩
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨m, hm⟩ := ConstructionN.circDist_eq_abs_sub_some_int ((d : ℝ) * τ)
  rw [hm] at hc
  have h1 : (m : ℝ) - 1 / 7 < d * τ := by have := neg_abs_le ((d : ℝ) * τ - m); linarith
  have h2 : (d : ℝ) * τ < m + 1 / 7 := by have := le_abs_self ((d : ℝ) * τ - m); linarith
  simp only [Set.mem_iUnion, Finset.mem_Icc]
  refine ⟨m, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Int.ceil_le]; nlinarith [hs.1, hτ.1]
  · rw [Int.le_floor]; nlinarith [hs.2, hτ.2]
  · have : ((m : ℝ) - 1 / 7) / d < τ := by rw [div_lt_iff₀ hd']; linarith
    linarith [hτ.2]
  · have : τ < ((m : ℝ) + 1 / 7) / d := by rw [lt_div_iff₀ hd']; linarith
    linarith [hτ.1]

theorem bad_measure_w {d : ℕ} (hd : 0 < d) (a L w : ℝ) (hL : 0 ≤ L) (_hw : 0 ≤ w) :
    volume {s | s ∈ Set.Icc a (a + L) ∧ ∃ τ ∈ Set.Icc s (s + w), circDist ((d : ℝ) * τ) < 1 / 7} ≤
      ENNReal.ofReal (2 * L / 7 + d * L * w + 2 * w / 7 + d * w ^ 2 + 4 / (7 * d) + 2 * w) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  refine le_trans (measure_mono (bad_subset_w hd a L w hw)) (le_trans (measure_biUnion_finset_le _ _) ?_)
  simp only [Real.volume_Ioo]
  have hlen : ∀ m : ℤ, ((m : ℝ) + 1 / 7) / d - (((m : ℝ) - 1 / 7) / d - w) = 2 / (7 * d) + w := by
    intro m; field_simp; ring
  simp only [hlen, Finset.sum_const, nsmul_eq_mul]
  set lo := ⌈(d : ℝ) * a - 1 / 7⌉
  set hi := ⌊(d : ℝ) * (a + L + w) + 1 / 7⌋
  have hcard : ((Finset.Icc lo hi).card : ℝ) ≤ d * L + d * w + 2 := by
    rw [Int.card_Icc]
    have hl : (d : ℝ) * a - 1 / 7 ≤ lo := Int.le_ceil _
    have hh : (hi : ℝ) ≤ d * (a + L + w) + 1 / 7 := Int.floor_le _
    rcases le_or_gt lo (hi + 1) with h | h
    · have : ((hi + 1 - lo).toNat : ℝ) = (hi : ℝ) + 1 - lo := by
        rw [show ((hi + 1 - lo).toNat : ℝ) = (((hi + 1 - lo).toNat : ℤ) : ℝ) by norm_cast,
          Int.toNat_of_nonneg (by omega)]; push_cast; ring
      rw [this]; nlinarith
    · rw [show (hi + 1 - lo).toNat = 0 by omega]; push_cast; nlinarith
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc ((Finset.Icc lo hi).card : ℝ) * (2 / (7 * d) + w) ≤ (d * L + d * w + 2) * (2 / (7 * d) + w) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 2 * L / 7 + d * L * w + 2 * w / 7 + d * w ^ 2 + 4 / (7 * d) + 2 * w := by field_simp; ring

/-- **Union bound with a window.**  If the bad measures sum to less than `L`, every interval of length `L + w` contains
a window of length `w` for `F`. -/
theorem gap_union {F : Finset ℕ} (hpos : ∀ d ∈ F, 0 < d) {L w : ℝ} (hL : 0 ≤ L) (hw : 0 ≤ w)
    (hcond : ∑ d ∈ F, (2 * L / 7 + d * L * w + 2 * w / 7 + d * w ^ 2 + 4 / (7 * d) + 2 * w) < L) :
    GapProp F (L + w) w := by
  intro a
  by_contra hno
  simp only [not_exists, not_and] at hno
  have hcover : Set.Icc a (a + L) ⊆
      ⋃ d ∈ F, {s | s ∈ Set.Icc a (a + L) ∧ ∃ τ ∈ Set.Icc s (s + w), circDist ((d : ℝ) * τ) < 1 / 7} := by
    intro s hs
    have h := hno s hs.1 (by linarith [hs.2])
    simp only [InBandOn, not_forall, not_le] at h
    obtain ⟨τ, hτ, d, hd, h7⟩ := h
    simp only [Set.mem_iUnion]; exact ⟨d, hd, hs, τ, hτ, h7⟩
  have hmeas := le_trans (measure_mono (μ := (volume : Measure ℝ)) hcover) (measure_biUnion_finset_le _ _)
  rw [Real.volume_Icc, show a + L - a = L by ring] at hmeas
  have hsum := Finset.sum_le_sum (fun d hd => bad_measure_w (hpos d hd) a L w hL hw)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun d hd => by have := hpos d hd; positivity)] at hsum
  have htot := le_trans hmeas hsum
  rw [ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg (fun d hd => by have := hpos d hd; positivity))] at htot
  linarith

end LRC.O7Gap3
