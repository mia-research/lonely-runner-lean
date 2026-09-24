import LonelyRunner.LRC.Spec.ResonanceN

/-!
# The sharp-window criterion (P4)

2026-09-21.  The flank openings of `e` sit at spacing `1/e`, and the flank itself is at exactly
`1/n` there, so a window need only keep the **non-flank** disparities lonely.  Let

    L = { t : ‖d·t‖ ≥ 1/n for every non-flank d },   W = its largest interval.

`L`'s complement is a union of open intervals `((k − 1/n)/d, (k + 1/n)/d)`, so `L` is a union of
closed intervals with those endpoints and `W` is an exact finite computation.  When `W > 1/e`,
`LRC.FlankFinite.exists_lonely_flankOpening_of_gap` delivers a lonely opening.

`windowOK` is the decidable certificate for a candidate window: for each `d` the image
`[d·x, d·(x+w)]` must fit inside one band `[k + 1/n, k + 1 − 1/n]`.  Measured coverage at
`n = 5`: **15.3%** of all primitive card-4 sets, **23.3%** of the residue, and soundness checked
(no set the criterion claims actually fails).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.Window

open Flanks MomentIterationN LRC.SpecN LRC.FlankFinite

variable {n : ℕ} [Fact (2 ≤ n)]

/-- **The window check.**  For each `d ∈ L`, the image `[d·x, d·(x+w)]` must fit inside one band
`[k + 1/n, k + 1 − 1/n]`.  Decidable rational arithmetic. -/
def windowOK (n : ℕ) (L : List ℕ) (x w : ℚ) : Bool :=
  L.all fun d =>
    let k : ℤ := ⌊(d : ℚ) * x - (n : ℚ)⁻¹⌋
    decide ((k : ℚ) + (n : ℚ)⁻¹ ≤ (d : ℚ) * x) &&
    decide ((d : ℚ) * (x + w) ≤ (k : ℚ) + 1 - (n : ℚ)⁻¹)

/-- **The check certifies the whole window.** -/
theorem lonely_of_windowOK {L : List ℕ} {x w : ℚ} (h : windowOK n L x w = true)
    {t : ℝ} (h1 : (x : ℝ) ≤ t) (h2 : t ≤ (x : ℝ) + (w : ℝ)) :
    ∀ d ∈ L, (n : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  intro d hd
  unfold windowOK at h
  rw [List.all_eq_true] at h
  have hdd := h d hd
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hdd
  obtain ⟨hlo, hhi⟩ := hdd
  set k : ℤ := ⌊(d : ℚ) * x - (n : ℚ)⁻¹⌋ with hk
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
  -- cast the two rational bounds
  have hloR : ((k : ℝ)) + (n : ℝ)⁻¹ ≤ (d : ℝ) * (x : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hlo
    push_cast at hc
    exact hc
  have hhiR : (d : ℝ) * ((x : ℝ) + (w : ℝ)) ≤ (k : ℝ) + 1 - (n : ℝ)⁻¹ := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hhi
    push_cast at hc
    exact hc
  have hmono1 : (d : ℝ) * (x : ℝ) ≤ (d : ℝ) * t := mul_le_mul_of_nonneg_left h1 hd0
  have hmono2 : (d : ℝ) * t ≤ (d : ℝ) * ((x : ℝ) + (w : ℝ)) := mul_le_mul_of_nonneg_left h2 hd0
  have hy : (d : ℝ) * t = ((d : ℝ) * t - (k : ℝ)) + (k : ℝ) := by ring
  rw [hy]
  refine circDist_ge_of_band k ?_ ?_ <;> linarith

/-- **P4, the sharp-window criterion.**  A window `(x, x+w)` that the check certifies, wider
than the opening spacing `1/e`, forces a lonely opening of the flank `e` — the flank itself
being automatically at exactly `1/n` there. -/
theorem flank_of_windowOK {L : List ℕ} {e : ℕ} (he : 0 < e) {x w : ℚ}
    (hx : 0 ≤ x) (hw : 1 / (e : ℚ) < w) (h : windowOK n L x w = true) :
    ∃ j : ℕ, ∀ d ∈ (e :: L), (n : ℝ)⁻¹ ≤ circDist ((d : ℝ) * flankOpening n (e : ℝ) j) := by
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hxR : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hwR : 1 / (e : ℝ) < (w : ℝ) := by
    have hc := (Rat.cast_lt (K := ℝ)).mpr hw
    push_cast at hc
    exact hc
  obtain ⟨j, hj1, hj2⟩ := exists_flankOpening_mem_Ioo (n := n) heR hxR hwR
  refine ⟨j, fun d hd => ?_⟩
  rcases List.mem_cons.mp hd with rfl | hdL
  · rw [circDist_flank_self heR j]
  · exact lonely_of_windowOK h (le_of_lt hj1) (le_of_lt hj2) d hdL

open Classical in
/-- **On a difference set.**  The same criterion, stated where the obligation lives. -/
theorem lonely_flank_of_windowOK {S : Finset ℕ} {e : ℕ} (he : 0 < e) {x w : ℚ}
    (hx : 0 ≤ x) (hw : 1 / (e : ℚ) < w) (hmem : e ∈ S)
    (h : windowOK n (S.erase e).toList x w = true) :
    ∃ j : ℕ, Lonely n (Finset.image (fun d : ℕ => (d : ℝ)) S) (flankOpening n (e : ℝ) j) := by
  obtain ⟨j, hj⟩ := flank_of_windowOK (n := n) he hx hw h
  refine ⟨j, fun y hy => ?_⟩
  obtain ⟨d, hdS, rfl⟩ := Finset.mem_image.mp hy
  by_cases hde : d = e
  · subst hde; exact hj d (List.mem_cons_self)
  · exact hj d (List.mem_cons_of_mem _ (Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨hde, hdS⟩)))

/-! ## a worked instance, so the criterion is visibly not vacuous

`ds = (1, 2, 5, 16)` is in the residue: `5` is a non-flank multiple of 5, the ratio `16/1` is
wide, and `16 > 15` — so none of P1′, P2, P3 reaches it.  Its lonely set has the interval
`(6/25, 9/25)`, of width `3/25 > 1/16`, and the certificate checks by `decide`. -/

example : windowOK 5 [1, 2, 5] (6/25) (3/25) = true := by norm_num [windowOK]

instance : Fact (2 ≤ 5) := ⟨by norm_num⟩

theorem residue_instance_1_2_5_16 :
    ∃ j : ℕ, ∀ d ∈ ([16, 1, 2, 5] : List ℕ),
      ((5 : ℕ) : ℝ)⁻¹ ≤ circDist ((d : ℝ) * flankOpening 5 ((16 : ℕ) : ℝ) j) :=
  flank_of_windowOK (n := 5) (L := [1,2,5]) (e := 16) (x := 6/25) (w := 3/25)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [windowOK])

end LRC.Window
