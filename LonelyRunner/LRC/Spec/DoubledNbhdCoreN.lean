import LonelyRunner.LRC.Spec.GridClassN
import LonelyRunner.LRC.Spec.DoubledSlotN

/-!
# The deviated doubled slot: the relocation lemma and the generic roles

2026-09-27.  Undeviated, a runner of the doubled-slot family is lonely at an opening of a named flank `X` at the
instant `t₀` (`DoubledSlotN`).  Deviated, the instant is `X`'s actual opening, `t₀ · D_X / δ_X`: the flank sits
exactly where it sat, and every other reading moves by at most `t₀ (2η + 2ηK)` (`reloc`), `K` bounding its size
relative to the flank.  The generic roles are here: the far member of the pair (the ratio condition at its nearest
runner), the home member at an interior slot (the partner's opening), and a runner outside the pair (the grid rule at
class 1 or 3, `GridClassN`).  The ends and the seven exceptions are in `DoubledNbhdN`.  No `sorry`, no `native_decide`.
-/

namespace LRC.DoubledNbhd

open Arrangement LRC.GridNbhd

/-- **The relocation.**  At the flank's actual opening every reading sits within `t₀(2η + 2ηK)` of its undeviated
position `t₀ · D_j`. -/
theorem reloc {t0 η K δX δj : ℝ} {DX Dj : ℤ} (ht0 : 0 ≤ t0) (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4)
    (hX : |δX - DX| ≤ η) (hDX : 1 ≤ |(DX : ℝ)|) (hj : |δj - Dj| ≤ η) (hK0 : 0 ≤ K)
    (hK : |(Dj : ℝ)| ≤ K * |(DX : ℝ)|) :
    |δj * (t0 * DX / δX) - t0 * Dj| ≤ t0 * (2 * η + 2 * η * K) := by
  have hδX : |(DX : ℝ)| / 2 ≤ |δX| := by
    have h := abs_sub_abs_le_abs_sub (DX : ℝ) δX
    rw [abs_sub_comm] at h
    linarith
  have hδXpos : 0 < |δX| := by linarith
  have hδX0 : δX ≠ 0 := fun h => by rw [h, abs_zero] at hδXpos; exact lt_irrefl _ hδXpos
  have hk1 : |(DX : ℝ) / δX - 1| ≤ 2 * η / |(DX : ℝ)| := by
    have e1 : (DX : ℝ) / δX - 1 = ((DX : ℝ) - δX) / δX := by field_simp
    rw [e1, abs_div, div_le_div_iff₀ hδXpos (by linarith)]
    have : |(DX : ℝ) - δX| ≤ η := by rw [abs_sub_comm]; exact hX
    nlinarith [abs_nonneg ((DX : ℝ) - δX)]
  have hk : |(DX : ℝ) / δX| ≤ 2 := by
    have h := abs_sub_abs_le_abs_sub ((DX : ℝ) / δX) 1
    have : 2 * η / |(DX : ℝ)| ≤ 1 := by rw [div_le_iff₀ (by linarith)]; linarith
    rw [abs_one] at h
    linarith
  have key : δj * (t0 * DX / δX) - t0 * Dj
      = t0 * ((δj - Dj) * ((DX : ℝ) / δX) + Dj * ((DX : ℝ) / δX - 1)) := by
    field_simp; ring
  rw [key, abs_mul, abs_of_nonneg ht0]
  apply mul_le_mul_of_nonneg_left _ ht0
  calc |(δj - Dj) * ((DX : ℝ) / δX) + Dj * ((DX : ℝ) / δX - 1)|
      ≤ |(δj - Dj) * ((DX : ℝ) / δX)| + |(Dj : ℝ) * ((DX : ℝ) / δX - 1)| := abs_add_le _ _
    _ = |δj - Dj| * |(DX : ℝ) / δX| + |(Dj : ℝ)| * |(DX : ℝ) / δX - 1| := by rw [abs_mul, abs_mul]
    _ ≤ η * 2 + (K * |(DX : ℝ)|) * (2 * η / |(DX : ℝ)|) := by
        gcongr
    _ = 2 * η + 2 * η * K := by field_simp

/-- A reading within `err` of a point that sits `err` inside a band is clear. -/
theorem clear_near {x y err : ℝ} {N : ℤ} (h : |x - y| ≤ err) (h1 : (N : ℝ) + 1 / 8 + err ≤ y)
    (h2 : y + err ≤ (N : ℝ) + 7 / 8) : (8 : ℝ)⁻¹ ≤ circDist x := by
  have := abs_le.mp h
  exact LRC.TwoPinner.clear_of_band (N := N) (by linarith) (by linarith)

/-- The relocation, closed off in a band. -/
theorem reloc_clear {t0 η K δX δj : ℝ} {DX Dj N : ℤ} (ht0 : 0 ≤ t0) (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4)
    (hX : |δX - DX| ≤ η) (hDX : 1 ≤ |(DX : ℝ)|) (hj : |δj - Dj| ≤ η) (hK0 : 0 ≤ K)
    (hK : |(Dj : ℝ)| ≤ K * |(DX : ℝ)|)
    (h1 : (N : ℝ) + 1 / 8 + t0 * (2 * η + 2 * η * K) ≤ t0 * Dj)
    (h2 : t0 * Dj + t0 * (2 * η + 2 * η * K) ≤ (N : ℝ) + 7 / 8) :
    (8 : ℝ)⁻¹ ≤ circDist (δj * (t0 * DX / δX)) :=
  clear_near (reloc ht0 hη0 hη1 hX hDX hj hK0 hK) h1 h2

/-- The flank itself sits exactly on its band edge. -/
theorem flank_exact {t0 δX : ℝ} {DX : ℤ} {L : ℤ} (hδX : δX ≠ 0)
    (ht : t0 * DX = L + 1 / 8 ∨ t0 * DX = -((L : ℝ) + 1 / 8)) :
    (8 : ℝ)⁻¹ ≤ circDist (δX * (t0 * DX / δX)) := by
  rw [show δX * (t0 * DX / δX) = t0 * DX by field_simp]
  rcases ht with h | h <;> rw [h]
  · exact LRC.TwoPinner.clear_of_band (N := L) (by linarith) (by linarith)
  · exact LRC.TwoPinner.clear_of_band (N := -L - 1) (by push_cast; linarith) (by push_cast; linarith)

/-- The sign of a deviated flank reading, and that it is not zero. -/
theorem nz_of {x η : ℝ} {D : ℤ} (hη : η < 1) (hx : |x - D| ≤ η) (hD : 1 ≤ |(D : ℝ)|) : x ≠ 0 := by
  intro h; rw [h, zero_sub, abs_neg] at hx; linarith

/-- **Far member**: the ratio condition at its nearest runner `X` (`D_X = −W`, `W ≥ 2`), every other reading in
`[−(W + 7), −(W + 1)]`. -/
theorem far_role {δ : Fin 8 → ℝ} {D : Fin 8 → ℤ} {k X : Fin 8} {η : ℝ} {W : ℤ} (hXk : X ≠ k)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 32) (hδ : ∀ j, |δ j - D j| ≤ η) (hDX : D X = -W) (hW2 : 2 ≤ W)
    (hrest : ∀ j, j ≠ k → j ≠ X → -(W + 7) ≤ D j ∧ D j ≤ -(W + 1)) :
    ∀ j, j ≠ k → (8 : ℝ)⁻¹ ≤ circDist (δ j * ((1 / (8 * (W : ℝ))) * D X / δ X)) := by
  have hWR : (2 : ℝ) ≤ W := by exact_mod_cast hW2
  have hDXR : (D X : ℝ) = -W := by exact_mod_cast hDX
  have hDX1 : 1 ≤ |(D X : ℝ)| := by
    rw [hDXR, abs_neg, abs_of_pos (show (0 : ℝ) < W by linarith)]; linarith
  have hδX0 := nz_of (by linarith) (hδ X) hDX1
  intro j hjk
  by_cases hjX : j = X
  · rw [hjX]
    refine flank_exact (L := 0) hδX0 (Or.inr ?_)
    rw [hDXR]; field_simp; push_cast; ring
  obtain ⟨hlo, hhi⟩ := hrest j hjk hjX
  have hloR : -((W : ℝ) + 7) ≤ D j := by exact_mod_cast hlo
  have hhiR : (D j : ℝ) ≤ -((W : ℝ) + 1) := by exact_mod_cast hhi
  set u : ℝ := 1 / (8 * (W : ℝ)) with hudef
  have hu0 : 0 < u := by rw [hudef]; positivity
  have huW : u * W = 1 / 8 := by rw [hudef]; field_simp
  have hu16 : u ≤ 1 / 16 := by
    rw [hudef, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  apply reloc_clear (N := -1) (K := 8) hu0.le hη0 (by linarith) (hδ X) hDX1 (hδ j) (by norm_num)
  · rw [hDXR, abs_neg, abs_of_pos (show (0 : ℝ) < W by linarith),
      abs_of_neg (show (D j : ℝ) < 0 by linarith)]
    linarith
  · have := mul_le_mul_of_nonneg_left hloR hu0.le
    push_cast; nlinarith
  · have := mul_le_mul_of_nonneg_left hhiR hu0.le
    push_cast; nlinarith

/-- **Home member at an interior slot**: the partner's opening (`D_X = 8m`), every other reading of size 1 to 6. -/
theorem home_role {δ : Fin 8 → ℝ} {D : Fin 8 → ℤ} {k X : Fin 8} {η : ℝ} {m : ℕ} (hm : 1 ≤ m) (hXk : X ≠ k)
    (hη0 : 0 ≤ η) (hηm : η * (256 * ((m : ℝ) + 1)) ≤ 1) (hδ : ∀ j, |δ j - D j| ≤ η)
    (hDX : D X = 8 * m) (hrest : ∀ j, j ≠ k → j ≠ X → 1 ≤ |D j| ∧ |D j| ≤ 6) :
    ∀ j, j ≠ k → (8 : ℝ)⁻¹ ≤ circDist (δ j * (((8 * (m : ℝ) + 1) / (64 * m)) * D X / δ X)) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hDXR : (D X : ℝ) = 8 * m := by exact_mod_cast hDX
  have hDX1 : 1 ≤ |(D X : ℝ)| := by
    rw [hDXR, abs_of_pos (show (0 : ℝ) < 8 * m by linarith)]; linarith
  have hη1 : η ≤ 1 / 512 := by nlinarith
  have hηm' : η * m ≤ 1 / 256 := by nlinarith
  have hδX0 := nz_of (by linarith) (hδ X) hDX1
  set t0 := (8 * (m : ℝ) + 1) / (64 * m) with ht0def
  have ht0 : 64 * (m : ℝ) * t0 = 8 * m + 1 := by rw [ht0def]; field_simp
  have ht0lo : 1 / 8 < t0 := by rw [ht0def, lt_div_iff₀ (by positivity)]; linarith
  have ht0hi : t0 ≤ 9 / 64 := by rw [ht0def, div_le_iff₀ (by positivity)]; linarith
  intro j hjk
  by_cases hjX : j = X
  · rw [hjX]
    refine flank_exact (L := m) hδX0 (Or.inl ?_)
    rw [hDXR, ht0def]; push_cast; field_simp; ring
  obtain ⟨h1, h6⟩ := hrest j hjk hjX
  have hK : |(D j : ℝ)| ≤ 1 * |(D X : ℝ)| := by
    rw [one_mul, hDXR, abs_of_pos (show (0 : ℝ) < 8 * m by linarith)]
    have : |(D j : ℝ)| ≤ 6 := by exact_mod_cast h6
    linarith
  -- the error, against the smallest margin 1/(64m) = t0 - 1/8
  have herr : t0 * (2 * η + 2 * η * 1) ≤ t0 - 1 / 8 := by
    have : 64 * (m : ℝ) * (t0 * (4 * η)) ≤ 64 * m * (t0 - 1 / 8) := by nlinarith
    nlinarith
  rcases lt_or_gt_of_ne (show D j ≠ 0 by intro h; rw [h] at h1; norm_num at h1) with hneg | hpos
  · have ha1 : (D j : ℝ) ≤ -1 := by exact_mod_cast (show D j ≤ -1 by omega)
    have ha6 : -6 ≤ (D j : ℝ) := by
      have : |D j| ≤ 6 := h6; rw [abs_of_neg hneg] at this
      exact_mod_cast (show -6 ≤ D j by omega)
    apply reloc_clear (N := -1) (K := 1) (by linarith) hη0 (by linarith) (hδ X) hDX1 (hδ j) (by norm_num) hK
    · push_cast; nlinarith
    · push_cast; nlinarith
  · have ha1 : (1 : ℝ) ≤ D j := by exact_mod_cast (show 1 ≤ D j by omega)
    have ha6 : (D j : ℝ) ≤ 6 := by
      have : |D j| ≤ 6 := h6; rw [abs_of_pos hpos] at this
      exact_mod_cast this
    apply reloc_clear (N := 0) (K := 1) (by linarith) hη0 (by linarith) (hδ X) hDX1 (hδ j) (by norm_num) hK
    · push_cast; nlinarith
    · push_cast; nlinarith

/-- A flank-relocated instant is positive: the deviated flank reading has the sign of its whole part. -/
theorem pos_reloc {t0 η δX DX : ℝ} (ht0 : 0 < t0) (hη : η < 1) (hX : |δX - DX| ≤ η) (hDX : 1 ≤ |DX|) :
    0 < t0 * DX / δX := by
  have h := abs_le.mp hX
  rcases le_or_gt 0 DX with hpos | hneg
  · rw [abs_of_nonneg hpos] at hDX
    exact div_pos (mul_pos ht0 (by linarith)) (by linarith)
  · rw [abs_of_neg hneg] at hDX
    exact div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg ht0 hneg) (by linarith)

/-- **The partner at a fixed flank's opening**: at `t₀` it reads the fraction `P' m / dd` (not a whole number, as
`dd ∤ m`), at least `1/dd` from the integers; the relocation moves it by less than `1/dd − 1/8`. -/
theorem partner_lip {δX δj η t0 dX : ℝ} {DX Dj : ℤ} {m dd P' : ℕ} (ht0 : 0 ≤ t0) (hdd : 2 ≤ dd)
    (hdd8 : dd ≤ 8) (hcop : Nat.Coprime P' dd) (ht08 : t0 * 8 = (P' : ℝ) / dd) (hdv : ¬ dd ∣ m)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 512) (hηm : η * m ≤ 1 / 256) (hdX : |(DX : ℝ)| = dX) (hdX1 : 1 ≤ dX)
    (hbud : t0 * (2 * (1 / 512) + 16 * (1 / 256) / dX) ≤ 1 / dd - 1 / 8)
    (hX : |δX - DX| ≤ η) (hj : |δj - Dj| ≤ η) (hDj : (Dj : ℝ) = 8 * m) :
    (8 : ℝ)⁻¹ ≤ circDist (δj * (t0 * DX / δX)) := by
  have hmR : (0 : ℝ) ≤ m := by positivity
  have hddR : (2 : ℝ) ≤ dd := by exact_mod_cast hdd
  have hK : |(Dj : ℝ)| ≤ (8 * m / dX) * |(DX : ℝ)| := by
    rw [hDj, hdX, abs_of_nonneg (by positivity)]; field_simp; rfl
  have hr := reloc ht0 hη0 (by linarith) hX (by rw [hdX]; exact hdX1) hj (by positivity) hK
  -- the error bound
  have herr : t0 * (2 * η + 2 * η * (8 * m / dX)) ≤ 1 / dd - 1 / 8 := by
    have e1 : 2 * η * (8 * m / dX) = 16 * (η * m) / dX := by ring
    have e2 : 16 * (η * m) / dX ≤ 16 * (1 / 256) / dX := by gcongr
    have e3 : t0 * (2 * η + 2 * η * (8 * m / dX)) ≤ t0 * (2 * (1 / 512) + 16 * (1 / 256) / dX) := by
      apply mul_le_mul_of_nonneg_left _ ht0; rw [e1]; linarith
    linarith
  -- the partner's undeviated reading
  have hpos : (1 : ℝ) / dd ≤ circDist (t0 * Dj) := by
    have hnd : ¬ ((dd : ℕ) : ℤ) ∣ ((P' * m : ℕ) : ℤ) := by
      intro h
      have h' : dd ∣ P' * m := by exact_mod_cast h
      exact hdv (hcop.symm.dvd_of_dvd_mul_left h')
    have := ConstructionN.circDist_int_div (n := dd) (by omega) hnd
    have e : t0 * Dj = (((P' * m : ℕ) : ℤ) : ℝ) / ((dd : ℕ) : ℝ) := by
      rw [hDj]; push_cast
      have : t0 = (P' : ℝ) / dd / 8 := by linarith
      rw [this]; field_simp
    rw [e]; simpa using this
  have hlip := circDist_lipschitz.dist_le_mul (δj * (t0 * DX / δX)) (t0 * Dj)
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
  have := (abs_sub_le_iff.mp hlip).2
  have h8 : (8 : ℝ)⁻¹ = 1 / 8 := by norm_num
  rw [h8]
  linarith

end LRC.DoubledNbhd
