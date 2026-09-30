import LonelyRunner.LRC.Spec.TwoPinnerN

/-!
# The band cover, core: pairwise laps for seven real readings

2026-09-28.  Running record: `RUNNING_LOG_order8_v1.md` E169.

A lap assignment `k₀ … k₆` whose clear intervals `[(8kᵢ+1)/sᵢ, (8kᵢ+7)/sᵢ]` (of `R = 8t`) meet pairwise meets as a whole
(1-D Helly): at `R = maxᵢ (8kᵢ+1)/sᵢ` every reading is clear.  `TwoBlockN.lonely_eight_of_pairwise_laps` for seven real
readings; `cone_lonely` takes the forty-two pairwise inequalities as explicit hypotheses, the form the generated
band-cover lemmas supply.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.BandCover

/-- **Pairwise laps, seven real readings, lap function form.** -/
theorem cone_lonely_fun (s : Fin 7 → ℝ) (hpos : ∀ i, 0 < s i) (k : Fin 7 → ℕ)
    (hpair : ∀ i j, i ≠ j → (8 * (k i : ℝ) + 1) * s j ≤ (8 * (k j : ℝ) + 7) * s i) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, (8 : ℝ)⁻¹ ≤ circDist (s i * t) := by
  classical
  obtain ⟨e, -, he⟩ := Finset.exists_max_image Finset.univ (fun i => (8 * (k i : ℝ) + 1) / s i) Finset.univ_nonempty
  have hse := hpos e
  refine ⟨(8 * (k e : ℝ) + 1) / s e / 8, by positivity, fun j => ?_⟩
  have hsj := hpos j
  have hle := he j (Finset.mem_univ j)
  have hform : s j * ((8 * (k e : ℝ) + 1) / s e / 8) = ((8 * (k e : ℝ) + 1) * s j) / (8 * s e) := by field_simp
  refine LRC.TwoPinner.clear_of_band (N := (k j : ℤ)) ?_ ?_
  · rw [div_le_div_iff₀ hsj hse] at hle
    rw [hform, le_div_iff₀ (by positivity)]
    push_cast
    nlinarith only [hle, hse]
  · have hej : (8 * (k e : ℝ) + 1) * s j ≤ (8 * (k j : ℝ) + 7) * s e := by
      by_cases h : e = j
      · subst h; nlinarith only [hse]
      · exact hpair e j h
    rw [hform, div_le_iff₀ (by positivity)]
    push_cast
    nlinarith only [hej, hse]

/-- **Pairwise laps, seven real readings, explicit form.** -/
theorem cone_lonely (s : Fin 7 → ℝ) (hpos : ∀ i, 0 < s i) (k0 k1 k2 k3 k4 k5 k6 : ℕ)
    (h01 : (8 * (k0 : ℝ) + 1) * s 1 ≤ (8 * (k1 : ℝ) + 7) * s 0)
    (h02 : (8 * (k0 : ℝ) + 1) * s 2 ≤ (8 * (k2 : ℝ) + 7) * s 0)
    (h03 : (8 * (k0 : ℝ) + 1) * s 3 ≤ (8 * (k3 : ℝ) + 7) * s 0)
    (h04 : (8 * (k0 : ℝ) + 1) * s 4 ≤ (8 * (k4 : ℝ) + 7) * s 0)
    (h05 : (8 * (k0 : ℝ) + 1) * s 5 ≤ (8 * (k5 : ℝ) + 7) * s 0)
    (h06 : (8 * (k0 : ℝ) + 1) * s 6 ≤ (8 * (k6 : ℝ) + 7) * s 0)
    (h10 : (8 * (k1 : ℝ) + 1) * s 0 ≤ (8 * (k0 : ℝ) + 7) * s 1)
    (h12 : (8 * (k1 : ℝ) + 1) * s 2 ≤ (8 * (k2 : ℝ) + 7) * s 1)
    (h13 : (8 * (k1 : ℝ) + 1) * s 3 ≤ (8 * (k3 : ℝ) + 7) * s 1)
    (h14 : (8 * (k1 : ℝ) + 1) * s 4 ≤ (8 * (k4 : ℝ) + 7) * s 1)
    (h15 : (8 * (k1 : ℝ) + 1) * s 5 ≤ (8 * (k5 : ℝ) + 7) * s 1)
    (h16 : (8 * (k1 : ℝ) + 1) * s 6 ≤ (8 * (k6 : ℝ) + 7) * s 1)
    (h20 : (8 * (k2 : ℝ) + 1) * s 0 ≤ (8 * (k0 : ℝ) + 7) * s 2)
    (h21 : (8 * (k2 : ℝ) + 1) * s 1 ≤ (8 * (k1 : ℝ) + 7) * s 2)
    (h23 : (8 * (k2 : ℝ) + 1) * s 3 ≤ (8 * (k3 : ℝ) + 7) * s 2)
    (h24 : (8 * (k2 : ℝ) + 1) * s 4 ≤ (8 * (k4 : ℝ) + 7) * s 2)
    (h25 : (8 * (k2 : ℝ) + 1) * s 5 ≤ (8 * (k5 : ℝ) + 7) * s 2)
    (h26 : (8 * (k2 : ℝ) + 1) * s 6 ≤ (8 * (k6 : ℝ) + 7) * s 2)
    (h30 : (8 * (k3 : ℝ) + 1) * s 0 ≤ (8 * (k0 : ℝ) + 7) * s 3)
    (h31 : (8 * (k3 : ℝ) + 1) * s 1 ≤ (8 * (k1 : ℝ) + 7) * s 3)
    (h32 : (8 * (k3 : ℝ) + 1) * s 2 ≤ (8 * (k2 : ℝ) + 7) * s 3)
    (h34 : (8 * (k3 : ℝ) + 1) * s 4 ≤ (8 * (k4 : ℝ) + 7) * s 3)
    (h35 : (8 * (k3 : ℝ) + 1) * s 5 ≤ (8 * (k5 : ℝ) + 7) * s 3)
    (h36 : (8 * (k3 : ℝ) + 1) * s 6 ≤ (8 * (k6 : ℝ) + 7) * s 3)
    (h40 : (8 * (k4 : ℝ) + 1) * s 0 ≤ (8 * (k0 : ℝ) + 7) * s 4)
    (h41 : (8 * (k4 : ℝ) + 1) * s 1 ≤ (8 * (k1 : ℝ) + 7) * s 4)
    (h42 : (8 * (k4 : ℝ) + 1) * s 2 ≤ (8 * (k2 : ℝ) + 7) * s 4)
    (h43 : (8 * (k4 : ℝ) + 1) * s 3 ≤ (8 * (k3 : ℝ) + 7) * s 4)
    (h45 : (8 * (k4 : ℝ) + 1) * s 5 ≤ (8 * (k5 : ℝ) + 7) * s 4)
    (h46 : (8 * (k4 : ℝ) + 1) * s 6 ≤ (8 * (k6 : ℝ) + 7) * s 4)
    (h50 : (8 * (k5 : ℝ) + 1) * s 0 ≤ (8 * (k0 : ℝ) + 7) * s 5)
    (h51 : (8 * (k5 : ℝ) + 1) * s 1 ≤ (8 * (k1 : ℝ) + 7) * s 5)
    (h52 : (8 * (k5 : ℝ) + 1) * s 2 ≤ (8 * (k2 : ℝ) + 7) * s 5)
    (h53 : (8 * (k5 : ℝ) + 1) * s 3 ≤ (8 * (k3 : ℝ) + 7) * s 5)
    (h54 : (8 * (k5 : ℝ) + 1) * s 4 ≤ (8 * (k4 : ℝ) + 7) * s 5)
    (h56 : (8 * (k5 : ℝ) + 1) * s 6 ≤ (8 * (k6 : ℝ) + 7) * s 5)
    (h60 : (8 * (k6 : ℝ) + 1) * s 0 ≤ (8 * (k0 : ℝ) + 7) * s 6)
    (h61 : (8 * (k6 : ℝ) + 1) * s 1 ≤ (8 * (k1 : ℝ) + 7) * s 6)
    (h62 : (8 * (k6 : ℝ) + 1) * s 2 ≤ (8 * (k2 : ℝ) + 7) * s 6)
    (h63 : (8 * (k6 : ℝ) + 1) * s 3 ≤ (8 * (k3 : ℝ) + 7) * s 6)
    (h64 : (8 * (k6 : ℝ) + 1) * s 4 ≤ (8 * (k4 : ℝ) + 7) * s 6)
    (h65 : (8 * (k6 : ℝ) + 1) * s 5 ≤ (8 * (k5 : ℝ) + 7) * s 6) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, (8 : ℝ)⁻¹ ≤ circDist (s i * t) := by
  refine cone_lonely_fun s hpos ![k0, k1, k2, k3, k4, k5, k6] ?_
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first | exact absurd rfl hij | (simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk] ; assumption)

/-- The seven readings of a band shape, the nearest runner at `1`: `1, 1 + x₀, …, 1 + x₅`. -/
def bandS (x0 x1 x2 x3 x4 x5 : ℝ) : Fin 7 → ℝ := ![1, 1 + x0, 1 + x1, 1 + x2, 1 + x3, 1 + x4, 1 + x5]

/-- **One cell of the band cover.**  Seven laps whose clear intervals meet pairwise: lonely. -/
theorem cone_band (x0 x1 x2 x3 x4 x5 : ℝ) (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) (hx3 : 0 ≤ x3)
    (hx4 : 0 ≤ x4) (hx5 : 0 ≤ x5) (k0 k1 k2 k3 k4 k5 k6 : ℕ)
    (h01 : (8 * (k0 : ℝ) + 1) * (1 + x0) ≤ (8 * (k1 : ℝ) + 7) * 1)
    (h02 : (8 * (k0 : ℝ) + 1) * (1 + x1) ≤ (8 * (k2 : ℝ) + 7) * 1)
    (h03 : (8 * (k0 : ℝ) + 1) * (1 + x2) ≤ (8 * (k3 : ℝ) + 7) * 1)
    (h04 : (8 * (k0 : ℝ) + 1) * (1 + x3) ≤ (8 * (k4 : ℝ) + 7) * 1)
    (h05 : (8 * (k0 : ℝ) + 1) * (1 + x4) ≤ (8 * (k5 : ℝ) + 7) * 1)
    (h06 : (8 * (k0 : ℝ) + 1) * (1 + x5) ≤ (8 * (k6 : ℝ) + 7) * 1)
    (h10 : (8 * (k1 : ℝ) + 1) * 1 ≤ (8 * (k0 : ℝ) + 7) * (1 + x0))
    (h12 : (8 * (k1 : ℝ) + 1) * (1 + x1) ≤ (8 * (k2 : ℝ) + 7) * (1 + x0))
    (h13 : (8 * (k1 : ℝ) + 1) * (1 + x2) ≤ (8 * (k3 : ℝ) + 7) * (1 + x0))
    (h14 : (8 * (k1 : ℝ) + 1) * (1 + x3) ≤ (8 * (k4 : ℝ) + 7) * (1 + x0))
    (h15 : (8 * (k1 : ℝ) + 1) * (1 + x4) ≤ (8 * (k5 : ℝ) + 7) * (1 + x0))
    (h16 : (8 * (k1 : ℝ) + 1) * (1 + x5) ≤ (8 * (k6 : ℝ) + 7) * (1 + x0))
    (h20 : (8 * (k2 : ℝ) + 1) * 1 ≤ (8 * (k0 : ℝ) + 7) * (1 + x1))
    (h21 : (8 * (k2 : ℝ) + 1) * (1 + x0) ≤ (8 * (k1 : ℝ) + 7) * (1 + x1))
    (h23 : (8 * (k2 : ℝ) + 1) * (1 + x2) ≤ (8 * (k3 : ℝ) + 7) * (1 + x1))
    (h24 : (8 * (k2 : ℝ) + 1) * (1 + x3) ≤ (8 * (k4 : ℝ) + 7) * (1 + x1))
    (h25 : (8 * (k2 : ℝ) + 1) * (1 + x4) ≤ (8 * (k5 : ℝ) + 7) * (1 + x1))
    (h26 : (8 * (k2 : ℝ) + 1) * (1 + x5) ≤ (8 * (k6 : ℝ) + 7) * (1 + x1))
    (h30 : (8 * (k3 : ℝ) + 1) * 1 ≤ (8 * (k0 : ℝ) + 7) * (1 + x2))
    (h31 : (8 * (k3 : ℝ) + 1) * (1 + x0) ≤ (8 * (k1 : ℝ) + 7) * (1 + x2))
    (h32 : (8 * (k3 : ℝ) + 1) * (1 + x1) ≤ (8 * (k2 : ℝ) + 7) * (1 + x2))
    (h34 : (8 * (k3 : ℝ) + 1) * (1 + x3) ≤ (8 * (k4 : ℝ) + 7) * (1 + x2))
    (h35 : (8 * (k3 : ℝ) + 1) * (1 + x4) ≤ (8 * (k5 : ℝ) + 7) * (1 + x2))
    (h36 : (8 * (k3 : ℝ) + 1) * (1 + x5) ≤ (8 * (k6 : ℝ) + 7) * (1 + x2))
    (h40 : (8 * (k4 : ℝ) + 1) * 1 ≤ (8 * (k0 : ℝ) + 7) * (1 + x3))
    (h41 : (8 * (k4 : ℝ) + 1) * (1 + x0) ≤ (8 * (k1 : ℝ) + 7) * (1 + x3))
    (h42 : (8 * (k4 : ℝ) + 1) * (1 + x1) ≤ (8 * (k2 : ℝ) + 7) * (1 + x3))
    (h43 : (8 * (k4 : ℝ) + 1) * (1 + x2) ≤ (8 * (k3 : ℝ) + 7) * (1 + x3))
    (h45 : (8 * (k4 : ℝ) + 1) * (1 + x4) ≤ (8 * (k5 : ℝ) + 7) * (1 + x3))
    (h46 : (8 * (k4 : ℝ) + 1) * (1 + x5) ≤ (8 * (k6 : ℝ) + 7) * (1 + x3))
    (h50 : (8 * (k5 : ℝ) + 1) * 1 ≤ (8 * (k0 : ℝ) + 7) * (1 + x4))
    (h51 : (8 * (k5 : ℝ) + 1) * (1 + x0) ≤ (8 * (k1 : ℝ) + 7) * (1 + x4))
    (h52 : (8 * (k5 : ℝ) + 1) * (1 + x1) ≤ (8 * (k2 : ℝ) + 7) * (1 + x4))
    (h53 : (8 * (k5 : ℝ) + 1) * (1 + x2) ≤ (8 * (k3 : ℝ) + 7) * (1 + x4))
    (h54 : (8 * (k5 : ℝ) + 1) * (1 + x3) ≤ (8 * (k4 : ℝ) + 7) * (1 + x4))
    (h56 : (8 * (k5 : ℝ) + 1) * (1 + x5) ≤ (8 * (k6 : ℝ) + 7) * (1 + x4))
    (h60 : (8 * (k6 : ℝ) + 1) * 1 ≤ (8 * (k0 : ℝ) + 7) * (1 + x5))
    (h61 : (8 * (k6 : ℝ) + 1) * (1 + x0) ≤ (8 * (k1 : ℝ) + 7) * (1 + x5))
    (h62 : (8 * (k6 : ℝ) + 1) * (1 + x1) ≤ (8 * (k2 : ℝ) + 7) * (1 + x5))
    (h63 : (8 * (k6 : ℝ) + 1) * (1 + x2) ≤ (8 * (k3 : ℝ) + 7) * (1 + x5))
    (h64 : (8 * (k6 : ℝ) + 1) * (1 + x3) ≤ (8 * (k4 : ℝ) + 7) * (1 + x5))
    (h65 : (8 * (k6 : ℝ) + 1) * (1 + x4) ≤ (8 * (k5 : ℝ) + 7) * (1 + x5)) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, (8 : ℝ)⁻¹ ≤ circDist (bandS x0 x1 x2 x3 x4 x5 i * t) := by
  refine cone_lonely (bandS x0 x1 x2 x3 x4 x5) ?_ k0 k1 k2 k3 k4 k5 k6 (by simpa [bandS] using h01) (by simpa [bandS] using h02) (by simpa [bandS] using h03) (by simpa [bandS] using h04) (by simpa [bandS] using h05) (by simpa [bandS] using h06) (by simpa [bandS] using h10) (by simpa [bandS] using h12) (by simpa [bandS] using h13) (by simpa [bandS] using h14) (by simpa [bandS] using h15) (by simpa [bandS] using h16) (by simpa [bandS] using h20) (by simpa [bandS] using h21) (by simpa [bandS] using h23) (by simpa [bandS] using h24) (by simpa [bandS] using h25) (by simpa [bandS] using h26) (by simpa [bandS] using h30) (by simpa [bandS] using h31) (by simpa [bandS] using h32) (by simpa [bandS] using h34) (by simpa [bandS] using h35) (by simpa [bandS] using h36) (by simpa [bandS] using h40) (by simpa [bandS] using h41) (by simpa [bandS] using h42) (by simpa [bandS] using h43) (by simpa [bandS] using h45) (by simpa [bandS] using h46) (by simpa [bandS] using h50) (by simpa [bandS] using h51) (by simpa [bandS] using h52) (by simpa [bandS] using h53) (by simpa [bandS] using h54) (by simpa [bandS] using h56) (by simpa [bandS] using h60) (by simpa [bandS] using h61) (by simpa [bandS] using h62) (by simpa [bandS] using h63) (by simpa [bandS] using h64) (by simpa [bandS] using h65)
  intro i; fin_cases i <;> simp [bandS] <;> linarith

end LRC.BandCover
