import LonelyRunner.LRC.Cascade.EighthFamily

/-!
# A census family, cold, through the `U`/`K` calculus

Part of the cascade artefact (`LRC/Cascade/`).  Threshold `1/8`.

The batch machine's row for the cover `((2,1),(5,1),(10,1),(10,3),(10,7))`
(`results/batch_machine_v1.out`) pins the ratios `1/10, 1/5, 3/10, 1/2, 7/10` and reports the flank
`1/2` as `('U', 3, 'K', [])` — free for every value of the free parameter.  Scaled by `10` the family
is `{1, 2, 3, 5, 7, x, 10}` with `0 < x < 10`, and that flank is the difference `5`.

Unlike the eighth family this one arrives with nothing: every clearance fact below is produced here,
from `Flanks.circDist_ge_of_band` alone.  `P = 5`; the machine's uncovered set is `{1, 3, 4}` and the
two residues `{1, 3}` used here suffice.

Data: `experiments/n8/cold_family_data_v1.py`.
-/

set_option linter.unusedVariables false

namespace CensusFamilies

open ConstructionN MomentIterationN Flanks EighthFamily

/-- **The modulus-10 family is lonely at the flank `5`, for every real `x`.** -/
theorem family10_lonely (x : ℝ) (hx0 : 0 < x) (hx10 : x < 10) :
    ∃ k : ℕ, Lonely 8 ({1, 2, 3, 5, 7, x, 10} : Finset ℝ) (Flanks.flankOpening 8 5 k) := by
  have h5 : ((5 : ℕ) : ℝ) * (x / 5) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 5 {1, 3}
    ⟨1, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hcast : ((5 : ℕ) : ℝ) * (d / 5) = d := by push_cast; ring
    rw [hcast]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) = ((1 : ℤ) : ℝ) by norm_num]; exact Int.fract_intCast 1
    · rw [show (2 : ℝ) = ((2 : ℤ) : ℝ) by norm_num]; exact Int.fract_intCast 2
    · rw [show (3 : ℝ) = ((3 : ℤ) : ℝ) by norm_num]; exact Int.fract_intCast 3
    · rw [show (5 : ℝ) = ((5 : ℤ) : ℝ) by norm_num]; exact Int.fract_intCast 5
    · rw [show (7 : ℝ) = ((7 : ℤ) : ℝ) by norm_num]; exact Int.fract_intCast 7
    · exact absurd h hdx
    · rw [show (10 : ℝ) = ((10 : ℤ) : ℝ) by norm_num]; exact Int.fract_intCast 10
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 5 1 = (9 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 5 1 = (18 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 5 1 = (27 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 5 1 = (5 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 5 1 = (23 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 5 1 = (10 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 5 3 = (25 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 5 3 = (10 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 5 3 = (35 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 5 3 = (5 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 5 3 = (15 : ℝ)/40 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 5 3 = (10 : ℝ)/40 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
  · intro hlat
    rw [h5] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm9 : ⌊x⌋ ≤ 9 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 10 := by rw [← hxi]; exact hx10
      have hh' : (⌊x⌋ : ℤ) < 10 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (9 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (18 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (27 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (20 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (5 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (14 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (23 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (32 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (25 : ℝ)/40 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)

end CensusFamilies
