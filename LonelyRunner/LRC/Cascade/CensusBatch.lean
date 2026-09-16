import LonelyRunner.LRC.Cascade.EighthFamily

/-!
# Census families, emitted

Part of the cascade artefact (`LRC/Cascade/`).  Threshold `1/8`.

Each theorem below takes one census family through `Flanks.lonely_of_flank_unkillable`.
The family data — flank, period, uncovered residues — is the batch machine's own, recomputed
and cross-checked in `experiments/n8/census_export_v1.py`; the Lean is emitted by
`experiments/n8/gen_census_batch_v1.py`.  Every clearance fact reduces to
`Flanks.circDist_ge_of_band`.

Selection: covers with one free parameter, a flank whose killer set is empty on both counts,
and `e/P = 1` so the on-lattice values of the free parameter are the integers.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace CensusBatch

open ConstructionN MomentIterationN Flanks EighthFamily

/-- **Family 1**: differences `{1, 3, 4, 5, 7, x, 8}`, flank `7`, period `7`, uncovered residues `{1, 3}`.  Covers 7 census rows. -/
theorem family1_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 8) :
    ∃ k : ℕ, Lonely 8 ({1, 3, 4, 5, 7, x, 8} : Finset ℝ) (Flanks.flankOpening 8 7 k) := by
  have hq : ((7 : ℕ) : ℝ) * (x / 7) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 7
    {1, 3} ⟨1, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((7 : ℕ) : ℝ) * (d / 7) = d * 7 / 7 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 7 / 7 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (3 : ℝ) * 7 / 7 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (4 : ℝ) * 7 / 7 = ((4 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 4
    · rw [show (5 : ℝ) * 7 / 7 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (7 : ℝ) * 7 / 7 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · exact absurd h hdx
    · rw [show (8 : ℝ) * 7 / 7 = ((8 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 8
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 7 1 = (9 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 7 1 = (27 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 7 1 = (36 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 7 1 = (45 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 1 = (7 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 7 1 = (16 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 7 3 = (25 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 7 3 = (19 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 7 3 = (44 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 7 3 = (13 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 3 = (7 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 7 3 = (32 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 7 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 8 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 8 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (9 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (18 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (27 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (36 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (45 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 7 = 3 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 3 = (38 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (7 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)

/-- **Family 2**: differences `{1, 2, 3, 5, 7, x, 10}`, flank `5`, period `5`, uncovered residues `{1, 3, 4}`.  Covers 6 census rows. -/
theorem family2_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 10) :
    ∃ k : ℕ, Lonely 8 ({1, 2, 3, 5, 7, x, 10} : Finset ℝ) (Flanks.flankOpening 8 5 k) := by
  have hq : ((5 : ℕ) : ℝ) * (x / 5) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 5
    {1, 3, 4} ⟨1, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((5 : ℕ) : ℝ) * (d / 5) = d * 5 / 5 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 5 / 5 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (2 : ℝ) * 5 / 5 = ((2 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 2
    · rw [show (3 : ℝ) * 5 / 5 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (5 : ℝ) * 5 / 5 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (7 : ℝ) * 5 / 5 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · exact absurd h hdx
    · rw [show (10 : ℝ) * 5 / 5 = ((10 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 10
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr <;> subst hr
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
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 5 4 = (33 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 5 4 = (26 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 5 4 = (19 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 5 4 = (5 : ℝ)/40 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 5 4 = (31 : ℝ)/40 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 5 4 = (10 : ℝ)/40 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 9 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 10 := by rw [← hxi]; exact hxM
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

/-- **Family 3**: differences `{1, 3, 4, 5, 7, x, 10}`, flank `5`, period `5`, uncovered residues `{3, 4}`.  Covers 6 census rows. -/
theorem family3_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 10) :
    ∃ k : ℕ, Lonely 8 ({1, 3, 4, 5, 7, x, 10} : Finset ℝ) (Flanks.flankOpening 8 5 k) := by
  have hq : ((5 : ℕ) : ℝ) * (x / 5) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 5
    {3, 4} ⟨3, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((5 : ℕ) : ℝ) * (d / 5) = d * 5 / 5 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 5 / 5 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (3 : ℝ) * 5 / 5 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (4 : ℝ) * 5 / 5 = ((4 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 4
    · rw [show (5 : ℝ) * 5 / 5 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (7 : ℝ) * 5 / 5 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · exact absurd h hdx
    · rw [show (10 : ℝ) * 5 / 5 = ((10 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 10
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 5 3 = (25 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 5 3 = (35 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 5 3 = (20 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
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
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 5 4 = (33 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 5 4 = (19 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 5 4 = (12 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 5 4 = (5 : ℝ)/40 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 5 4 = (31 : ℝ)/40 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 5 4 = (10 : ℝ)/40 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 9 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 10 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 10 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (25 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (10 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (35 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (20 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (5 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (30 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (15 : ℝ)/40 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 5 = 4 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 4 = (24 : ℝ)/40 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (25 : ℝ)/40 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)

/-- **Family 4**: differences `{1, 3, 5, 6, 7, x, 10}`, flank `5`, period `5`, uncovered residues `{1, 3}`.  Covers 6 census rows. -/
theorem family4_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 10) :
    ∃ k : ℕ, Lonely 8 ({1, 3, 5, 6, 7, x, 10} : Finset ℝ) (Flanks.flankOpening 8 5 k) := by
  have hq : ((5 : ℕ) : ℝ) * (x / 5) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 5
    {1, 3} ⟨1, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((5 : ℕ) : ℝ) * (d / 5) = d * 5 / 5 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 5 / 5 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (3 : ℝ) * 5 / 5 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (5 : ℝ) * 5 / 5 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (6 : ℝ) * 5 / 5 = ((6 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 6
    · rw [show (7 : ℝ) * 5 / 5 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · exact absurd h hdx
    · rw [show (10 : ℝ) * 5 / 5 = ((10 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 10
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 5 1 = (9 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 5 1 = (27 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 5 1 = (5 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 5 1 = (14 : ℝ)/40 + ((1 : ℤ) : ℝ) by
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
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 5 3 = (35 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 5 3 = (5 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 5 3 = (30 : ℝ)/40 + ((3 : ℤ) : ℝ) by
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
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 9 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 10 := by rw [← hxi]; exact hxM
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

/-- **Family 5**: differences `{1, 3, 5, 7, 8, x, 10}`, flank `5`, period `5`, uncovered residues `{1, 4}`.  Covers 6 census rows. -/
theorem family5_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 10) :
    ∃ k : ℕ, Lonely 8 ({1, 3, 5, 7, 8, x, 10} : Finset ℝ) (Flanks.flankOpening 8 5 k) := by
  have hq : ((5 : ℕ) : ℝ) * (x / 5) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 5
    {1, 4} ⟨1, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((5 : ℕ) : ℝ) * (d / 5) = d * 5 / 5 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 5 / 5 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (3 : ℝ) * 5 / 5 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (5 : ℝ) * 5 / 5 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (7 : ℝ) * 5 / 5 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (8 : ℝ) * 5 / 5 = ((8 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 8
    · exact absurd h hdx
    · rw [show (10 : ℝ) * 5 / 5 = ((10 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 10
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 5 1 = (9 : ℝ)/40 + ((0 : ℤ) : ℝ) by
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
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 5 1 = (32 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 5 1 = (10 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 5 4 = (33 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 5 4 = (19 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 5 4 = (5 : ℝ)/40 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 5 4 = (31 : ℝ)/40 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 5 4 = (24 : ℝ)/40 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 5 4 = (10 : ℝ)/40 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 9 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 10 := by rw [← hxi]; exact hxM
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
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 5 = 4 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 4 = (12 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
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
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 5 = 4 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 4 = (17 : ℝ)/40 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)

/-- **Family 6**: differences `{1, 3, 4, 5, 7, x, 12}`, flank `7`, period `7`, uncovered residues `{3, 6}`.  Covers 5 census rows. -/
theorem family6_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 12) :
    ∃ k : ℕ, Lonely 8 ({1, 3, 4, 5, 7, x, 12} : Finset ℝ) (Flanks.flankOpening 8 7 k) := by
  have hq : ((7 : ℕ) : ℝ) * (x / 7) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 7
    {3, 6} ⟨3, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((7 : ℕ) : ℝ) * (d / 7) = d * 7 / 7 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 7 / 7 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (3 : ℝ) * 7 / 7 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (4 : ℝ) * 7 / 7 = ((4 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 4
    · rw [show (5 : ℝ) * 7 / 7 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (7 : ℝ) * 7 / 7 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · exact absurd h hdx
    · rw [show (12 : ℝ) * 7 / 7 = ((12 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 12
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 7 3 = (25 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 7 3 = (19 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 7 3 = (44 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 7 3 = (13 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 3 = (7 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 7 3 = (20 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 7 6 = (49 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 7 6 = (35 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 7 6 = (28 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 7 6 = (21 : ℝ)/56 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 6 = (7 : ℝ)/56 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 7 6 = (28 : ℝ)/56 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 11 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 12 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 12 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 7 = 3 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 3 = (25 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 7 = 6 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 6 = (42 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 7 = 3 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 3 = (19 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 7 = 3 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 3 = (44 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 7 = 3 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 3 = (13 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 7 = 3 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 3 = (38 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 7 = 3 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 3 = (7 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 7 = 3 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 3 = (32 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 7 = 6 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 6 = (49 : ℝ)/56 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 7 = 3 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 3 = (26 : ℝ)/56 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 7 = 6 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 6 = (35 : ℝ)/56 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)

/-- **Family 7**: differences `{1, 4, 5, 6, 7, x, 12}`, flank `7`, period `7`, uncovered residues `{2, 3, 6}`.  Covers 5 census rows. -/
theorem family7_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 12) :
    ∃ k : ℕ, Lonely 8 ({1, 4, 5, 6, 7, x, 12} : Finset ℝ) (Flanks.flankOpening 8 7 k) := by
  have hq : ((7 : ℕ) : ℝ) * (x / 7) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 7
    {2, 3, 6} ⟨2, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((7 : ℕ) : ℝ) * (d / 7) = d * 7 / 7 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 7 / 7 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (4 : ℝ) * 7 / 7 = ((4 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 4
    · rw [show (5 : ℝ) * 7 / 7 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (6 : ℝ) * 7 / 7 = ((6 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 6
    · rw [show (7 : ℝ) * 7 / 7 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · exact absurd h hdx
    · rw [show (12 : ℝ) * 7 / 7 = ((12 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 12
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 7 2 = (17 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 7 2 = (12 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 7 2 = (29 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 7 2 = (46 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 2 = (7 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 7 2 = (36 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 7 3 = (25 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 7 3 = (44 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 7 3 = (13 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 7 3 = (38 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 3 = (7 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 7 3 = (20 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 7 6 = (49 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 7 6 = (28 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 7 6 = (21 : ℝ)/56 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 7 6 = (14 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 6 = (7 : ℝ)/56 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 7 6 = (28 : ℝ)/56 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 11 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 12 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 12 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (17 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (34 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 7 = 3 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 3 = (19 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (12 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (29 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (46 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (7 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (24 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (41 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 7 = 3 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 3 = (26 : ℝ)/56 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (19 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)

/-- **Family 8**: differences `{1, 4, 5, 7, 9, x, 12}`, flank `7`, period `7`, uncovered residues `{2, 6}`.  Covers 5 census rows. -/
theorem family8_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 12) :
    ∃ k : ℕ, Lonely 8 ({1, 4, 5, 7, 9, x, 12} : Finset ℝ) (Flanks.flankOpening 8 7 k) := by
  have hq : ((7 : ℕ) : ℝ) * (x / 7) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 7
    {2, 6} ⟨2, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((7 : ℕ) : ℝ) * (d / 7) = d * 7 / 7 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 7 / 7 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (4 : ℝ) * 7 / 7 = ((4 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 4
    · rw [show (5 : ℝ) * 7 / 7 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (7 : ℝ) * 7 / 7 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (9 : ℝ) * 7 / 7 = ((9 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 9
    · exact absurd h hdx
    · rw [show (12 : ℝ) * 7 / 7 = ((12 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 12
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 7 2 = (17 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 7 2 = (12 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 7 2 = (29 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 2 = (7 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (9 : ℝ) * Flanks.flankOpening 8 7 2 = (41 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 7 2 = (36 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 7 6 = (49 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 7 6 = (28 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 7 6 = (21 : ℝ)/56 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 6 = (7 : ℝ)/56 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (9 : ℝ) * Flanks.flankOpening 8 7 6 = (49 : ℝ)/56 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 7 6 = (28 : ℝ)/56 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 11 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 12 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 12 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (17 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (34 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 7 = 6 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 6 = (35 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (12 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (29 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (46 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (7 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (24 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (41 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 7 = 6 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 6 = (42 : ℝ)/56 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (19 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)

/-- **Family 9**: differences `{1, 4, 6, 7, 10, x, 12}`, flank `4`, period `4`, uncovered residues `{2, 3}`.  Covers 5 census rows. -/
theorem family9_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 12) :
    ∃ k : ℕ, Lonely 8 ({1, 4, 6, 7, 10, x, 12} : Finset ℝ) (Flanks.flankOpening 8 4 k) := by
  have hq : ((4 : ℕ) : ℝ) * (x / 4) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 4
    {2, 3} ⟨2, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((4 : ℕ) : ℝ) * (d / 4) = d * 4 / 4 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 4 / 4 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (4 : ℝ) * 4 / 4 = ((4 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 4
    · rw [show (6 : ℝ) * 4 / 4 = ((6 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 6
    · rw [show (7 : ℝ) * 4 / 4 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (10 : ℝ) * 4 / 4 = ((10 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 10
    · exact absurd h hdx
    · rw [show (12 : ℝ) * 4 / 4 = ((12 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 12
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 4 2 = (17 : ℝ)/32 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 4 2 = (4 : ℝ)/32 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 4 2 = (6 : ℝ)/32 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 4 2 = (23 : ℝ)/32 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 4 2 = (10 : ℝ)/32 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 4 2 = (12 : ℝ)/32 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 4 3 = (25 : ℝ)/32 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 4 3 = (4 : ℝ)/32 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 4 3 = (22 : ℝ)/32 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 4 3 = (15 : ℝ)/32 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 4 3 = (26 : ℝ)/32 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 4 3 = (12 : ℝ)/32 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 11 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 12 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 12 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 4 = 2 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 2 = (17 : ℝ)/32 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 4 = 3 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 3 = (18 : ℝ)/32 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 4 = 2 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 2 = (19 : ℝ)/32 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 4 = 2 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 2 = (4 : ℝ)/32 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 4 = 2 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 2 = (21 : ℝ)/32 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 4 = 2 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 2 = (6 : ℝ)/32 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 4 = 2 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 2 = (23 : ℝ)/32 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 4 = 2 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 2 = (8 : ℝ)/32 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 4 = 2 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 2 = (25 : ℝ)/32 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 4 = 2 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 2 = (10 : ℝ)/32 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 4 = 2 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 2 = (27 : ℝ)/32 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)

/-- **Family 10**: differences `{1, 5, 6, 7, 8, x, 12}`, flank `6`, period `6`, uncovered residues `{2, 3, 4}`.  Covers 5 census rows. -/
theorem family10_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 12) :
    ∃ k : ℕ, Lonely 8 ({1, 5, 6, 7, 8, x, 12} : Finset ℝ) (Flanks.flankOpening 8 6 k) := by
  have hq : ((6 : ℕ) : ℝ) * (x / 6) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 6
    {2, 3, 4} ⟨2, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((6 : ℕ) : ℝ) * (d / 6) = d * 6 / 6 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 6 / 6 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (5 : ℝ) * 6 / 6 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (6 : ℝ) * 6 / 6 = ((6 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 6
    · rw [show (7 : ℝ) * 6 / 6 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (8 : ℝ) * 6 / 6 = ((8 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 8
    · exact absurd h hdx
    · rw [show (12 : ℝ) * 6 / 6 = ((12 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 12
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 6 2 = (17 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 6 2 = (37 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 6 2 = (6 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 6 2 = (23 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 6 2 = (40 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 6 2 = (12 : ℝ)/48 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 6 3 = (25 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 6 3 = (29 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 6 3 = (6 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 6 3 = (31 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 6 3 = (8 : ℝ)/48 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 6 3 = (12 : ℝ)/48 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 6 4 = (33 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 6 4 = (21 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 6 4 = (6 : ℝ)/48 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 6 4 = (39 : ℝ)/48 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 6 4 = (24 : ℝ)/48 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 6 4 = (12 : ℝ)/48 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 11 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 12 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 12 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (17 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (34 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 6 = 3 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 3 = (27 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (20 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (37 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (6 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (23 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (40 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (9 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (26 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 6 = 3 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 3 = (35 : ℝ)/48 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)

/-- **Family 11**: differences `{1, 5, 7, 8, 9, x, 12}`, flank `7`, period `7`, uncovered residues `{2, 5}`.  Covers 5 census rows. -/
theorem family11_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 12) :
    ∃ k : ℕ, Lonely 8 ({1, 5, 7, 8, 9, x, 12} : Finset ℝ) (Flanks.flankOpening 8 7 k) := by
  have hq : ((7 : ℕ) : ℝ) * (x / 7) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 7
    {2, 5} ⟨2, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((7 : ℕ) : ℝ) * (d / 7) = d * 7 / 7 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 7 / 7 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (5 : ℝ) * 7 / 7 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (7 : ℝ) * 7 / 7 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (8 : ℝ) * 7 / 7 = ((8 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 8
    · rw [show (9 : ℝ) * 7 / 7 = ((9 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 9
    · exact absurd h hdx
    · rw [show (12 : ℝ) * 7 / 7 = ((12 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 12
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 7 2 = (17 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 7 2 = (29 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 2 = (7 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 7 2 = (24 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (9 : ℝ) * Flanks.flankOpening 8 7 2 = (41 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 7 2 = (36 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 7 5 = (41 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 7 5 = (37 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 5 = (7 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 7 5 = (48 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (9 : ℝ) * Flanks.flankOpening 8 7 5 = (33 : ℝ)/56 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 7 5 = (44 : ℝ)/56 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 11 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 12 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 12 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (17 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (34 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (11 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (12 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (29 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (46 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (7 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (24 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (41 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (18 : ℝ)/56 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (19 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)

/-- **Family 12**: differences `{1, 6, 7, 8, 10, x, 12}`, flank `6`, period `6`, uncovered residues `{1, 2, 3, 4}`.  Covers 5 census rows. -/
theorem family12_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 12) :
    ∃ k : ℕ, Lonely 8 ({1, 6, 7, 8, 10, x, 12} : Finset ℝ) (Flanks.flankOpening 8 6 k) := by
  have hq : ((6 : ℕ) : ℝ) * (x / 6) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 6
    {1, 2, 3, 4} ⟨1, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((6 : ℕ) : ℝ) * (d / 6) = d * 6 / 6 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 6 / 6 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (6 : ℝ) * 6 / 6 = ((6 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 6
    · rw [show (7 : ℝ) * 6 / 6 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (8 : ℝ) * 6 / 6 = ((8 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 8
    · rw [show (10 : ℝ) * 6 / 6 = ((10 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 10
    · exact absurd h hdx
    · rw [show (12 : ℝ) * 6 / 6 = ((12 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 12
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 6 1 = (9 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 6 1 = (6 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 6 1 = (15 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 6 1 = (24 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 6 1 = (42 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 6 1 = (12 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 6 2 = (17 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 6 2 = (6 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 6 2 = (23 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 6 2 = (40 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 6 2 = (26 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 6 2 = (12 : ℝ)/48 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 6 3 = (25 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 6 3 = (6 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 6 3 = (31 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 6 3 = (8 : ℝ)/48 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 6 3 = (10 : ℝ)/48 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 6 3 = (12 : ℝ)/48 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 6 4 = (33 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 6 4 = (6 : ℝ)/48 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 6 4 = (39 : ℝ)/48 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 6 4 = (24 : ℝ)/48 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 6 4 = (42 : ℝ)/48 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 6 4 = (12 : ℝ)/48 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 11 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 12 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 12 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (9 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (18 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (27 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (36 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (37 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (6 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (15 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (24 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (33 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (42 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 6 = 3 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 3 = (35 : ℝ)/48 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)

/-- **Family 13**: differences `{1, 2, 3, 5, 7, x, 14}`, flank `5`, period `5`, uncovered residues `{1, 3, 4}`.  Covers 4 census rows. -/
theorem family13_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 14) :
    ∃ k : ℕ, Lonely 8 ({1, 2, 3, 5, 7, x, 14} : Finset ℝ) (Flanks.flankOpening 8 5 k) := by
  have hq : ((5 : ℕ) : ℝ) * (x / 5) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 5
    {1, 3, 4} ⟨1, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((5 : ℕ) : ℝ) * (d / 5) = d * 5 / 5 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 5 / 5 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (2 : ℝ) * 5 / 5 = ((2 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 2
    · rw [show (3 : ℝ) * 5 / 5 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (5 : ℝ) * 5 / 5 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (7 : ℝ) * 5 / 5 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · exact absurd h hdx
    · rw [show (14 : ℝ) * 5 / 5 = ((14 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 14
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr <;> subst hr
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
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 5 1 = (6 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
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
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 5 3 = (30 : ℝ)/40 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 5 4 = (33 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 5 4 = (26 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 5 4 = (19 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 5 4 = (5 : ℝ)/40 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 5 4 = (31 : ℝ)/40 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 5 4 = (22 : ℝ)/40 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 13 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 14 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 14 := by exact_mod_cast hh
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
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (10 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (19 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (28 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (5 : ℝ)/40 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)

/-- **Family 14**: differences `{1, 3, 4, 5, 7, x, 14}`, flank `5`, period `5`, uncovered residues `{3, 4}`.  Covers 4 census rows. -/
theorem family14_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 14) :
    ∃ k : ℕ, Lonely 8 ({1, 3, 4, 5, 7, x, 14} : Finset ℝ) (Flanks.flankOpening 8 5 k) := by
  have hq : ((5 : ℕ) : ℝ) * (x / 5) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 5
    {3, 4} ⟨3, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((5 : ℕ) : ℝ) * (d / 5) = d * 5 / 5 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 5 / 5 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (3 : ℝ) * 5 / 5 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (4 : ℝ) * 5 / 5 = ((4 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 4
    · rw [show (5 : ℝ) * 5 / 5 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (7 : ℝ) * 5 / 5 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · exact absurd h hdx
    · rw [show (14 : ℝ) * 5 / 5 = ((14 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 14
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 5 3 = (25 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 5 3 = (35 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 5 3 = (20 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 5 3 = (5 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 5 3 = (15 : ℝ)/40 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 5 3 = (30 : ℝ)/40 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 5 4 = (33 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 5 4 = (19 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 5 4 = (12 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 5 4 = (5 : ℝ)/40 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 5 4 = (31 : ℝ)/40 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 5 4 = (22 : ℝ)/40 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 13 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 14 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 14 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (25 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (10 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (35 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (20 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (5 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (30 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (15 : ℝ)/40 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 5 = 4 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 4 = (24 : ℝ)/40 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (25 : ℝ)/40 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (10 : ℝ)/40 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (35 : ℝ)/40 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (20 : ℝ)/40 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (5 : ℝ)/40 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)

/-- **Family 15**: differences `{1, 3, 4, 7, 10, x, 14}`, flank `7`, period `7`, uncovered residues `{1, 3, 6}`.  Covers 4 census rows. -/
theorem family15_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 14) :
    ∃ k : ℕ, Lonely 8 ({1, 3, 4, 7, 10, x, 14} : Finset ℝ) (Flanks.flankOpening 8 7 k) := by
  have hq : ((7 : ℕ) : ℝ) * (x / 7) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 7
    {1, 3, 6} ⟨1, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((7 : ℕ) : ℝ) * (d / 7) = d * 7 / 7 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 7 / 7 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (3 : ℝ) * 7 / 7 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (4 : ℝ) * 7 / 7 = ((4 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 4
    · rw [show (7 : ℝ) * 7 / 7 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (10 : ℝ) * 7 / 7 = ((10 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 10
    · exact absurd h hdx
    · rw [show (14 : ℝ) * 7 / 7 = ((14 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 14
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 7 1 = (9 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 7 1 = (27 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 7 1 = (36 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 1 = (7 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 7 1 = (34 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 7 1 = (14 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 7 3 = (25 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 7 3 = (19 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 7 3 = (44 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 3 = (7 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 7 3 = (26 : ℝ)/56 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 7 3 = (14 : ℝ)/56 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 7 6 = (49 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 7 6 = (35 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 7 6 = (28 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 6 = (7 : ℝ)/56 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 7 6 = (42 : ℝ)/56 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 7 6 = (14 : ℝ)/56 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 13 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 14 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 14 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (9 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (18 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (27 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (36 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (45 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 7 = 3 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 3 = (38 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (7 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (16 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (25 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (34 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (43 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 7 = 3 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 3 = (20 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 7 = 3 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 3 = (45 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)

/-- **Family 16**: differences `{1, 3, 5, 6, 7, x, 14}`, flank `5`, period `5`, uncovered residues `{1, 3}`.  Covers 4 census rows. -/
theorem family16_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 14) :
    ∃ k : ℕ, Lonely 8 ({1, 3, 5, 6, 7, x, 14} : Finset ℝ) (Flanks.flankOpening 8 5 k) := by
  have hq : ((5 : ℕ) : ℝ) * (x / 5) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 5
    {1, 3} ⟨1, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((5 : ℕ) : ℝ) * (d / 5) = d * 5 / 5 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 5 / 5 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (3 : ℝ) * 5 / 5 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (5 : ℝ) * 5 / 5 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (6 : ℝ) * 5 / 5 = ((6 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 6
    · rw [show (7 : ℝ) * 5 / 5 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · exact absurd h hdx
    · rw [show (14 : ℝ) * 5 / 5 = ((14 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 14
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 5 1 = (9 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 5 1 = (27 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 5 1 = (5 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 5 1 = (14 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 5 1 = (23 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 5 1 = (6 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 5 3 = (25 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 5 3 = (35 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 5 3 = (5 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 5 3 = (30 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 5 3 = (15 : ℝ)/40 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 5 3 = (30 : ℝ)/40 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 13 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 14 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 14 := by exact_mod_cast hh
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
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (10 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (19 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (28 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (5 : ℝ)/40 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)

/-- **Family 17**: differences `{1, 3, 5, 7, 8, x, 14}`, flank `5`, period `5`, uncovered residues `{1, 4}`.  Covers 4 census rows. -/
theorem family17_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 14) :
    ∃ k : ℕ, Lonely 8 ({1, 3, 5, 7, 8, x, 14} : Finset ℝ) (Flanks.flankOpening 8 5 k) := by
  have hq : ((5 : ℕ) : ℝ) * (x / 5) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 5
    {1, 4} ⟨1, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((5 : ℕ) : ℝ) * (d / 5) = d * 5 / 5 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 5 / 5 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (3 : ℝ) * 5 / 5 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (5 : ℝ) * 5 / 5 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (7 : ℝ) * 5 / 5 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (8 : ℝ) * 5 / 5 = ((8 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 8
    · exact absurd h hdx
    · rw [show (14 : ℝ) * 5 / 5 = ((14 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 14
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 5 1 = (9 : ℝ)/40 + ((0 : ℤ) : ℝ) by
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
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 5 1 = (32 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 5 1 = (6 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 5 4 = (33 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 5 4 = (19 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 5 4 = (5 : ℝ)/40 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 5 4 = (31 : ℝ)/40 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 5 4 = (24 : ℝ)/40 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 5 4 = (22 : ℝ)/40 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 13 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 14 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 14 := by exact_mod_cast hh
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
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 5 = 4 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 4 = (12 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
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
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 5 = 4 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 4 = (17 : ℝ)/40 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (10 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (19 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (28 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 5 = 4 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 4 = (29 : ℝ)/40 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)

/-- **Family 18**: differences `{1, 3, 5, 7, 10, x, 14}`, flank `5`, period `5`, uncovered residues `{1, 3, 4}`.  Covers 4 census rows. -/
theorem family18_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 14) :
    ∃ k : ℕ, Lonely 8 ({1, 3, 5, 7, 10, x, 14} : Finset ℝ) (Flanks.flankOpening 8 5 k) := by
  have hq : ((5 : ℕ) : ℝ) * (x / 5) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 5
    {1, 3, 4} ⟨1, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((5 : ℕ) : ℝ) * (d / 5) = d * 5 / 5 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 5 / 5 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (3 : ℝ) * 5 / 5 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (5 : ℝ) * 5 / 5 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (7 : ℝ) * 5 / 5 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (10 : ℝ) * 5 / 5 = ((10 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 10
    · exact absurd h hdx
    · rw [show (14 : ℝ) * 5 / 5 = ((14 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 14
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 5 1 = (9 : ℝ)/40 + ((0 : ℤ) : ℝ) by
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
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 5 1 = (10 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 5 1 = (6 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 5 3 = (25 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 5 3 = (35 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 5 3 = (5 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 5 3 = (15 : ℝ)/40 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 5 3 = (10 : ℝ)/40 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 5 3 = (30 : ℝ)/40 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 5 4 = (33 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 5 4 = (19 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 5 4 = (5 : ℝ)/40 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 5 4 = (31 : ℝ)/40 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 5 4 = (10 : ℝ)/40 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 5 4 = (22 : ℝ)/40 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 13 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 14 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 14 := by exact_mod_cast hh
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
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (10 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (19 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (28 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (5 : ℝ)/40 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)

/-- **Family 19**: differences `{1, 3, 5, 7, 12, x, 14}`, flank `5`, period `5`, uncovered residues `{1, 3}`.  Covers 4 census rows. -/
theorem family19_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 14) :
    ∃ k : ℕ, Lonely 8 ({1, 3, 5, 7, 12, x, 14} : Finset ℝ) (Flanks.flankOpening 8 5 k) := by
  have hq : ((5 : ℕ) : ℝ) * (x / 5) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 5
    {1, 3} ⟨1, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((5 : ℕ) : ℝ) * (d / 5) = d * 5 / 5 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 5 / 5 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (3 : ℝ) * 5 / 5 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (5 : ℝ) * 5 / 5 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (7 : ℝ) * 5 / 5 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (12 : ℝ) * 5 / 5 = ((12 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 12
    · exact absurd h hdx
    · rw [show (14 : ℝ) * 5 / 5 = ((14 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 14
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 5 1 = (9 : ℝ)/40 + ((0 : ℤ) : ℝ) by
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
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 5 1 = (28 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 5 1 = (6 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 5 3 = (25 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 5 3 = (35 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 5 3 = (5 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 5 3 = (15 : ℝ)/40 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 5 3 = (20 : ℝ)/40 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 5 3 = (30 : ℝ)/40 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 13 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 14 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 14 := by exact_mod_cast hh
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
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (10 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (19 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (28 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (5 : ℝ)/40 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)

/-- **Family 20**: differences `{1, 3, 7, 9, 10, x, 14}`, flank `7`, period `7`, uncovered residues `{1, 5, 6}`.  Covers 4 census rows. -/
theorem family20_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 14) :
    ∃ k : ℕ, Lonely 8 ({1, 3, 7, 9, 10, x, 14} : Finset ℝ) (Flanks.flankOpening 8 7 k) := by
  have hq : ((7 : ℕ) : ℝ) * (x / 7) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 7
    {1, 5, 6} ⟨1, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((7 : ℕ) : ℝ) * (d / 7) = d * 7 / 7 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 7 / 7 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (3 : ℝ) * 7 / 7 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (7 : ℝ) * 7 / 7 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (9 : ℝ) * 7 / 7 = ((9 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 9
    · rw [show (10 : ℝ) * 7 / 7 = ((10 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 10
    · exact absurd h hdx
    · rw [show (14 : ℝ) * 7 / 7 = ((14 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 14
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 7 1 = (9 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 7 1 = (27 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 1 = (7 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (9 : ℝ) * Flanks.flankOpening 8 7 1 = (25 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 7 1 = (34 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 7 1 = (14 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 7 5 = (41 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 7 5 = (11 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 5 = (7 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (9 : ℝ) * Flanks.flankOpening 8 7 5 = (33 : ℝ)/56 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 7 5 = (18 : ℝ)/56 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 7 5 = (14 : ℝ)/56 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 7 6 = (49 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 7 6 = (35 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 6 = (7 : ℝ)/56 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (9 : ℝ) * Flanks.flankOpening 8 7 6 = (49 : ℝ)/56 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 7 6 = (42 : ℝ)/56 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 7 6 = (14 : ℝ)/56 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 13 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 14 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 14 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (9 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (18 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (27 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (36 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (45 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (22 : ℝ)/56 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (7 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (16 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (25 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (34 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (43 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (44 : ℝ)/56 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (29 : ℝ)/56 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)

/-- **Family 21**: differences `{1, 3, 7, 10, 13, x, 14}`, flank `7`, period `7`, uncovered residues `{3, 5, 6}`.  Covers 4 census rows. -/
theorem family21_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 14) :
    ∃ k : ℕ, Lonely 8 ({1, 3, 7, 10, 13, x, 14} : Finset ℝ) (Flanks.flankOpening 8 7 k) := by
  have hq : ((7 : ℕ) : ℝ) * (x / 7) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 7
    {3, 5, 6} ⟨3, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((7 : ℕ) : ℝ) * (d / 7) = d * 7 / 7 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 7 / 7 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (3 : ℝ) * 7 / 7 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (7 : ℝ) * 7 / 7 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (10 : ℝ) * 7 / 7 = ((10 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 10
    · rw [show (13 : ℝ) * 7 / 7 = ((13 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 13
    · exact absurd h hdx
    · rw [show (14 : ℝ) * 7 / 7 = ((14 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 14
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 7 3 = (25 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 7 3 = (19 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 3 = (7 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 7 3 = (26 : ℝ)/56 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (13 : ℝ) * Flanks.flankOpening 8 7 3 = (45 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 7 3 = (14 : ℝ)/56 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 7 5 = (41 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 7 5 = (11 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 5 = (7 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 7 5 = (18 : ℝ)/56 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (13 : ℝ) * Flanks.flankOpening 8 7 5 = (29 : ℝ)/56 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 7 5 = (14 : ℝ)/56 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 7 6 = (49 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 7 6 = (35 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 6 = (7 : ℝ)/56 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 7 6 = (42 : ℝ)/56 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (13 : ℝ) * Flanks.flankOpening 8 7 6 = (21 : ℝ)/56 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 7 6 = (14 : ℝ)/56 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 13 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 14 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 14 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 7 = 3 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 3 = (25 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (26 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 7 = 3 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 3 = (19 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 7 = 3 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 3 = (44 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 7 = 3 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 3 = (13 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 7 = 3 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 3 = (38 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 7 = 3 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 3 = (7 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 7 = 3 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 3 = (32 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (33 : ℝ)/56 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 7 = 3 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 3 = (26 : ℝ)/56 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 7 = 6 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 6 = (35 : ℝ)/56 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 7 = 3 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 3 = (20 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 7 = 3 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 3 = (45 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)

/-- **Family 22**: differences `{1, 5, 6, 7, 8, x, 14}`, flank `6`, period `6`, uncovered residues `{3, 4}`.  Covers 4 census rows. -/
theorem family22_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 14) :
    ∃ k : ℕ, Lonely 8 ({1, 5, 6, 7, 8, x, 14} : Finset ℝ) (Flanks.flankOpening 8 6 k) := by
  have hq : ((6 : ℕ) : ℝ) * (x / 6) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 6
    {3, 4} ⟨3, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((6 : ℕ) : ℝ) * (d / 6) = d * 6 / 6 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 6 / 6 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (5 : ℝ) * 6 / 6 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (6 : ℝ) * 6 / 6 = ((6 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 6
    · rw [show (7 : ℝ) * 6 / 6 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (8 : ℝ) * 6 / 6 = ((8 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 8
    · exact absurd h hdx
    · rw [show (14 : ℝ) * 6 / 6 = ((14 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 14
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 6 3 = (25 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 6 3 = (29 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 6 3 = (6 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 6 3 = (31 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 6 3 = (8 : ℝ)/48 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 6 3 = (14 : ℝ)/48 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 6 4 = (33 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 6 4 = (21 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 6 4 = (6 : ℝ)/48 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 6 4 = (39 : ℝ)/48 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 6 4 = (24 : ℝ)/48 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 6 4 = (30 : ℝ)/48 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 13 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 14 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 14 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 6 = 3 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 3 = (25 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 6 = 4 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 4 = (18 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 6 = 3 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 3 = (27 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 6 = 4 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 4 = (36 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 6 = 3 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 3 = (29 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 6 = 3 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 3 = (6 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 6 = 3 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 3 = (31 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 6 = 3 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 3 = (8 : ℝ)/48 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 6 = 3 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 3 = (33 : ℝ)/48 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 6 = 3 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 3 = (10 : ℝ)/48 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 6 = 3 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 3 = (35 : ℝ)/48 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 6 = 3 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 3 = (12 : ℝ)/48 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 6 = 3 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 3 = (37 : ℝ)/48 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)

/-- **Family 23**: differences `{1, 5, 6, 7, 11, x, 14}`, flank `5`, period `5`, uncovered residues `{1, 3}`.  Covers 4 census rows. -/
theorem family23_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 14) :
    ∃ k : ℕ, Lonely 8 ({1, 5, 6, 7, 11, x, 14} : Finset ℝ) (Flanks.flankOpening 8 5 k) := by
  have hq : ((5 : ℕ) : ℝ) * (x / 5) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 5
    {1, 3} ⟨1, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((5 : ℕ) : ℝ) * (d / 5) = d * 5 / 5 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 5 / 5 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (5 : ℝ) * 5 / 5 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (6 : ℝ) * 5 / 5 = ((6 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 6
    · rw [show (7 : ℝ) * 5 / 5 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (11 : ℝ) * 5 / 5 = ((11 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 11
    · exact absurd h hdx
    · rw [show (14 : ℝ) * 5 / 5 = ((14 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 14
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 5 1 = (9 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 5 1 = (5 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 5 1 = (14 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 5 1 = (23 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (11 : ℝ) * Flanks.flankOpening 8 5 1 = (19 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 5 1 = (6 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 5 3 = (25 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 5 3 = (5 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 5 3 = (30 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 5 3 = (15 : ℝ)/40 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (11 : ℝ) * Flanks.flankOpening 8 5 3 = (35 : ℝ)/40 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 5 3 = (30 : ℝ)/40 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 13 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 14 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 14 := by exact_mod_cast hh
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
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (10 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (19 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (28 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (5 : ℝ)/40 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)

/-- **Family 24**: differences `{2, 5, 7, 8, 12, x, 15}`, flank `8`, period `8`, uncovered residues `{5, 6, 7}`.  Covers 4 census rows. -/
theorem family24_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 15) :
    ∃ k : ℕ, Lonely 8 ({2, 5, 7, 8, 12, x, 15} : Finset ℝ) (Flanks.flankOpening 8 8 k) := by
  have hq : ((8 : ℕ) : ℝ) * (x / 8) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 8
    {5, 6, 7} ⟨5, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((8 : ℕ) : ℝ) * (d / 8) = d * 8 / 8 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (2 : ℝ) * 8 / 8 = ((2 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 2
    · rw [show (5 : ℝ) * 8 / 8 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (7 : ℝ) * 8 / 8 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (8 : ℝ) * 8 / 8 = ((8 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 8
    · rw [show (12 : ℝ) * 8 / 8 = ((12 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 12
    · exact absurd h hdx
    · rw [show (15 : ℝ) * 8 / 8 = ((15 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 15
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 8 5 = (18 : ℝ)/64 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 8 5 = (13 : ℝ)/64 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 8 5 = (31 : ℝ)/64 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 8 5 = (8 : ℝ)/64 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 8 5 = (44 : ℝ)/64 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (15 : ℝ) * Flanks.flankOpening 8 8 5 = (39 : ℝ)/64 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 8 6 = (34 : ℝ)/64 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 8 6 = (53 : ℝ)/64 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 8 6 = (23 : ℝ)/64 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 8 6 = (8 : ℝ)/64 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 8 6 = (12 : ℝ)/64 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (15 : ℝ) * Flanks.flankOpening 8 8 6 = (31 : ℝ)/64 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 8 7 = (50 : ℝ)/64 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 8 7 = (29 : ℝ)/64 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 8 7 = (15 : ℝ)/64 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 8 7 = (8 : ℝ)/64 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 8 7 = (44 : ℝ)/64 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (15 : ℝ) * Flanks.flankOpening 8 8 7 = (23 : ℝ)/64 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 14 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 15 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 15 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 8 = 5 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 5 = (41 : ℝ)/64 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 8 = 5 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 5 = (18 : ℝ)/64 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 8 = 6 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 6 = (19 : ℝ)/64 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 8 = 5 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 5 = (36 : ℝ)/64 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 8 = 5 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 5 = (13 : ℝ)/64 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 8 = 5 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 5 = (54 : ℝ)/64 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 8 = 5 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 5 = (31 : ℝ)/64 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 8 = 5 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 5 = (8 : ℝ)/64 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 8 = 5 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 5 = (49 : ℝ)/64 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 8 = 5 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 5 = (26 : ℝ)/64 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 8 = 6 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 6 = (27 : ℝ)/64 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 8 = 5 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 5 = (44 : ℝ)/64 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 8 = 5 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 5 = (21 : ℝ)/64 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 8 = 6 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 6 = (46 : ℝ)/64 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)

/-- **Family 25**: differences `{2, 7, 8, 10, 12, x, 15}`, flank `8`, period `8`, uncovered residues `{5, 6}`.  Covers 4 census rows. -/
theorem family25_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 15) :
    ∃ k : ℕ, Lonely 8 ({2, 7, 8, 10, 12, x, 15} : Finset ℝ) (Flanks.flankOpening 8 8 k) := by
  have hq : ((8 : ℕ) : ℝ) * (x / 8) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 8
    {5, 6} ⟨5, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((8 : ℕ) : ℝ) * (d / 8) = d * 8 / 8 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (2 : ℝ) * 8 / 8 = ((2 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 2
    · rw [show (7 : ℝ) * 8 / 8 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (8 : ℝ) * 8 / 8 = ((8 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 8
    · rw [show (10 : ℝ) * 8 / 8 = ((10 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 10
    · rw [show (12 : ℝ) * 8 / 8 = ((12 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 12
    · exact absurd h hdx
    · rw [show (15 : ℝ) * 8 / 8 = ((15 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 15
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 8 5 = (18 : ℝ)/64 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 8 5 = (31 : ℝ)/64 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 8 5 = (8 : ℝ)/64 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 8 5 = (26 : ℝ)/64 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 8 5 = (44 : ℝ)/64 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (15 : ℝ) * Flanks.flankOpening 8 8 5 = (39 : ℝ)/64 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 8 6 = (34 : ℝ)/64 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 8 6 = (23 : ℝ)/64 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 8 6 = (8 : ℝ)/64 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 8 6 = (42 : ℝ)/64 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 8 6 = (12 : ℝ)/64 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (15 : ℝ) * Flanks.flankOpening 8 8 6 = (31 : ℝ)/64 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 14 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 15 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 15 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 8 = 5 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 5 = (41 : ℝ)/64 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 8 = 5 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 5 = (18 : ℝ)/64 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 8 = 6 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 6 = (19 : ℝ)/64 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 8 = 5 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 5 = (36 : ℝ)/64 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 8 = 5 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 5 = (13 : ℝ)/64 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 8 = 5 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 5 = (54 : ℝ)/64 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 8 = 5 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 5 = (31 : ℝ)/64 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 8 = 5 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 5 = (8 : ℝ)/64 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 8 = 5 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 5 = (49 : ℝ)/64 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 8 = 5 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 5 = (26 : ℝ)/64 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 8 = 6 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 6 = (27 : ℝ)/64 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 8 = 5 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 5 = (44 : ℝ)/64 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 8 = 5 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 5 = (21 : ℝ)/64 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 8 = 6 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 6 = (46 : ℝ)/64 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)

/-- **Family 26**: differences `{1, 3, 4, 5, 7, x, 16}`, flank `7`, period `7`, uncovered residues `{1, 3}`.  Covers 3 census rows. -/
theorem family26_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 16) :
    ∃ k : ℕ, Lonely 8 ({1, 3, 4, 5, 7, x, 16} : Finset ℝ) (Flanks.flankOpening 8 7 k) := by
  have hq : ((7 : ℕ) : ℝ) * (x / 7) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 7
    {1, 3} ⟨1, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((7 : ℕ) : ℝ) * (d / 7) = d * 7 / 7 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 7 / 7 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (3 : ℝ) * 7 / 7 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (4 : ℝ) * 7 / 7 = ((4 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 4
    · rw [show (5 : ℝ) * 7 / 7 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (7 : ℝ) * 7 / 7 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · exact absurd h hdx
    · rw [show (16 : ℝ) * 7 / 7 = ((16 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 16
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 7 1 = (9 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 7 1 = (27 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 7 1 = (36 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 7 1 = (45 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 1 = (7 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 7 1 = (32 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 7 3 = (25 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 7 3 = (19 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 7 3 = (44 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 7 3 = (13 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 3 = (7 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 7 3 = (8 : ℝ)/56 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 15 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 16 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 16 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (9 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (18 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (27 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (36 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (45 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 7 = 3 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 3 = (38 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (7 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (16 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (25 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (34 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (43 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 7 = 3 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 3 = (20 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 7 = 3 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 3 = (45 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (14 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (23 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)

/-- **Family 27**: differences `{1, 3, 5, 7, 8, x, 16}`, flank `5`, period `5`, uncovered residues `{1, 4}`.  Covers 3 census rows. -/
theorem family27_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 16) :
    ∃ k : ℕ, Lonely 8 ({1, 3, 5, 7, 8, x, 16} : Finset ℝ) (Flanks.flankOpening 8 5 k) := by
  have hq : ((5 : ℕ) : ℝ) * (x / 5) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 5
    {1, 4} ⟨1, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((5 : ℕ) : ℝ) * (d / 5) = d * 5 / 5 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 5 / 5 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (3 : ℝ) * 5 / 5 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (5 : ℝ) * 5 / 5 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (7 : ℝ) * 5 / 5 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (8 : ℝ) * 5 / 5 = ((8 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 8
    · exact absurd h hdx
    · rw [show (16 : ℝ) * 5 / 5 = ((16 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 16
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 5 1 = (9 : ℝ)/40 + ((0 : ℤ) : ℝ) by
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
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 5 1 = (32 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 5 1 = (24 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 5 4 = (33 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 5 4 = (19 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 5 4 = (5 : ℝ)/40 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 5 4 = (31 : ℝ)/40 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 5 4 = (24 : ℝ)/40 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 5 4 = (8 : ℝ)/40 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 15 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 16 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 16 := by exact_mod_cast hh
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
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 5 = 4 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 4 = (12 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
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
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 5 = 4 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 4 = (17 : ℝ)/40 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (10 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (19 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (28 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 5 = 4 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 4 = (29 : ℝ)/40 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (6 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (15 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)

/-- **Family 28**: differences `{1, 6, 7, 8, 10, x, 16}`, flank `6`, period `6`, uncovered residues `{2, 3}`.  Covers 3 census rows. -/
theorem family28_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 16) :
    ∃ k : ℕ, Lonely 8 ({1, 6, 7, 8, 10, x, 16} : Finset ℝ) (Flanks.flankOpening 8 6 k) := by
  have hq : ((6 : ℕ) : ℝ) * (x / 6) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 6
    {2, 3} ⟨2, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((6 : ℕ) : ℝ) * (d / 6) = d * 6 / 6 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 6 / 6 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (6 : ℝ) * 6 / 6 = ((6 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 6
    · rw [show (7 : ℝ) * 6 / 6 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (8 : ℝ) * 6 / 6 = ((8 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 8
    · rw [show (10 : ℝ) * 6 / 6 = ((10 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 10
    · exact absurd h hdx
    · rw [show (16 : ℝ) * 6 / 6 = ((16 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 16
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 6 2 = (17 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 6 2 = (6 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 6 2 = (23 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 6 2 = (40 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 6 2 = (26 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 6 2 = (32 : ℝ)/48 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 6 3 = (25 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 6 3 = (6 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 6 3 = (31 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 6 3 = (8 : ℝ)/48 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 6 3 = (10 : ℝ)/48 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 6 3 = (16 : ℝ)/48 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 15 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 16 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 16 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (17 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (34 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 6 = 3 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 3 = (27 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (20 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (37 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (6 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (23 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (40 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (9 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (26 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 6 = 3 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 3 = (35 : ℝ)/48 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (12 : ℝ)/48 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (29 : ℝ)/48 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 6 = 3 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 3 = (14 : ℝ)/48 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (15 : ℝ)/48 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)

/-- **Family 29**: differences `{2, 3, 5, 8, 14, x, 16}`, flank `5`, period `5`, uncovered residues `{1, 4}`.  Covers 3 census rows. -/
theorem family29_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 16) :
    ∃ k : ℕ, Lonely 8 ({2, 3, 5, 8, 14, x, 16} : Finset ℝ) (Flanks.flankOpening 8 5 k) := by
  have hq : ((5 : ℕ) : ℝ) * (x / 5) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 5
    {1, 4} ⟨1, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((5 : ℕ) : ℝ) * (d / 5) = d * 5 / 5 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (2 : ℝ) * 5 / 5 = ((2 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 2
    · rw [show (3 : ℝ) * 5 / 5 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (5 : ℝ) * 5 / 5 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (8 : ℝ) * 5 / 5 = ((8 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 8
    · rw [show (14 : ℝ) * 5 / 5 = ((14 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 14
    · exact absurd h hdx
    · rw [show (16 : ℝ) * 5 / 5 = ((16 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 16
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 5 1 = (18 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 5 1 = (27 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 5 1 = (5 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 5 1 = (32 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 5 1 = (6 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 5 1 = (24 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 5 4 = (26 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 5 4 = (19 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 5 4 = (5 : ℝ)/40 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 5 4 = (24 : ℝ)/40 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 5 4 = (22 : ℝ)/40 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 5 4 = (8 : ℝ)/40 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 15 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 16 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 16 := by exact_mod_cast hh
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
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 5 = 4 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 4 = (12 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
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
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 5 = 4 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 4 = (17 : ℝ)/40 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (10 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (19 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (28 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 5 = 4 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 4 = (29 : ℝ)/40 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (6 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (15 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)

/-- **Family 30**: differences `{1, 5, 6, 7, 9, x, 18}`, flank `6`, period `6`, uncovered residues `{2, 3, 4}`.  Covers 3 census rows. -/
theorem family30_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 18) :
    ∃ k : ℕ, Lonely 8 ({1, 5, 6, 7, 9, x, 18} : Finset ℝ) (Flanks.flankOpening 8 6 k) := by
  have hq : ((6 : ℕ) : ℝ) * (x / 6) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 6
    {2, 3, 4} ⟨2, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((6 : ℕ) : ℝ) * (d / 6) = d * 6 / 6 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 6 / 6 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (5 : ℝ) * 6 / 6 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (6 : ℝ) * 6 / 6 = ((6 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 6
    · rw [show (7 : ℝ) * 6 / 6 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (9 : ℝ) * 6 / 6 = ((9 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 9
    · exact absurd h hdx
    · rw [show (18 : ℝ) * 6 / 6 = ((18 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 18
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 6 2 = (17 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 6 2 = (37 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 6 2 = (6 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 6 2 = (23 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (9 : ℝ) * Flanks.flankOpening 8 6 2 = (9 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (18 : ℝ) * Flanks.flankOpening 8 6 2 = (18 : ℝ)/48 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 6 3 = (25 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 6 3 = (29 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 6 3 = (6 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 6 3 = (31 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (9 : ℝ) * Flanks.flankOpening 8 6 3 = (33 : ℝ)/48 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (18 : ℝ) * Flanks.flankOpening 8 6 3 = (18 : ℝ)/48 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 6 4 = (33 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 6 4 = (21 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 6 4 = (6 : ℝ)/48 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 6 4 = (39 : ℝ)/48 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (9 : ℝ) * Flanks.flankOpening 8 6 4 = (9 : ℝ)/48 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (18 : ℝ) * Flanks.flankOpening 8 6 4 = (18 : ℝ)/48 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 17 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 18 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 18 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (17 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (34 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 6 = 3 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 3 = (27 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (20 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (37 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (6 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (23 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (40 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (9 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (26 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 6 = 3 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 3 = (35 : ℝ)/48 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (12 : ℝ)/48 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (29 : ℝ)/48 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 6 = 3 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 3 = (14 : ℝ)/48 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (15 : ℝ)/48 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 6 = 2 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 2 = (32 : ℝ)/48 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 6 = 3 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 3 = (41 : ℝ)/48 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)

/-- **Family 31**: differences `{1, 5, 7, 9, 12, x, 18}`, flank `7`, period `7`, uncovered residues `{2, 5, 6}`.  Covers 3 census rows. -/
theorem family31_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 18) :
    ∃ k : ℕ, Lonely 8 ({1, 5, 7, 9, 12, x, 18} : Finset ℝ) (Flanks.flankOpening 8 7 k) := by
  have hq : ((7 : ℕ) : ℝ) * (x / 7) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 7
    {2, 5, 6} ⟨2, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((7 : ℕ) : ℝ) * (d / 7) = d * 7 / 7 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 7 / 7 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (5 : ℝ) * 7 / 7 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (7 : ℝ) * 7 / 7 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (9 : ℝ) * 7 / 7 = ((9 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 9
    · rw [show (12 : ℝ) * 7 / 7 = ((12 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 12
    · exact absurd h hdx
    · rw [show (18 : ℝ) * 7 / 7 = ((18 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 18
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 7 2 = (17 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 7 2 = (29 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 2 = (7 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (9 : ℝ) * Flanks.flankOpening 8 7 2 = (41 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 7 2 = (36 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (18 : ℝ) * Flanks.flankOpening 8 7 2 = (26 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 7 5 = (41 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 7 5 = (37 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 5 = (7 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (9 : ℝ) * Flanks.flankOpening 8 7 5 = (33 : ℝ)/56 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 7 5 = (44 : ℝ)/56 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (18 : ℝ) * Flanks.flankOpening 8 7 5 = (10 : ℝ)/56 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 7 6 = (49 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 7 6 = (21 : ℝ)/56 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 6 = (7 : ℝ)/56 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (9 : ℝ) * Flanks.flankOpening 8 7 6 = (49 : ℝ)/56 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 7 6 = (28 : ℝ)/56 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (18 : ℝ) * Flanks.flankOpening 8 7 6 = (42 : ℝ)/56 + ((15 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 15 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 17 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 18 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 18 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (17 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (34 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (11 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (12 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (29 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (46 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (7 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (24 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (41 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (18 : ℝ)/56 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (19 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (36 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (29 : ℝ)/56 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (14 : ℝ)/56 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (31 : ℝ)/56 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (48 : ℝ)/56 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (9 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)

/-- **Family 32**: differences `{2, 5, 7, 9, 17, x, 18}`, flank `7`, period `7`, uncovered residues `{2, 5, 6}`.  Covers 3 census rows. -/
theorem family32_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 18) :
    ∃ k : ℕ, Lonely 8 ({2, 5, 7, 9, 17, x, 18} : Finset ℝ) (Flanks.flankOpening 8 7 k) := by
  have hq : ((7 : ℕ) : ℝ) * (x / 7) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 7
    {2, 5, 6} ⟨2, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((7 : ℕ) : ℝ) * (d / 7) = d * 7 / 7 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (2 : ℝ) * 7 / 7 = ((2 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 2
    · rw [show (5 : ℝ) * 7 / 7 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (7 : ℝ) * 7 / 7 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (9 : ℝ) * 7 / 7 = ((9 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 9
    · rw [show (17 : ℝ) * 7 / 7 = ((17 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 17
    · exact absurd h hdx
    · rw [show (18 : ℝ) * 7 / 7 = ((18 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 18
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 7 2 = (34 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 7 2 = (29 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 2 = (7 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (9 : ℝ) * Flanks.flankOpening 8 7 2 = (41 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (17 : ℝ) * Flanks.flankOpening 8 7 2 = (9 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (18 : ℝ) * Flanks.flankOpening 8 7 2 = (26 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 7 5 = (26 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 7 5 = (37 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 5 = (7 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (9 : ℝ) * Flanks.flankOpening 8 7 5 = (33 : ℝ)/56 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (17 : ℝ) * Flanks.flankOpening 8 7 5 = (25 : ℝ)/56 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (18 : ℝ) * Flanks.flankOpening 8 7 5 = (10 : ℝ)/56 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 7 6 = (42 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 7 6 = (21 : ℝ)/56 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 6 = (7 : ℝ)/56 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (9 : ℝ) * Flanks.flankOpening 8 7 6 = (49 : ℝ)/56 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (17 : ℝ) * Flanks.flankOpening 8 7 6 = (49 : ℝ)/56 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (18 : ℝ) * Flanks.flankOpening 8 7 6 = (42 : ℝ)/56 + ((15 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 15 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 17 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 18 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 18 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (17 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (34 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (11 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (12 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (29 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (46 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (7 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (24 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (41 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (18 : ℝ)/56 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (19 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (36 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (29 : ℝ)/56 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (14 : ℝ)/56 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (31 : ℝ)/56 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (48 : ℝ)/56 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (9 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)

/-- **Family 33**: differences `{2, 3, 4, 7, 10, x, 20}`, flank `7`, period `7`, uncovered residues `{1, 6}`.  Covers 3 census rows. -/
theorem family33_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 20) :
    ∃ k : ℕ, Lonely 8 ({2, 3, 4, 7, 10, x, 20} : Finset ℝ) (Flanks.flankOpening 8 7 k) := by
  have hq : ((7 : ℕ) : ℝ) * (x / 7) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 7
    {1, 6} ⟨1, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((7 : ℕ) : ℝ) * (d / 7) = d * 7 / 7 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (2 : ℝ) * 7 / 7 = ((2 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 2
    · rw [show (3 : ℝ) * 7 / 7 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (4 : ℝ) * 7 / 7 = ((4 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 4
    · rw [show (7 : ℝ) * 7 / 7 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (10 : ℝ) * 7 / 7 = ((10 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 10
    · exact absurd h hdx
    · rw [show (20 : ℝ) * 7 / 7 = ((20 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 20
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 7 1 = (18 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 7 1 = (27 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 7 1 = (36 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 1 = (7 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 7 1 = (34 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 7 1 = (12 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 7 6 = (42 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 7 6 = (35 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 7 6 = (28 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 6 = (7 : ℝ)/56 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 7 6 = (42 : ℝ)/56 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 7 6 = (28 : ℝ)/56 + ((17 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 17 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 19 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 20 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 20 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (9 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (18 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (27 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (36 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (45 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 7 = 6 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 6 = (14 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (7 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (16 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (25 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (34 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (43 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 7 = 6 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 6 = (28 : ℝ)/56 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 7 = 6 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 6 = (21 : ℝ)/56 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (14 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (23 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (32 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (41 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 7 = 6 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 6 = (42 : ℝ)/56 + ((15 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 15 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 7 = 6 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 6 = (35 : ℝ)/56 + ((16 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 16 (by norm_num) (by norm_num)

/-- **Family 34**: differences `{2, 3, 7, 8, 10, x, 20}`, flank `10`, period `10`, uncovered residues `{2, 8, 9}`.  Covers 3 census rows. -/
theorem family34_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 20) :
    ∃ k : ℕ, Lonely 8 ({2, 3, 7, 8, 10, x, 20} : Finset ℝ) (Flanks.flankOpening 8 10 k) := by
  have hq : ((10 : ℕ) : ℝ) * (x / 10) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 10
    {2, 8, 9} ⟨2, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((10 : ℕ) : ℝ) * (d / 10) = d * 10 / 10 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (2 : ℝ) * 10 / 10 = ((2 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 2
    · rw [show (3 : ℝ) * 10 / 10 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (7 : ℝ) * 10 / 10 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (8 : ℝ) * 10 / 10 = ((8 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 8
    · rw [show (10 : ℝ) * 10 / 10 = ((10 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 10
    · exact absurd h hdx
    · rw [show (20 : ℝ) * 10 / 10 = ((20 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 20
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 10 2 = (34 : ℝ)/80 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 10 2 = (51 : ℝ)/80 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 10 2 = (39 : ℝ)/80 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 10 2 = (56 : ℝ)/80 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 10 2 = (10 : ℝ)/80 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 10 2 = (20 : ℝ)/80 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 10 8 = (50 : ℝ)/80 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 10 8 = (35 : ℝ)/80 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 10 8 = (55 : ℝ)/80 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 10 8 = (40 : ℝ)/80 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 10 8 = (10 : ℝ)/80 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 10 8 = (20 : ℝ)/80 + ((16 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 16 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 10 9 = (66 : ℝ)/80 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 10 9 = (59 : ℝ)/80 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 10 9 = (31 : ℝ)/80 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 10 9 = (24 : ℝ)/80 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 10 9 = (10 : ℝ)/80 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 10 9 = (20 : ℝ)/80 + ((18 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 18 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 19 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 20 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 20 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 10 = 2 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 2 = (17 : ℝ)/80 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 10 = 2 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 2 = (34 : ℝ)/80 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 10 = 2 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 2 = (51 : ℝ)/80 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 10 = 2 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 2 = (68 : ℝ)/80 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨9, by decide, 0, ?_⟩
      rw [show (9 : ℕ) + 0 * 10 = 9 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 9 = (45 : ℝ)/80 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 10 = 2 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 2 = (22 : ℝ)/80 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 10 = 2 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 2 = (39 : ℝ)/80 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 10 = 2 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 2 = (56 : ℝ)/80 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨8, by decide, 0, ?_⟩
      rw [show (8 : ℕ) + 0 * 10 = 8 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 8 = (25 : ℝ)/80 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 10 = 2 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 2 = (10 : ℝ)/80 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 10 = 2 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 2 = (27 : ℝ)/80 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 10 = 2 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 2 = (44 : ℝ)/80 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 10 = 2 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 2 = (61 : ℝ)/80 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨8, by decide, 0, ?_⟩
      rw [show (8 : ℕ) + 0 * 10 = 8 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 8 = (30 : ℝ)/80 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 10 = 2 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 2 = (15 : ℝ)/80 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 10 = 2 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 2 = (32 : ℝ)/80 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 10 = 2 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 2 = (49 : ℝ)/80 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 10 = 2 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 2 = (66 : ℝ)/80 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨8, by decide, 0, ?_⟩
      rw [show (8 : ℕ) + 0 * 10 = 8 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 8 = (35 : ℝ)/80 + ((15 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 15 (by norm_num) (by norm_num)

/-- **Family 35**: differences `{2, 3, 7, 10, 12, x, 20}`, flank `7`, period `7`, uncovered residues `{5, 6}`.  Covers 3 census rows. -/
theorem family35_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 20) :
    ∃ k : ℕ, Lonely 8 ({2, 3, 7, 10, 12, x, 20} : Finset ℝ) (Flanks.flankOpening 8 7 k) := by
  have hq : ((7 : ℕ) : ℝ) * (x / 7) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 7
    {5, 6} ⟨5, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((7 : ℕ) : ℝ) * (d / 7) = d * 7 / 7 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (2 : ℝ) * 7 / 7 = ((2 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 2
    · rw [show (3 : ℝ) * 7 / 7 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (7 : ℝ) * 7 / 7 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (10 : ℝ) * 7 / 7 = ((10 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 10
    · rw [show (12 : ℝ) * 7 / 7 = ((12 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 12
    · exact absurd h hdx
    · rw [show (20 : ℝ) * 7 / 7 = ((20 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 20
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 7 5 = (26 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 7 5 = (11 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 5 = (7 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 7 5 = (18 : ℝ)/56 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 7 5 = (44 : ℝ)/56 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 7 5 = (36 : ℝ)/56 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 7 6 = (42 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 7 6 = (35 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 6 = (7 : ℝ)/56 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 7 6 = (42 : ℝ)/56 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 7 6 = (28 : ℝ)/56 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 7 6 = (28 : ℝ)/56 + ((17 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 17 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 19 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 20 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 20 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (41 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (26 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (11 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 7 = 6 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 6 = (28 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (37 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (22 : ℝ)/56 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (7 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (48 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (33 : ℝ)/56 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (18 : ℝ)/56 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 7 = 6 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 6 = (35 : ℝ)/56 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (44 : ℝ)/56 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (29 : ℝ)/56 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (14 : ℝ)/56 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 7 = 6 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 6 = (7 : ℝ)/56 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (40 : ℝ)/56 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (25 : ℝ)/56 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (10 : ℝ)/56 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 7 = 6 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 6 = (35 : ℝ)/56 + ((16 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 16 (by norm_num) (by norm_num)

/-- **Family 36**: differences `{2, 3, 7, 10, 16, x, 20}`, flank `10`, period `10`, uncovered residues `{1, 2, 6, 9}`.  Covers 3 census rows. -/
theorem family36_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 20) :
    ∃ k : ℕ, Lonely 8 ({2, 3, 7, 10, 16, x, 20} : Finset ℝ) (Flanks.flankOpening 8 10 k) := by
  have hq : ((10 : ℕ) : ℝ) * (x / 10) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 10
    {1, 2, 6, 9} ⟨1, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((10 : ℕ) : ℝ) * (d / 10) = d * 10 / 10 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (2 : ℝ) * 10 / 10 = ((2 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 2
    · rw [show (3 : ℝ) * 10 / 10 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (7 : ℝ) * 10 / 10 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (10 : ℝ) * 10 / 10 = ((10 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 10
    · rw [show (16 : ℝ) * 10 / 10 = ((16 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 16
    · exact absurd h hdx
    · rw [show (20 : ℝ) * 10 / 10 = ((20 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 20
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 10 1 = (18 : ℝ)/80 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 10 1 = (27 : ℝ)/80 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 10 1 = (63 : ℝ)/80 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 10 1 = (10 : ℝ)/80 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 10 1 = (64 : ℝ)/80 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 10 1 = (20 : ℝ)/80 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 10 2 = (34 : ℝ)/80 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 10 2 = (51 : ℝ)/80 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 10 2 = (39 : ℝ)/80 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 10 2 = (10 : ℝ)/80 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 10 2 = (32 : ℝ)/80 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 10 2 = (20 : ℝ)/80 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 10 6 = (18 : ℝ)/80 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 10 6 = (67 : ℝ)/80 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 10 6 = (23 : ℝ)/80 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 10 6 = (10 : ℝ)/80 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 10 6 = (64 : ℝ)/80 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 10 6 = (20 : ℝ)/80 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 10 9 = (66 : ℝ)/80 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 10 9 = (59 : ℝ)/80 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 10 9 = (31 : ℝ)/80 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 10 9 = (10 : ℝ)/80 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 10 9 = (48 : ℝ)/80 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 10 9 = (20 : ℝ)/80 + ((18 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 18 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 19 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 20 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 20 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 10 = 2 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 2 = (17 : ℝ)/80 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 10 = 1 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 1 = (18 : ℝ)/80 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 10 = 1 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 1 = (27 : ℝ)/80 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 10 = 1 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 1 = (36 : ℝ)/80 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 10 = 1 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 1 = (45 : ℝ)/80 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 10 = 1 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 1 = (54 : ℝ)/80 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 10 = 1 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 1 = (63 : ℝ)/80 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 10 = 2 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 2 = (56 : ℝ)/80 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 10 = 6 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 6 = (41 : ℝ)/80 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 10 = 1 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 1 = (10 : ℝ)/80 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 10 = 1 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 1 = (19 : ℝ)/80 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 10 = 1 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 1 = (28 : ℝ)/80 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 10 = 1 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 1 = (37 : ℝ)/80 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 10 = 1 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 1 = (46 : ℝ)/80 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 10 = 1 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 1 = (55 : ℝ)/80 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 10 = 1 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 1 = (64 : ℝ)/80 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 10 = 2 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 2 = (49 : ℝ)/80 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 10 = 2 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 2 = (66 : ℝ)/80 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 10 = 1 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 1 = (11 : ℝ)/80 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)

/-- **Family 37**: differences `{3, 4, 7, 11, 20, x, 22}`, flank `4`, period `4`, uncovered residues `{2, 3}`.  Covers 2 census rows. -/
theorem family37_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 22) :
    ∃ k : ℕ, Lonely 8 ({3, 4, 7, 11, 20, x, 22} : Finset ℝ) (Flanks.flankOpening 8 4 k) := by
  have hq : ((4 : ℕ) : ℝ) * (x / 4) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 4
    {2, 3} ⟨2, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((4 : ℕ) : ℝ) * (d / 4) = d * 4 / 4 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (3 : ℝ) * 4 / 4 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (4 : ℝ) * 4 / 4 = ((4 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 4
    · rw [show (7 : ℝ) * 4 / 4 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (11 : ℝ) * 4 / 4 = ((11 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 11
    · rw [show (20 : ℝ) * 4 / 4 = ((20 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 20
    · exact absurd h hdx
    · rw [show (22 : ℝ) * 4 / 4 = ((22 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 22
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 4 2 = (19 : ℝ)/32 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 4 2 = (4 : ℝ)/32 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 4 2 = (23 : ℝ)/32 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (11 : ℝ) * Flanks.flankOpening 8 4 2 = (27 : ℝ)/32 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 4 2 = (20 : ℝ)/32 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (22 : ℝ) * Flanks.flankOpening 8 4 2 = (22 : ℝ)/32 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 4 3 = (11 : ℝ)/32 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 4 3 = (4 : ℝ)/32 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 4 3 = (15 : ℝ)/32 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (11 : ℝ) * Flanks.flankOpening 8 4 3 = (19 : ℝ)/32 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 4 3 = (20 : ℝ)/32 + ((15 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 15 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (22 : ℝ) * Flanks.flankOpening 8 4 3 = (6 : ℝ)/32 + ((17 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 17 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 21 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 22 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 22 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 4 = 2 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 2 = (17 : ℝ)/32 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 4 = 3 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 3 = (18 : ℝ)/32 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 4 = 2 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 2 = (19 : ℝ)/32 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 4 = 2 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 2 = (4 : ℝ)/32 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 4 = 2 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 2 = (21 : ℝ)/32 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 4 = 2 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 2 = (6 : ℝ)/32 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 4 = 2 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 2 = (23 : ℝ)/32 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 4 = 2 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 2 = (8 : ℝ)/32 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 4 = 2 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 2 = (25 : ℝ)/32 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 4 = 2 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 2 = (10 : ℝ)/32 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 4 = 2 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 2 = (27 : ℝ)/32 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 4 = 2 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 2 = (12 : ℝ)/32 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 4 = 3 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 3 = (5 : ℝ)/32 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 4 = 2 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 2 = (14 : ℝ)/32 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 4 = 3 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 3 = (23 : ℝ)/32 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 4 = 2 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 2 = (16 : ℝ)/32 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 4 = 3 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 3 = (9 : ℝ)/32 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 4 = 2 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 2 = (18 : ℝ)/32 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 4 = 3 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 3 = (27 : ℝ)/32 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 4 = 2 from rfl,
        show (((20 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 2 = (20 : ℝ)/32 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 4 = 2 from rfl,
        show (((21 : ℤ)) : ℝ) * Flanks.flankOpening 8 4 2 = (5 : ℝ)/32 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)

/-- **Family 38**: differences `{3, 5, 8, 11, 21, x, 22}`, flank `8`, period `8`, uncovered residues `{4, 7}`.  Covers 2 census rows. -/
theorem family38_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 22) :
    ∃ k : ℕ, Lonely 8 ({3, 5, 8, 11, 21, x, 22} : Finset ℝ) (Flanks.flankOpening 8 8 k) := by
  have hq : ((8 : ℕ) : ℝ) * (x / 8) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 8
    {4, 7} ⟨4, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((8 : ℕ) : ℝ) * (d / 8) = d * 8 / 8 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (3 : ℝ) * 8 / 8 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (5 : ℝ) * 8 / 8 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (8 : ℝ) * 8 / 8 = ((8 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 8
    · rw [show (11 : ℝ) * 8 / 8 = ((11 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 11
    · rw [show (21 : ℝ) * 8 / 8 = ((21 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 21
    · exact absurd h hdx
    · rw [show (22 : ℝ) * 8 / 8 = ((22 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 22
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 8 4 = (35 : ℝ)/64 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 8 4 = (37 : ℝ)/64 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 8 4 = (8 : ℝ)/64 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (11 : ℝ) * Flanks.flankOpening 8 8 4 = (43 : ℝ)/64 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (21 : ℝ) * Flanks.flankOpening 8 8 4 = (53 : ℝ)/64 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (22 : ℝ) * Flanks.flankOpening 8 8 4 = (22 : ℝ)/64 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 8 7 = (43 : ℝ)/64 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 8 7 = (29 : ℝ)/64 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 8 7 = (8 : ℝ)/64 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (11 : ℝ) * Flanks.flankOpening 8 8 7 = (51 : ℝ)/64 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
      · rw [h, show (21 : ℝ) * Flanks.flankOpening 8 8 7 = (45 : ℝ)/64 + ((18 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 18 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (22 : ℝ) * Flanks.flankOpening 8 8 7 = (38 : ℝ)/64 + ((19 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 19 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 21 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 22 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 22 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 8 = 4 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 4 = (33 : ℝ)/64 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨7, by decide, 0, ?_⟩
      rw [show (7 : ℕ) + 0 * 8 = 7 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 7 = (50 : ℝ)/64 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 8 = 4 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 4 = (35 : ℝ)/64 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨7, by decide, 0, ?_⟩
      rw [show (7 : ℕ) + 0 * 8 = 7 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 7 = (36 : ℝ)/64 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 8 = 4 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 4 = (37 : ℝ)/64 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨7, by decide, 0, ?_⟩
      rw [show (7 : ℕ) + 0 * 8 = 7 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 7 = (22 : ℝ)/64 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 8 = 4 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 4 = (39 : ℝ)/64 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 8 = 4 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 4 = (8 : ℝ)/64 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 8 = 4 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 4 = (41 : ℝ)/64 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 8 = 4 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 4 = (10 : ℝ)/64 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 8 = 4 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 4 = (43 : ℝ)/64 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 8 = 4 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 4 = (12 : ℝ)/64 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 8 = 4 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 4 = (45 : ℝ)/64 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 8 = 4 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 4 = (14 : ℝ)/64 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 8 = 4 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 4 = (47 : ℝ)/64 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 8 = 4 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 4 = (16 : ℝ)/64 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 8 = 4 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 4 = (49 : ℝ)/64 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 8 = 4 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 4 = (18 : ℝ)/64 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 8 = 4 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 4 = (51 : ℝ)/64 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 8 = 4 from rfl,
        show (((20 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 4 = (20 : ℝ)/64 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 8 = 4 from rfl,
        show (((21 : ℤ)) : ℝ) * Flanks.flankOpening 8 8 4 = (53 : ℝ)/64 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)

/-- **Family 39**: differences `{3, 5, 11, 16, 21, x, 22}`, flank `11`, period `11`, uncovered residues `{1, 5, 8, 9, 10}`.  Covers 2 census rows. -/
theorem family39_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 22) :
    ∃ k : ℕ, Lonely 8 ({3, 5, 11, 16, 21, x, 22} : Finset ℝ) (Flanks.flankOpening 8 11 k) := by
  have hq : ((11 : ℕ) : ℝ) * (x / 11) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 11
    {1, 5, 8, 9, 10} ⟨1, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((11 : ℕ) : ℝ) * (d / 11) = d * 11 / 11 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (3 : ℝ) * 11 / 11 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (5 : ℝ) * 11 / 11 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (11 : ℝ) * 11 / 11 = ((11 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 11
    · rw [show (16 : ℝ) * 11 / 11 = ((16 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 16
    · rw [show (21 : ℝ) * 11 / 11 = ((21 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 21
    · exact absurd h hdx
    · rw [show (22 : ℝ) * 11 / 11 = ((22 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 22
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 11 1 = (27 : ℝ)/88 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 11 1 = (45 : ℝ)/88 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (11 : ℝ) * Flanks.flankOpening 8 11 1 = (11 : ℝ)/88 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 11 1 = (56 : ℝ)/88 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (21 : ℝ) * Flanks.flankOpening 8 11 1 = (13 : ℝ)/88 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (22 : ℝ) * Flanks.flankOpening 8 11 1 = (22 : ℝ)/88 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 11 5 = (35 : ℝ)/88 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 11 5 = (29 : ℝ)/88 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (11 : ℝ) * Flanks.flankOpening 8 11 5 = (11 : ℝ)/88 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 11 5 = (40 : ℝ)/88 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (21 : ℝ) * Flanks.flankOpening 8 11 5 = (69 : ℝ)/88 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (22 : ℝ) * Flanks.flankOpening 8 11 5 = (22 : ℝ)/88 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 11 8 = (19 : ℝ)/88 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 11 8 = (61 : ℝ)/88 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (11 : ℝ) * Flanks.flankOpening 8 11 8 = (11 : ℝ)/88 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 11 8 = (72 : ℝ)/88 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
      · rw [h, show (21 : ℝ) * Flanks.flankOpening 8 11 8 = (45 : ℝ)/88 + ((15 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 15 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (22 : ℝ) * Flanks.flankOpening 8 11 8 = (22 : ℝ)/88 + ((16 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 16 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 11 9 = (43 : ℝ)/88 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 11 9 = (13 : ℝ)/88 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (11 : ℝ) * Flanks.flankOpening 8 11 9 = (11 : ℝ)/88 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 11 9 = (24 : ℝ)/88 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
      · rw [h, show (21 : ℝ) * Flanks.flankOpening 8 11 9 = (37 : ℝ)/88 + ((17 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 17 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (22 : ℝ) * Flanks.flankOpening 8 11 9 = (22 : ℝ)/88 + ((18 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 18 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 11 10 = (67 : ℝ)/88 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 11 10 = (53 : ℝ)/88 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (11 : ℝ) * Flanks.flankOpening 8 11 10 = (11 : ℝ)/88 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 11 10 = (64 : ℝ)/88 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
      · rw [h, show (21 : ℝ) * Flanks.flankOpening 8 11 10 = (29 : ℝ)/88 + ((19 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 19 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (22 : ℝ) * Flanks.flankOpening 8 11 10 = (22 : ℝ)/88 + ((20 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 20 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 21 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 22 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 22 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (41 : ℝ)/88 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 11 = 1 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 1 = (18 : ℝ)/88 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 11 = 1 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 1 = (27 : ℝ)/88 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 11 = 1 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 1 = (36 : ℝ)/88 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 11 = 1 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 1 = (45 : ℝ)/88 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 11 = 1 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 1 = (54 : ℝ)/88 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 11 = 1 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 1 = (63 : ℝ)/88 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 11 = 1 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 1 = (72 : ℝ)/88 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (17 : ℝ)/88 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (58 : ℝ)/88 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 11 = 1 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 1 = (11 : ℝ)/88 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 11 = 1 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 1 = (20 : ℝ)/88 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 11 = 1 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 1 = (29 : ℝ)/88 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 11 = 1 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 1 = (38 : ℝ)/88 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 11 = 1 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 1 = (47 : ℝ)/88 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 11 = 1 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 1 = (56 : ℝ)/88 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 11 = 1 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 1 = (65 : ℝ)/88 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 11 = 1 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 1 = (74 : ℝ)/88 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (75 : ℝ)/88 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((20 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (28 : ℝ)/88 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 11 = 1 from rfl,
        show (((21 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 1 = (13 : ℝ)/88 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)

/-- **Family 40**: differences `{3, 7, 9, 11, 20, x, 22}`, flank `7`, period `7`, uncovered residues `{1, 6}`.  Covers 2 census rows. -/
theorem family40_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 22) :
    ∃ k : ℕ, Lonely 8 ({3, 7, 9, 11, 20, x, 22} : Finset ℝ) (Flanks.flankOpening 8 7 k) := by
  have hq : ((7 : ℕ) : ℝ) * (x / 7) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 7
    {1, 6} ⟨1, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((7 : ℕ) : ℝ) * (d / 7) = d * 7 / 7 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (3 : ℝ) * 7 / 7 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (7 : ℝ) * 7 / 7 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (9 : ℝ) * 7 / 7 = ((9 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 9
    · rw [show (11 : ℝ) * 7 / 7 = ((11 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 11
    · rw [show (20 : ℝ) * 7 / 7 = ((20 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 20
    · exact absurd h hdx
    · rw [show (22 : ℝ) * 7 / 7 = ((22 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 22
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 7 1 = (27 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 1 = (7 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (9 : ℝ) * Flanks.flankOpening 8 7 1 = (25 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (11 : ℝ) * Flanks.flankOpening 8 7 1 = (43 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 7 1 = (12 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (22 : ℝ) * Flanks.flankOpening 8 7 1 = (30 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 7 6 = (35 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 6 = (7 : ℝ)/56 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (9 : ℝ) * Flanks.flankOpening 8 7 6 = (49 : ℝ)/56 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (11 : ℝ) * Flanks.flankOpening 8 7 6 = (35 : ℝ)/56 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 7 6 = (28 : ℝ)/56 + ((17 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 17 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (22 : ℝ) * Flanks.flankOpening 8 7 6 = (14 : ℝ)/56 + ((19 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 19 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 21 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 22 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 22 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (9 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (18 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (27 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (36 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (45 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 7 = 6 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 6 = (14 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (7 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (16 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (25 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (34 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (43 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 7 = 6 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 6 = (28 : ℝ)/56 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 7 = 6 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 6 = (21 : ℝ)/56 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (14 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (23 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (32 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (41 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 7 = 6 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 6 = (42 : ℝ)/56 + ((15 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 15 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 7 = 6 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 6 = (35 : ℝ)/56 + ((16 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 16 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((20 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (12 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 7 = 1 from rfl,
        show (((21 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 1 = (21 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)

/-- **Family 41**: differences `{3, 7, 11, 13, 20, x, 22}`, flank `11`, period `11`, uncovered residues `{2, 4, 8, 9}`.  Covers 2 census rows. -/
theorem family41_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 22) :
    ∃ k : ℕ, Lonely 8 ({3, 7, 11, 13, 20, x, 22} : Finset ℝ) (Flanks.flankOpening 8 11 k) := by
  have hq : ((11 : ℕ) : ℝ) * (x / 11) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 11
    {2, 4, 8, 9} ⟨2, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((11 : ℕ) : ℝ) * (d / 11) = d * 11 / 11 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (3 : ℝ) * 11 / 11 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (7 : ℝ) * 11 / 11 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (11 : ℝ) * 11 / 11 = ((11 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 11
    · rw [show (13 : ℝ) * 11 / 11 = ((13 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 13
    · rw [show (20 : ℝ) * 11 / 11 = ((20 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 20
    · exact absurd h hdx
    · rw [show (22 : ℝ) * 11 / 11 = ((22 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 22
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 11 2 = (51 : ℝ)/88 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 11 2 = (31 : ℝ)/88 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (11 : ℝ) * Flanks.flankOpening 8 11 2 = (11 : ℝ)/88 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (13 : ℝ) * Flanks.flankOpening 8 11 2 = (45 : ℝ)/88 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 11 2 = (76 : ℝ)/88 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (22 : ℝ) * Flanks.flankOpening 8 11 2 = (22 : ℝ)/88 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 11 4 = (11 : ℝ)/88 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 11 4 = (55 : ℝ)/88 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (11 : ℝ) * Flanks.flankOpening 8 11 4 = (11 : ℝ)/88 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (13 : ℝ) * Flanks.flankOpening 8 11 4 = (77 : ℝ)/88 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 11 4 = (44 : ℝ)/88 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (22 : ℝ) * Flanks.flankOpening 8 11 4 = (22 : ℝ)/88 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 11 8 = (19 : ℝ)/88 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 11 8 = (15 : ℝ)/88 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (11 : ℝ) * Flanks.flankOpening 8 11 8 = (11 : ℝ)/88 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (13 : ℝ) * Flanks.flankOpening 8 11 8 = (53 : ℝ)/88 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 11 8 = (68 : ℝ)/88 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (22 : ℝ) * Flanks.flankOpening 8 11 8 = (22 : ℝ)/88 + ((16 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 16 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 11 9 = (43 : ℝ)/88 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 11 9 = (71 : ℝ)/88 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (11 : ℝ) * Flanks.flankOpening 8 11 9 = (11 : ℝ)/88 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
      · rw [h, show (13 : ℝ) * Flanks.flankOpening 8 11 9 = (69 : ℝ)/88 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 11 9 = (52 : ℝ)/88 + ((16 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 16 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (22 : ℝ) * Flanks.flankOpening 8 11 9 = (22 : ℝ)/88 + ((18 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 18 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 21 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 22 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 22 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 11 = 2 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 2 = (17 : ℝ)/88 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 11 = 2 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 2 = (34 : ℝ)/88 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 11 = 2 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 2 = (51 : ℝ)/88 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 11 = 2 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 2 = (68 : ℝ)/88 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 11 = 4 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 4 = (77 : ℝ)/88 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 11 = 2 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 2 = (14 : ℝ)/88 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 11 = 2 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 2 = (31 : ℝ)/88 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 11 = 2 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 2 = (48 : ℝ)/88 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 11 = 2 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 2 = (65 : ℝ)/88 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 11 = 4 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 4 = (66 : ℝ)/88 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 11 = 2 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 2 = (11 : ℝ)/88 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 11 = 2 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 2 = (28 : ℝ)/88 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 11 = 2 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 2 = (45 : ℝ)/88 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 11 = 2 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 2 = (62 : ℝ)/88 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 11 = 4 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 4 = (55 : ℝ)/88 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨8, by decide, 0, ?_⟩
      rw [show (8 : ℕ) + 0 * 11 = 8 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 8 = (72 : ℝ)/88 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 11 = 2 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 2 = (25 : ℝ)/88 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 11 = 2 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 2 = (42 : ℝ)/88 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 11 = 2 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 2 = (59 : ℝ)/88 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 11 = 2 from rfl,
        show (((20 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 2 = (76 : ℝ)/88 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 11 = 4 from rfl,
        show (((21 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 4 = (77 : ℝ)/88 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)

/-- **Family 42**: differences `{3, 12, 15, 18, 21, x, 22}`, flank `3`, period `3`, uncovered residues `{1, 2}`.  Covers 2 census rows. -/
theorem family42_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 22) :
    ∃ k : ℕ, Lonely 8 ({3, 12, 15, 18, 21, x, 22} : Finset ℝ) (Flanks.flankOpening 8 3 k) := by
  have hq : ((3 : ℕ) : ℝ) * (x / 3) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 3
    {1, 2} ⟨1, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((3 : ℕ) : ℝ) * (d / 3) = d * 3 / 3 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (3 : ℝ) * 3 / 3 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (12 : ℝ) * 3 / 3 = ((12 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 12
    · rw [show (15 : ℝ) * 3 / 3 = ((15 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 15
    · rw [show (18 : ℝ) * 3 / 3 = ((18 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 18
    · rw [show (21 : ℝ) * 3 / 3 = ((21 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 21
    · exact absurd h hdx
    · rw [show (22 : ℝ) * 3 / 3 = ((22 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 22
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 3 1 = (3 : ℝ)/24 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 3 1 = (12 : ℝ)/24 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (15 : ℝ) * Flanks.flankOpening 8 3 1 = (15 : ℝ)/24 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (18 : ℝ) * Flanks.flankOpening 8 3 1 = (18 : ℝ)/24 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (21 : ℝ) * Flanks.flankOpening 8 3 1 = (21 : ℝ)/24 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (22 : ℝ) * Flanks.flankOpening 8 3 1 = (6 : ℝ)/24 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 3 2 = (3 : ℝ)/24 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 3 2 = (12 : ℝ)/24 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (15 : ℝ) * Flanks.flankOpening 8 3 2 = (15 : ℝ)/24 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
      · rw [h, show (18 : ℝ) * Flanks.flankOpening 8 3 2 = (18 : ℝ)/24 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
      · rw [h, show (21 : ℝ) * Flanks.flankOpening 8 3 2 = (21 : ℝ)/24 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (22 : ℝ) * Flanks.flankOpening 8 3 2 = (14 : ℝ)/24 + ((15 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 15 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 21 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 22 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 22 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 3 = 1 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 3 1 = (9 : ℝ)/24 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 3 = 1 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 3 1 = (18 : ℝ)/24 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 3 = 1 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 3 1 = (3 : ℝ)/24 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 3 = 1 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 3 1 = (12 : ℝ)/24 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 3 = 1 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 3 1 = (21 : ℝ)/24 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 3 = 1 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 3 1 = (6 : ℝ)/24 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 3 = 1 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 3 1 = (15 : ℝ)/24 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 3 = 2 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 3 2 = (16 : ℝ)/24 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 3 = 1 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 3 1 = (9 : ℝ)/24 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 3 = 1 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 3 1 = (18 : ℝ)/24 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 3 = 1 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 3 1 = (3 : ℝ)/24 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 3 = 1 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 3 1 = (12 : ℝ)/24 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 3 = 1 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 3 1 = (21 : ℝ)/24 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 3 = 1 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 3 1 = (6 : ℝ)/24 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 3 = 1 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 3 1 = (15 : ℝ)/24 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 3 = 2 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 3 2 = (8 : ℝ)/24 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 3 = 1 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 3 1 = (9 : ℝ)/24 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 3 = 1 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 3 1 = (18 : ℝ)/24 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 3 = 1 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 3 1 = (3 : ℝ)/24 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 3 = 1 from rfl,
        show (((20 : ℤ)) : ℝ) * Flanks.flankOpening 8 3 1 = (12 : ℝ)/24 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 3 = 1 from rfl,
        show (((21 : ℤ)) : ℝ) * Flanks.flankOpening 8 3 1 = (21 : ℝ)/24 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)

/-- **Family 43**: differences `{1, 5, 7, 11, 12, x, 24}`, flank `11`, period `11`, uncovered residues `{5, 7, 8}`.  Covers 2 census rows. -/
theorem family43_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 24) :
    ∃ k : ℕ, Lonely 8 ({1, 5, 7, 11, 12, x, 24} : Finset ℝ) (Flanks.flankOpening 8 11 k) := by
  have hq : ((11 : ℕ) : ℝ) * (x / 11) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 11
    {5, 7, 8} ⟨5, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((11 : ℕ) : ℝ) * (d / 11) = d * 11 / 11 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 11 / 11 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (5 : ℝ) * 11 / 11 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (7 : ℝ) * 11 / 11 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (11 : ℝ) * 11 / 11 = ((11 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 11
    · rw [show (12 : ℝ) * 11 / 11 = ((12 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 12
    · exact absurd h hdx
    · rw [show (24 : ℝ) * 11 / 11 = ((24 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 24
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 11 5 = (41 : ℝ)/88 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 11 5 = (29 : ℝ)/88 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 11 5 = (23 : ℝ)/88 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (11 : ℝ) * Flanks.flankOpening 8 11 5 = (11 : ℝ)/88 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 11 5 = (52 : ℝ)/88 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (24 : ℝ) * Flanks.flankOpening 8 11 5 = (16 : ℝ)/88 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 11 7 = (57 : ℝ)/88 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 11 7 = (21 : ℝ)/88 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 11 7 = (47 : ℝ)/88 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (11 : ℝ) * Flanks.flankOpening 8 11 7 = (11 : ℝ)/88 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 11 7 = (68 : ℝ)/88 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (24 : ℝ) * Flanks.flankOpening 8 11 7 = (48 : ℝ)/88 + ((15 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 15 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 11 8 = (65 : ℝ)/88 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 11 8 = (61 : ℝ)/88 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 11 8 = (15 : ℝ)/88 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (11 : ℝ) * Flanks.flankOpening 8 11 8 = (11 : ℝ)/88 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 11 8 = (76 : ℝ)/88 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (24 : ℝ) * Flanks.flankOpening 8 11 8 = (64 : ℝ)/88 + ((17 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 17 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 23 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 24 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 24 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (41 : ℝ)/88 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨7, by decide, 0, ?_⟩
      rw [show (7 : ℕ) + 0 * 11 = 7 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 7 = (26 : ℝ)/88 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (35 : ℝ)/88 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (76 : ℝ)/88 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (29 : ℝ)/88 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (70 : ℝ)/88 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (23 : ℝ)/88 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (64 : ℝ)/88 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (17 : ℝ)/88 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (58 : ℝ)/88 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (11 : ℝ)/88 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (52 : ℝ)/88 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨7, by decide, 0, ?_⟩
      rw [show (7 : ℕ) + 0 * 11 = 7 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 7 = (37 : ℝ)/88 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (46 : ℝ)/88 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨7, by decide, 0, ?_⟩
      rw [show (7 : ℕ) + 0 * 11 = 7 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 7 = (63 : ℝ)/88 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (40 : ℝ)/88 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨8, by decide, 0, ?_⟩
      rw [show (8 : ℕ) + 0 * 11 = 8 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 8 = (49 : ℝ)/88 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (34 : ℝ)/88 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (75 : ℝ)/88 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((20 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (28 : ℝ)/88 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((21 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (69 : ℝ)/88 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((22 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (22 : ℝ)/88 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((23 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (63 : ℝ)/88 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)

/-- **Family 44**: differences `{2, 5, 7, 8, 12, x, 24}`, flank `7`, period `7`, uncovered residues `{2, 5}`.  Covers 2 census rows. -/
theorem family44_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 24) :
    ∃ k : ℕ, Lonely 8 ({2, 5, 7, 8, 12, x, 24} : Finset ℝ) (Flanks.flankOpening 8 7 k) := by
  have hq : ((7 : ℕ) : ℝ) * (x / 7) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 7
    {2, 5} ⟨2, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((7 : ℕ) : ℝ) * (d / 7) = d * 7 / 7 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (2 : ℝ) * 7 / 7 = ((2 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 2
    · rw [show (5 : ℝ) * 7 / 7 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (7 : ℝ) * 7 / 7 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (8 : ℝ) * 7 / 7 = ((8 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 8
    · rw [show (12 : ℝ) * 7 / 7 = ((12 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 12
    · exact absurd h hdx
    · rw [show (24 : ℝ) * 7 / 7 = ((24 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 24
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 7 2 = (34 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 7 2 = (29 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 2 = (7 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 7 2 = (24 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 7 2 = (36 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (24 : ℝ) * Flanks.flankOpening 8 7 2 = (16 : ℝ)/56 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 7 5 = (26 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 7 5 = (37 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 5 = (7 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 7 5 = (48 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 7 5 = (44 : ℝ)/56 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (24 : ℝ) * Flanks.flankOpening 8 7 5 = (32 : ℝ)/56 + ((17 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 17 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 23 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 24 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 24 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (17 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (34 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (11 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (12 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (29 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (46 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (7 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (24 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (41 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (18 : ℝ)/56 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (19 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (36 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (29 : ℝ)/56 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (14 : ℝ)/56 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (31 : ℝ)/56 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (48 : ℝ)/56 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (9 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (26 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (43 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((20 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (36 : ℝ)/56 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((21 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (21 : ℝ)/56 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((22 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (38 : ℝ)/56 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((23 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (47 : ℝ)/56 + ((16 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 16 (by norm_num) (by norm_num)

/-- **Family 45**: differences `{2, 5, 7, 12, 16, x, 24}`, flank `7`, period `7`, uncovered residues `{2, 5}`.  Covers 2 census rows. -/
theorem family45_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 24) :
    ∃ k : ℕ, Lonely 8 ({2, 5, 7, 12, 16, x, 24} : Finset ℝ) (Flanks.flankOpening 8 7 k) := by
  have hq : ((7 : ℕ) : ℝ) * (x / 7) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 7
    {2, 5} ⟨2, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((7 : ℕ) : ℝ) * (d / 7) = d * 7 / 7 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (2 : ℝ) * 7 / 7 = ((2 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 2
    · rw [show (5 : ℝ) * 7 / 7 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (7 : ℝ) * 7 / 7 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (12 : ℝ) * 7 / 7 = ((12 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 12
    · rw [show (16 : ℝ) * 7 / 7 = ((16 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 16
    · exact absurd h hdx
    · rw [show (24 : ℝ) * 7 / 7 = ((24 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 24
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 7 2 = (34 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 7 2 = (29 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 2 = (7 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 7 2 = (36 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 7 2 = (48 : ℝ)/56 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (24 : ℝ) * Flanks.flankOpening 8 7 2 = (16 : ℝ)/56 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 7 5 = (26 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 7 5 = (37 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 7 5 = (7 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 7 5 = (44 : ℝ)/56 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 7 5 = (40 : ℝ)/56 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (24 : ℝ) * Flanks.flankOpening 8 7 5 = (32 : ℝ)/56 + ((17 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 17 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 23 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 24 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 24 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (17 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (34 : ℝ)/56 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (11 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (12 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (29 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (46 : ℝ)/56 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (7 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (24 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (41 : ℝ)/56 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (18 : ℝ)/56 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (19 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (36 : ℝ)/56 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (29 : ℝ)/56 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (14 : ℝ)/56 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (31 : ℝ)/56 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (48 : ℝ)/56 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (9 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (26 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (43 : ℝ)/56 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((20 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (36 : ℝ)/56 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((21 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (21 : ℝ)/56 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 7 = 2 from rfl,
        show (((22 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 2 = (38 : ℝ)/56 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 7 = 5 from rfl,
        show (((23 : ℤ)) : ℝ) * Flanks.flankOpening 8 7 5 = (47 : ℝ)/56 + ((16 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 16 (by norm_num) (by norm_num)

/-- **Family 46**: differences `{1, 5, 13, 14, 15, x, 26}`, flank `5`, period `5`, uncovered residues `{3, 4}`.  Covers 2 census rows. -/
theorem family46_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 26) :
    ∃ k : ℕ, Lonely 8 ({1, 5, 13, 14, 15, x, 26} : Finset ℝ) (Flanks.flankOpening 8 5 k) := by
  have hq : ((5 : ℕ) : ℝ) * (x / 5) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 5
    {3, 4} ⟨3, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((5 : ℕ) : ℝ) * (d / 5) = d * 5 / 5 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 5 / 5 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (5 : ℝ) * 5 / 5 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (13 : ℝ) * 5 / 5 = ((13 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 13
    · rw [show (14 : ℝ) * 5 / 5 = ((14 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 14
    · rw [show (15 : ℝ) * 5 / 5 = ((15 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 15
    · exact absurd h hdx
    · rw [show (26 : ℝ) * 5 / 5 = ((26 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 26
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 5 3 = (25 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 5 3 = (5 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (13 : ℝ) * Flanks.flankOpening 8 5 3 = (5 : ℝ)/40 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 5 3 = (30 : ℝ)/40 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (15 : ℝ) * Flanks.flankOpening 8 5 3 = (15 : ℝ)/40 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (26 : ℝ) * Flanks.flankOpening 8 5 3 = (10 : ℝ)/40 + ((16 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 16 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 5 4 = (33 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 5 4 = (5 : ℝ)/40 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (13 : ℝ) * Flanks.flankOpening 8 5 4 = (29 : ℝ)/40 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 5 4 = (22 : ℝ)/40 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
      · rw [h, show (15 : ℝ) * Flanks.flankOpening 8 5 4 = (15 : ℝ)/40 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (26 : ℝ) * Flanks.flankOpening 8 5 4 = (18 : ℝ)/40 + ((21 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 21 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 25 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 26 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 26 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (25 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (10 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (35 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (20 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (5 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (30 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (15 : ℝ)/40 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 5 = 4 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 4 = (24 : ℝ)/40 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (25 : ℝ)/40 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (10 : ℝ)/40 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (35 : ℝ)/40 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (20 : ℝ)/40 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (5 : ℝ)/40 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (30 : ℝ)/40 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (15 : ℝ)/40 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 5 = 4 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 4 = (8 : ℝ)/40 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (25 : ℝ)/40 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (10 : ℝ)/40 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (35 : ℝ)/40 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((20 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (20 : ℝ)/40 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((21 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (5 : ℝ)/40 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((22 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (30 : ℝ)/40 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((23 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (15 : ℝ)/40 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 5 = 4 from rfl,
        show (((24 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 4 = (32 : ℝ)/40 + ((19 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 19 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((25 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (25 : ℝ)/40 + ((15 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 15 (by norm_num) (by norm_num)

/-- **Family 47**: differences `{2, 13, 15, 17, 21, x, 26}`, flank `13`, period `13`, uncovered residues `{1, 2, 4, 8, 10}`.  Covers 2 census rows. -/
theorem family47_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 26) :
    ∃ k : ℕ, Lonely 8 ({2, 13, 15, 17, 21, x, 26} : Finset ℝ) (Flanks.flankOpening 8 13 k) := by
  have hq : ((13 : ℕ) : ℝ) * (x / 13) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 13
    {1, 2, 4, 8, 10} ⟨1, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((13 : ℕ) : ℝ) * (d / 13) = d * 13 / 13 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (2 : ℝ) * 13 / 13 = ((2 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 2
    · rw [show (13 : ℝ) * 13 / 13 = ((13 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 13
    · rw [show (15 : ℝ) * 13 / 13 = ((15 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 15
    · rw [show (17 : ℝ) * 13 / 13 = ((17 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 17
    · rw [show (21 : ℝ) * 13 / 13 = ((21 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 21
    · exact absurd h hdx
    · rw [show (26 : ℝ) * 13 / 13 = ((26 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 26
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 13 1 = (18 : ℝ)/104 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (13 : ℝ) * Flanks.flankOpening 8 13 1 = (13 : ℝ)/104 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (15 : ℝ) * Flanks.flankOpening 8 13 1 = (31 : ℝ)/104 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (17 : ℝ) * Flanks.flankOpening 8 13 1 = (49 : ℝ)/104 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (21 : ℝ) * Flanks.flankOpening 8 13 1 = (85 : ℝ)/104 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (26 : ℝ) * Flanks.flankOpening 8 13 1 = (26 : ℝ)/104 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 13 2 = (34 : ℝ)/104 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (13 : ℝ) * Flanks.flankOpening 8 13 2 = (13 : ℝ)/104 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (15 : ℝ) * Flanks.flankOpening 8 13 2 = (47 : ℝ)/104 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (17 : ℝ) * Flanks.flankOpening 8 13 2 = (81 : ℝ)/104 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (21 : ℝ) * Flanks.flankOpening 8 13 2 = (45 : ℝ)/104 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (26 : ℝ) * Flanks.flankOpening 8 13 2 = (26 : ℝ)/104 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 13 4 = (66 : ℝ)/104 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (13 : ℝ) * Flanks.flankOpening 8 13 4 = (13 : ℝ)/104 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (15 : ℝ) * Flanks.flankOpening 8 13 4 = (79 : ℝ)/104 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (17 : ℝ) * Flanks.flankOpening 8 13 4 = (41 : ℝ)/104 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (21 : ℝ) * Flanks.flankOpening 8 13 4 = (69 : ℝ)/104 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (26 : ℝ) * Flanks.flankOpening 8 13 4 = (26 : ℝ)/104 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 13 8 = (26 : ℝ)/104 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (13 : ℝ) * Flanks.flankOpening 8 13 8 = (13 : ℝ)/104 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (15 : ℝ) * Flanks.flankOpening 8 13 8 = (39 : ℝ)/104 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
      · rw [h, show (17 : ℝ) * Flanks.flankOpening 8 13 8 = (65 : ℝ)/104 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
      · rw [h, show (21 : ℝ) * Flanks.flankOpening 8 13 8 = (13 : ℝ)/104 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (26 : ℝ) * Flanks.flankOpening 8 13 8 = (26 : ℝ)/104 + ((16 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 16 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 13 10 = (58 : ℝ)/104 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (13 : ℝ) * Flanks.flankOpening 8 13 10 = (13 : ℝ)/104 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
      · rw [h, show (15 : ℝ) * Flanks.flankOpening 8 13 10 = (71 : ℝ)/104 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
      · rw [h, show (17 : ℝ) * Flanks.flankOpening 8 13 10 = (25 : ℝ)/104 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
      · rw [h, show (21 : ℝ) * Flanks.flankOpening 8 13 10 = (37 : ℝ)/104 + ((16 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 16 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (26 : ℝ) * Flanks.flankOpening 8 13 10 = (26 : ℝ)/104 + ((20 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 20 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 25 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 26 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 26 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 13 = 2 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 2 = (17 : ℝ)/104 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 13 = 1 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 1 = (18 : ℝ)/104 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 13 = 1 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 1 = (27 : ℝ)/104 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 13 = 1 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 1 = (36 : ℝ)/104 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 13 = 1 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 1 = (45 : ℝ)/104 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 13 = 1 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 1 = (54 : ℝ)/104 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 13 = 1 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 1 = (63 : ℝ)/104 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 13 = 1 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 1 = (72 : ℝ)/104 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 13 = 1 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 1 = (81 : ℝ)/104 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 13 = 1 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 1 = (90 : ℝ)/104 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 13 = 2 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 2 = (83 : ℝ)/104 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 13 = 4 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 4 = (84 : ℝ)/104 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 13 = 1 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 1 = (13 : ℝ)/104 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 13 = 1 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 1 = (22 : ℝ)/104 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 13 = 1 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 1 = (31 : ℝ)/104 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 13 = 1 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 1 = (40 : ℝ)/104 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 13 = 1 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 1 = (49 : ℝ)/104 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 13 = 1 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 1 = (58 : ℝ)/104 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 13 = 1 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 1 = (67 : ℝ)/104 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 13 = 1 from rfl,
        show (((20 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 1 = (76 : ℝ)/104 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 13 = 1 from rfl,
        show (((21 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 1 = (85 : ℝ)/104 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 13 = 2 from rfl,
        show (((22 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 2 = (62 : ℝ)/104 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 13 = 2 from rfl,
        show (((23 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 2 = (79 : ℝ)/104 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 13 = 4 from rfl,
        show (((24 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 4 = (64 : ℝ)/104 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 13 = 1 from rfl,
        show (((25 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 1 = (17 : ℝ)/104 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)

/-- **Family 48**: differences `{1, 5, 12, 13, 14, x, 28}`, flank `12`, period `12`, uncovered residues `{3, 4, 6}`.  Covers 2 census rows. -/
theorem family48_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 28) :
    ∃ k : ℕ, Lonely 8 ({1, 5, 12, 13, 14, x, 28} : Finset ℝ) (Flanks.flankOpening 8 12 k) := by
  have hq : ((12 : ℕ) : ℝ) * (x / 12) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 12
    {3, 4, 6} ⟨3, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((12 : ℕ) : ℝ) * (d / 12) = d * 12 / 12 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 12 / 12 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (5 : ℝ) * 12 / 12 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (12 : ℝ) * 12 / 12 = ((12 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 12
    · rw [show (13 : ℝ) * 12 / 12 = ((13 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 13
    · rw [show (14 : ℝ) * 12 / 12 = ((14 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 14
    · exact absurd h hdx
    · rw [show (28 : ℝ) * 12 / 12 = ((28 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 28
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 12 3 = (25 : ℝ)/96 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 12 3 = (29 : ℝ)/96 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 12 3 = (12 : ℝ)/96 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (13 : ℝ) * Flanks.flankOpening 8 12 3 = (37 : ℝ)/96 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 12 3 = (62 : ℝ)/96 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 12 3 = (28 : ℝ)/96 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 12 4 = (33 : ℝ)/96 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 12 4 = (69 : ℝ)/96 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 12 4 = (12 : ℝ)/96 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (13 : ℝ) * Flanks.flankOpening 8 12 4 = (45 : ℝ)/96 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 12 4 = (78 : ℝ)/96 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 12 4 = (60 : ℝ)/96 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 12 6 = (49 : ℝ)/96 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 12 6 = (53 : ℝ)/96 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 12 6 = (12 : ℝ)/96 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (13 : ℝ) * Flanks.flankOpening 8 12 6 = (61 : ℝ)/96 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 12 6 = (14 : ℝ)/96 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 12 6 = (28 : ℝ)/96 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 27 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 28 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 28 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 12 = 3 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 12 3 = (25 : ℝ)/96 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 12 = 3 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 12 3 = (50 : ℝ)/96 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 12 = 3 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 12 3 = (75 : ℝ)/96 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 12 = 4 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 12 4 = (36 : ℝ)/96 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 12 = 3 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 12 3 = (29 : ℝ)/96 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 12 = 3 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 12 3 = (54 : ℝ)/96 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 12 = 3 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 12 3 = (79 : ℝ)/96 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 12 = 4 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 12 4 = (72 : ℝ)/96 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 12 = 3 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 12 3 = (33 : ℝ)/96 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 12 = 3 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 12 3 = (58 : ℝ)/96 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 12 = 3 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 12 3 = (83 : ℝ)/96 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 12 = 3 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 12 3 = (12 : ℝ)/96 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 12 = 3 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 12 3 = (37 : ℝ)/96 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 12 = 3 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 12 3 = (62 : ℝ)/96 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 12 = 4 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 12 4 = (15 : ℝ)/96 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 12 = 3 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 12 3 = (16 : ℝ)/96 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 12 = 3 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 12 3 = (41 : ℝ)/96 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 12 = 3 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 12 3 = (66 : ℝ)/96 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 12 = 4 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 12 4 = (51 : ℝ)/96 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 12 = 3 from rfl,
        show (((20 : ℤ)) : ℝ) * Flanks.flankOpening 8 12 3 = (20 : ℝ)/96 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 12 = 3 from rfl,
        show (((21 : ℤ)) : ℝ) * Flanks.flankOpening 8 12 3 = (45 : ℝ)/96 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 12 = 3 from rfl,
        show (((22 : ℤ)) : ℝ) * Flanks.flankOpening 8 12 3 = (70 : ℝ)/96 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 12 = 6 from rfl,
        show (((23 : ℤ)) : ℝ) * Flanks.flankOpening 8 12 6 = (71 : ℝ)/96 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 12 = 3 from rfl,
        show (((24 : ℤ)) : ℝ) * Flanks.flankOpening 8 12 3 = (24 : ℝ)/96 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 12 = 3 from rfl,
        show (((25 : ℤ)) : ℝ) * Flanks.flankOpening 8 12 3 = (49 : ℝ)/96 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 12 = 3 from rfl,
        show (((26 : ℤ)) : ℝ) * Flanks.flankOpening 8 12 3 = (74 : ℝ)/96 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 12 = 4 from rfl,
        show (((27 : ℤ)) : ℝ) * Flanks.flankOpening 8 12 4 = (27 : ℝ)/96 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)

/-- **Family 49**: differences `{1, 6, 8, 14, 15, x, 28}`, flank `6`, period `6`, uncovered residues `{1, 3, 4}`.  Covers 2 census rows. -/
theorem family49_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 28) :
    ∃ k : ℕ, Lonely 8 ({1, 6, 8, 14, 15, x, 28} : Finset ℝ) (Flanks.flankOpening 8 6 k) := by
  have hq : ((6 : ℕ) : ℝ) * (x / 6) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 6
    {1, 3, 4} ⟨1, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((6 : ℕ) : ℝ) * (d / 6) = d * 6 / 6 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 6 / 6 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (6 : ℝ) * 6 / 6 = ((6 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 6
    · rw [show (8 : ℝ) * 6 / 6 = ((8 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 8
    · rw [show (14 : ℝ) * 6 / 6 = ((14 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 14
    · rw [show (15 : ℝ) * 6 / 6 = ((15 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 15
    · exact absurd h hdx
    · rw [show (28 : ℝ) * 6 / 6 = ((28 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 28
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 6 1 = (9 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 6 1 = (6 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 6 1 = (24 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 6 1 = (30 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (15 : ℝ) * Flanks.flankOpening 8 6 1 = (39 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 6 1 = (12 : ℝ)/48 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 6 3 = (25 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 6 3 = (6 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 6 3 = (8 : ℝ)/48 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 6 3 = (14 : ℝ)/48 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (15 : ℝ) * Flanks.flankOpening 8 6 3 = (39 : ℝ)/48 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 6 3 = (28 : ℝ)/48 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 6 4 = (33 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 6 4 = (6 : ℝ)/48 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (8 : ℝ) * Flanks.flankOpening 8 6 4 = (24 : ℝ)/48 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 6 4 = (30 : ℝ)/48 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
      · rw [h, show (15 : ℝ) * Flanks.flankOpening 8 6 4 = (15 : ℝ)/48 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 6 4 = (12 : ℝ)/48 + ((19 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 19 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 27 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 28 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 28 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (9 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (18 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (27 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (36 : ℝ)/48 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 6 = 3 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 3 = (29 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (6 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (15 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (24 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (33 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (42 : ℝ)/48 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 6 = 3 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 3 = (35 : ℝ)/48 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (12 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (21 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (30 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (39 : ℝ)/48 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 6 = 3 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 3 = (16 : ℝ)/48 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (9 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (18 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (27 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((20 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (36 : ℝ)/48 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 6 = 4 from rfl,
        show (((21 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 4 = (21 : ℝ)/48 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((22 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (6 : ℝ)/48 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((23 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (15 : ℝ)/48 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((24 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (24 : ℝ)/48 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((25 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (33 : ℝ)/48 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 6 = 1 from rfl,
        show (((26 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 1 = (42 : ℝ)/48 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 6 = 4 from rfl,
        show (((27 : ℤ)) : ℝ) * Flanks.flankOpening 8 6 4 = (27 : ℝ)/48 + ((18 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 18 (by norm_num) (by norm_num)

/-- **Family 50**: differences `{1, 6, 13, 14, 20, x, 28}`, flank `13`, period `13`, uncovered residues `{3, 6, 8}`.  Covers 2 census rows. -/
theorem family50_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 28) :
    ∃ k : ℕ, Lonely 8 ({1, 6, 13, 14, 20, x, 28} : Finset ℝ) (Flanks.flankOpening 8 13 k) := by
  have hq : ((13 : ℕ) : ℝ) * (x / 13) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 13
    {3, 6, 8} ⟨3, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((13 : ℕ) : ℝ) * (d / 13) = d * 13 / 13 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 13 / 13 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (6 : ℝ) * 13 / 13 = ((6 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 6
    · rw [show (13 : ℝ) * 13 / 13 = ((13 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 13
    · rw [show (14 : ℝ) * 13 / 13 = ((14 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 14
    · rw [show (20 : ℝ) * 13 / 13 = ((20 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 20
    · exact absurd h hdx
    · rw [show (28 : ℝ) * 13 / 13 = ((28 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 28
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 13 3 = (25 : ℝ)/104 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 13 3 = (46 : ℝ)/104 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (13 : ℝ) * Flanks.flankOpening 8 13 3 = (13 : ℝ)/104 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 13 3 = (38 : ℝ)/104 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 13 3 = (84 : ℝ)/104 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 13 3 = (76 : ℝ)/104 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 13 6 = (49 : ℝ)/104 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 13 6 = (86 : ℝ)/104 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (13 : ℝ) * Flanks.flankOpening 8 13 6 = (13 : ℝ)/104 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 13 6 = (62 : ℝ)/104 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 13 6 = (44 : ℝ)/104 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 13 6 = (20 : ℝ)/104 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 13 8 = (65 : ℝ)/104 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (6 : ℝ) * Flanks.flankOpening 8 13 8 = (78 : ℝ)/104 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (13 : ℝ) * Flanks.flankOpening 8 13 8 = (13 : ℝ)/104 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 13 8 = (78 : ℝ)/104 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 13 8 = (52 : ℝ)/104 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 13 8 = (52 : ℝ)/104 + ((17 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 17 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 27 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 28 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 28 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 13 = 3 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 3 = (25 : ℝ)/104 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 13 = 3 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 3 = (50 : ℝ)/104 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 13 = 3 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 3 = (75 : ℝ)/104 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨8, by decide, 0, ?_⟩
      rw [show (8 : ℕ) + 0 * 13 = 8 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 8 = (52 : ℝ)/104 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 13 = 3 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 3 = (21 : ℝ)/104 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 13 = 3 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 3 = (46 : ℝ)/104 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 13 = 3 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 3 = (71 : ℝ)/104 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 13 = 6 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 6 = (80 : ℝ)/104 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 13 = 3 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 3 = (17 : ℝ)/104 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 13 = 3 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 3 = (42 : ℝ)/104 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 13 = 3 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 3 = (67 : ℝ)/104 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 13 = 6 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 6 = (68 : ℝ)/104 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 13 = 3 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 3 = (13 : ℝ)/104 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 13 = 3 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 3 = (38 : ℝ)/104 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 13 = 3 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 3 = (63 : ℝ)/104 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 13 = 3 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 3 = (88 : ℝ)/104 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨8, by decide, 0, ?_⟩
      rw [show (8 : ℕ) + 0 * 13 = 8 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 8 = (65 : ℝ)/104 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 13 = 3 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 3 = (34 : ℝ)/104 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 13 = 3 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 3 = (59 : ℝ)/104 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 13 = 3 from rfl,
        show (((20 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 3 = (84 : ℝ)/104 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨8, by decide, 0, ?_⟩
      rw [show (8 : ℕ) + 0 * 13 = 8 from rfl,
        show (((21 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 8 = (13 : ℝ)/104 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 13 = 3 from rfl,
        show (((22 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 3 = (30 : ℝ)/104 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 13 = 3 from rfl,
        show (((23 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 3 = (55 : ℝ)/104 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 13 = 3 from rfl,
        show (((24 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 3 = (80 : ℝ)/104 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 13 = 6 from rfl,
        show (((25 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 6 = (81 : ℝ)/104 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 13 = 3 from rfl,
        show (((26 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 3 = (26 : ℝ)/104 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 13 = 3 from rfl,
        show (((27 : ℤ)) : ℝ) * Flanks.flankOpening 8 13 3 = (51 : ℝ)/104 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)

/-- **Family 51**: differences `{1, 14, 15, 16, 23, x, 28}`, flank `14`, period `14`, uncovered residues `{2, 3, 4, 5, 7, 8, 10}`.  Covers 2 census rows. -/
theorem family51_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 28) :
    ∃ k : ℕ, Lonely 8 ({1, 14, 15, 16, 23, x, 28} : Finset ℝ) (Flanks.flankOpening 8 14 k) := by
  have hq : ((14 : ℕ) : ℝ) * (x / 14) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 14
    {2, 3, 4, 5, 7, 8, 10} ⟨2, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((14 : ℕ) : ℝ) * (d / 14) = d * 14 / 14 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 14 / 14 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (14 : ℝ) * 14 / 14 = ((14 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 14
    · rw [show (15 : ℝ) * 14 / 14 = ((15 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 15
    · rw [show (16 : ℝ) * 14 / 14 = ((16 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 16
    · rw [show (23 : ℝ) * 14 / 14 = ((23 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 23
    · exact absurd h hdx
    · rw [show (28 : ℝ) * 14 / 14 = ((28 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 28
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr | hr | hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 14 2 = (17 : ℝ)/112 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 14 2 = (14 : ℝ)/112 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (15 : ℝ) * Flanks.flankOpening 8 14 2 = (31 : ℝ)/112 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 14 2 = (48 : ℝ)/112 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (23 : ℝ) * Flanks.flankOpening 8 14 2 = (55 : ℝ)/112 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 14 2 = (28 : ℝ)/112 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 14 3 = (25 : ℝ)/112 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 14 3 = (14 : ℝ)/112 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (15 : ℝ) * Flanks.flankOpening 8 14 3 = (39 : ℝ)/112 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 14 3 = (64 : ℝ)/112 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (23 : ℝ) * Flanks.flankOpening 8 14 3 = (15 : ℝ)/112 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 14 3 = (28 : ℝ)/112 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 14 4 = (33 : ℝ)/112 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 14 4 = (14 : ℝ)/112 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (15 : ℝ) * Flanks.flankOpening 8 14 4 = (47 : ℝ)/112 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 14 4 = (80 : ℝ)/112 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (23 : ℝ) * Flanks.flankOpening 8 14 4 = (87 : ℝ)/112 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 14 4 = (28 : ℝ)/112 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 14 5 = (41 : ℝ)/112 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 14 5 = (14 : ℝ)/112 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (15 : ℝ) * Flanks.flankOpening 8 14 5 = (55 : ℝ)/112 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 14 5 = (96 : ℝ)/112 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (23 : ℝ) * Flanks.flankOpening 8 14 5 = (47 : ℝ)/112 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 14 5 = (28 : ℝ)/112 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 14 7 = (57 : ℝ)/112 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 14 7 = (14 : ℝ)/112 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (15 : ℝ) * Flanks.flankOpening 8 14 7 = (71 : ℝ)/112 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 14 7 = (16 : ℝ)/112 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (23 : ℝ) * Flanks.flankOpening 8 14 7 = (79 : ℝ)/112 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 14 7 = (28 : ℝ)/112 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 14 8 = (65 : ℝ)/112 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 14 8 = (14 : ℝ)/112 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (15 : ℝ) * Flanks.flankOpening 8 14 8 = (79 : ℝ)/112 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 14 8 = (32 : ℝ)/112 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
      · rw [h, show (23 : ℝ) * Flanks.flankOpening 8 14 8 = (39 : ℝ)/112 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 14 8 = (28 : ℝ)/112 + ((16 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 16 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 14 10 = (81 : ℝ)/112 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 14 10 = (14 : ℝ)/112 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
      · rw [h, show (15 : ℝ) * Flanks.flankOpening 8 14 10 = (95 : ℝ)/112 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 14 10 = (64 : ℝ)/112 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
      · rw [h, show (23 : ℝ) * Flanks.flankOpening 8 14 10 = (71 : ℝ)/112 + ((16 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 16 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 14 10 = (28 : ℝ)/112 + ((20 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 20 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 27 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 28 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 28 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (17 : ℝ)/112 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (34 : ℝ)/112 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (51 : ℝ)/112 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (68 : ℝ)/112 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (85 : ℝ)/112 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 14 = 3 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 3 = (38 : ℝ)/112 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 14 = 3 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 3 = (63 : ℝ)/112 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (24 : ℝ)/112 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (41 : ℝ)/112 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (58 : ℝ)/112 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (75 : ℝ)/112 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (92 : ℝ)/112 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 14 = 4 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 4 = (93 : ℝ)/112 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (14 : ℝ)/112 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (31 : ℝ)/112 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (48 : ℝ)/112 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (65 : ℝ)/112 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (82 : ℝ)/112 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 14 = 3 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 3 = (27 : ℝ)/112 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 14 = 3 from rfl,
        show (((20 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 3 = (52 : ℝ)/112 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((21 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (21 : ℝ)/112 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((22 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (38 : ℝ)/112 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((23 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (55 : ℝ)/112 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((24 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (72 : ℝ)/112 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((25 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (89 : ℝ)/112 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 14 = 3 from rfl,
        show (((26 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 3 = (90 : ℝ)/112 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨7, by decide, 0, ?_⟩
      rw [show (7 : ℕ) + 0 * 14 = 7 from rfl,
        show (((27 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 7 = (83 : ℝ)/112 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)

/-- **Family 52**: differences `{2, 5, 12, 14, 19, x, 28}`, flank `5`, period `5`, uncovered residues `{1, 3}`.  Covers 2 census rows. -/
theorem family52_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 28) :
    ∃ k : ℕ, Lonely 8 ({2, 5, 12, 14, 19, x, 28} : Finset ℝ) (Flanks.flankOpening 8 5 k) := by
  have hq : ((5 : ℕ) : ℝ) * (x / 5) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 5
    {1, 3} ⟨1, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((5 : ℕ) : ℝ) * (d / 5) = d * 5 / 5 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (2 : ℝ) * 5 / 5 = ((2 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 2
    · rw [show (5 : ℝ) * 5 / 5 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (12 : ℝ) * 5 / 5 = ((12 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 12
    · rw [show (14 : ℝ) * 5 / 5 = ((14 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 14
    · rw [show (19 : ℝ) * 5 / 5 = ((19 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 19
    · exact absurd h hdx
    · rw [show (28 : ℝ) * 5 / 5 = ((28 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 28
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 5 1 = (18 : ℝ)/40 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 5 1 = (5 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 5 1 = (28 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 5 1 = (6 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (19 : ℝ) * Flanks.flankOpening 8 5 1 = (11 : ℝ)/40 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 5 1 = (12 : ℝ)/40 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (2 : ℝ) * Flanks.flankOpening 8 5 3 = (10 : ℝ)/40 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 5 3 = (5 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 5 3 = (20 : ℝ)/40 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 5 3 = (30 : ℝ)/40 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (19 : ℝ) * Flanks.flankOpening 8 5 3 = (35 : ℝ)/40 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 5 3 = (20 : ℝ)/40 + ((17 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 17 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 27 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 28 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 28 := by exact_mod_cast hh
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
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (10 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (19 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (28 : ℝ)/40 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (5 : ℝ)/40 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (6 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (15 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (24 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (33 : ℝ)/40 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (10 : ℝ)/40 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (11 : ℝ)/40 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((20 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (20 : ℝ)/40 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((21 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (29 : ℝ)/40 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((22 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (30 : ℝ)/40 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((23 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (7 : ℝ)/40 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((24 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (16 : ℝ)/40 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((25 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (25 : ℝ)/40 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨1, by decide, 0, ?_⟩
      rw [show (1 : ℕ) + 0 * 5 = 1 from rfl,
        show (((26 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 1 = (34 : ℝ)/40 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 5 = 3 from rfl,
        show (((27 : ℤ)) : ℝ) * Flanks.flankOpening 8 5 3 = (35 : ℝ)/40 + ((16 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 16 (by norm_num) (by norm_num)

/-- **Family 53**: differences `{3, 10, 14, 17, 24, x, 28}`, flank `10`, period `10`, uncovered residues `{5, 6, 8}`.  Covers 2 census rows. -/
theorem family53_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 28) :
    ∃ k : ℕ, Lonely 8 ({3, 10, 14, 17, 24, x, 28} : Finset ℝ) (Flanks.flankOpening 8 10 k) := by
  have hq : ((10 : ℕ) : ℝ) * (x / 10) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 10
    {5, 6, 8} ⟨5, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((10 : ℕ) : ℝ) * (d / 10) = d * 10 / 10 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (3 : ℝ) * 10 / 10 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (10 : ℝ) * 10 / 10 = ((10 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 10
    · rw [show (14 : ℝ) * 10 / 10 = ((14 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 14
    · rw [show (17 : ℝ) * 10 / 10 = ((17 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 17
    · rw [show (24 : ℝ) * 10 / 10 = ((24 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 24
    · exact absurd h hdx
    · rw [show (28 : ℝ) * 10 / 10 = ((28 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 28
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 10 5 = (43 : ℝ)/80 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 10 5 = (10 : ℝ)/80 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 10 5 = (14 : ℝ)/80 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (17 : ℝ) * Flanks.flankOpening 8 10 5 = (57 : ℝ)/80 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (24 : ℝ) * Flanks.flankOpening 8 10 5 = (24 : ℝ)/80 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 10 5 = (28 : ℝ)/80 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 10 6 = (67 : ℝ)/80 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 10 6 = (10 : ℝ)/80 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 10 6 = (46 : ℝ)/80 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (17 : ℝ) * Flanks.flankOpening 8 10 6 = (33 : ℝ)/80 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
      · rw [h, show (24 : ℝ) * Flanks.flankOpening 8 10 6 = (56 : ℝ)/80 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 10 6 = (12 : ℝ)/80 + ((17 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 17 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 10 8 = (35 : ℝ)/80 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (10 : ℝ) * Flanks.flankOpening 8 10 8 = (10 : ℝ)/80 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 10 8 = (30 : ℝ)/80 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
      · rw [h, show (17 : ℝ) * Flanks.flankOpening 8 10 8 = (65 : ℝ)/80 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
      · rw [h, show (24 : ℝ) * Flanks.flankOpening 8 10 8 = (40 : ℝ)/80 + ((19 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 19 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 10 8 = (60 : ℝ)/80 + ((22 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 22 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 27 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 28 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 28 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 10 = 5 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 5 = (41 : ℝ)/80 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 10 = 6 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 6 = (18 : ℝ)/80 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 10 = 5 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 5 = (43 : ℝ)/80 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 10 = 6 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 6 = (36 : ℝ)/80 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 10 = 5 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 5 = (45 : ℝ)/80 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 10 = 6 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 6 = (54 : ℝ)/80 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 10 = 5 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 5 = (47 : ℝ)/80 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨8, by decide, 0, ?_⟩
      rw [show (8 : ℕ) + 0 * 10 = 8 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 8 = (40 : ℝ)/80 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 10 = 5 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 5 = (49 : ℝ)/80 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 10 = 5 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 5 = (10 : ℝ)/80 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 10 = 5 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 5 = (51 : ℝ)/80 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 10 = 5 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 5 = (12 : ℝ)/80 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 10 = 5 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 5 = (53 : ℝ)/80 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 10 = 5 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 5 = (14 : ℝ)/80 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 10 = 5 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 5 = (55 : ℝ)/80 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 10 = 5 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 5 = (16 : ℝ)/80 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 10 = 5 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 5 = (57 : ℝ)/80 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 10 = 5 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 5 = (18 : ℝ)/80 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 10 = 5 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 5 = (59 : ℝ)/80 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 10 = 5 from rfl,
        show (((20 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 5 = (20 : ℝ)/80 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 10 = 5 from rfl,
        show (((21 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 5 = (61 : ℝ)/80 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 10 = 5 from rfl,
        show (((22 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 5 = (22 : ℝ)/80 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 10 = 5 from rfl,
        show (((23 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 5 = (63 : ℝ)/80 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 10 = 5 from rfl,
        show (((24 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 5 = (24 : ℝ)/80 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 10 = 5 from rfl,
        show (((25 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 5 = (65 : ℝ)/80 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 10 = 5 from rfl,
        show (((26 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 5 = (26 : ℝ)/80 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 10 = 5 from rfl,
        show (((27 : ℤ)) : ℝ) * Flanks.flankOpening 8 10 5 = (67 : ℝ)/80 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)

/-- **Family 54**: differences `{3, 13, 14, 17, 20, x, 28}`, flank `14`, period `14`, uncovered residues `{6, 7, 8, 10, 12}`.  Covers 2 census rows. -/
theorem family54_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 28) :
    ∃ k : ℕ, Lonely 8 ({3, 13, 14, 17, 20, x, 28} : Finset ℝ) (Flanks.flankOpening 8 14 k) := by
  have hq : ((14 : ℕ) : ℝ) * (x / 14) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 14
    {6, 7, 8, 10, 12} ⟨6, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((14 : ℕ) : ℝ) * (d / 14) = d * 14 / 14 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (3 : ℝ) * 14 / 14 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (13 : ℝ) * 14 / 14 = ((13 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 13
    · rw [show (14 : ℝ) * 14 / 14 = ((14 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 14
    · rw [show (17 : ℝ) * 14 / 14 = ((17 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 17
    · rw [show (20 : ℝ) * 14 / 14 = ((20 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 20
    · exact absurd h hdx
    · rw [show (28 : ℝ) * 14 / 14 = ((28 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 28
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 14 6 = (35 : ℝ)/112 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (13 : ℝ) * Flanks.flankOpening 8 14 6 = (77 : ℝ)/112 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 14 6 = (14 : ℝ)/112 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (17 : ℝ) * Flanks.flankOpening 8 14 6 = (49 : ℝ)/112 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 14 6 = (84 : ℝ)/112 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 14 6 = (28 : ℝ)/112 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 14 7 = (59 : ℝ)/112 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (13 : ℝ) * Flanks.flankOpening 8 14 7 = (69 : ℝ)/112 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 14 7 = (14 : ℝ)/112 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (17 : ℝ) * Flanks.flankOpening 8 14 7 = (73 : ℝ)/112 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 14 7 = (20 : ℝ)/112 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 14 7 = (28 : ℝ)/112 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 14 8 = (83 : ℝ)/112 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (13 : ℝ) * Flanks.flankOpening 8 14 8 = (61 : ℝ)/112 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 14 8 = (14 : ℝ)/112 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (17 : ℝ) * Flanks.flankOpening 8 14 8 = (97 : ℝ)/112 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 14 8 = (68 : ℝ)/112 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 14 8 = (28 : ℝ)/112 + ((16 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 16 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 14 10 = (19 : ℝ)/112 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (13 : ℝ) * Flanks.flankOpening 8 14 10 = (45 : ℝ)/112 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 14 10 = (14 : ℝ)/112 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
      · rw [h, show (17 : ℝ) * Flanks.flankOpening 8 14 10 = (33 : ℝ)/112 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 14 10 = (52 : ℝ)/112 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 14 10 = (28 : ℝ)/112 + ((20 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 20 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 14 12 = (67 : ℝ)/112 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (13 : ℝ) * Flanks.flankOpening 8 14 12 = (29 : ℝ)/112 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 14 12 = (14 : ℝ)/112 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
      · rw [h, show (17 : ℝ) * Flanks.flankOpening 8 14 12 = (81 : ℝ)/112 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 14 12 = (36 : ℝ)/112 + ((17 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 17 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 14 12 = (28 : ℝ)/112 + ((24 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 24 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 27 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 28 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 28 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 14 = 6 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 6 = (49 : ℝ)/112 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 14 = 6 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 6 = (98 : ℝ)/112 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 14 = 6 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 6 = (35 : ℝ)/112 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 14 = 6 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 6 = (84 : ℝ)/112 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 14 = 6 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 6 = (21 : ℝ)/112 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 14 = 6 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 6 = (70 : ℝ)/112 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨7, by decide, 0, ?_⟩
      rw [show (7 : ℕ) + 0 * 14 = 7 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 7 = (63 : ℝ)/112 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 14 = 6 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 6 = (56 : ℝ)/112 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨7, by decide, 0, ?_⟩
      rw [show (7 : ℕ) + 0 * 14 = 7 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 7 = (65 : ℝ)/112 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 14 = 6 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 6 = (42 : ℝ)/112 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 14 = 6 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 6 = (91 : ℝ)/112 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 14 = 6 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 6 = (28 : ℝ)/112 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 14 = 6 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 6 = (77 : ℝ)/112 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 14 = 6 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 6 = (14 : ℝ)/112 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 14 = 6 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 6 = (63 : ℝ)/112 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨7, by decide, 0, ?_⟩
      rw [show (7 : ℕ) + 0 * 14 = 7 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 7 = (16 : ℝ)/112 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 14 = 6 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 6 = (49 : ℝ)/112 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 14 = 6 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 6 = (98 : ℝ)/112 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 14 = 6 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 6 = (35 : ℝ)/112 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 14 = 6 from rfl,
        show (((20 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 6 = (84 : ℝ)/112 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 14 = 6 from rfl,
        show (((21 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 6 = (21 : ℝ)/112 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 14 = 6 from rfl,
        show (((22 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 6 = (70 : ℝ)/112 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
    · refine ⟨7, by decide, 0, ?_⟩
      rw [show (7 : ℕ) + 0 * 14 = 7 from rfl,
        show (((23 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 7 = (79 : ℝ)/112 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 14 = 6 from rfl,
        show (((24 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 6 = (56 : ℝ)/112 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
    · refine ⟨7, by decide, 0, ?_⟩
      rw [show (7 : ℕ) + 0 * 14 = 7 from rfl,
        show (((25 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 7 = (81 : ℝ)/112 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 14 = 6 from rfl,
        show (((26 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 6 = (42 : ℝ)/112 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 14 = 6 from rfl,
        show (((27 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 6 = (91 : ℝ)/112 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)

/-- **Family 55**: differences `{3, 14, 17, 20, 26, x, 28}`, flank `14`, period `14`, uncovered residues `{3, 6, 7, 10, 12}`.  Covers 2 census rows. -/
theorem family55_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 28) :
    ∃ k : ℕ, Lonely 8 ({3, 14, 17, 20, 26, x, 28} : Finset ℝ) (Flanks.flankOpening 8 14 k) := by
  have hq : ((14 : ℕ) : ℝ) * (x / 14) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 14
    {3, 6, 7, 10, 12} ⟨3, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((14 : ℕ) : ℝ) * (d / 14) = d * 14 / 14 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (3 : ℝ) * 14 / 14 = ((3 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 3
    · rw [show (14 : ℝ) * 14 / 14 = ((14 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 14
    · rw [show (17 : ℝ) * 14 / 14 = ((17 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 17
    · rw [show (20 : ℝ) * 14 / 14 = ((20 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 20
    · rw [show (26 : ℝ) * 14 / 14 = ((26 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 26
    · exact absurd h hdx
    · rw [show (28 : ℝ) * 14 / 14 = ((28 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 28
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 14 3 = (75 : ℝ)/112 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 14 3 = (14 : ℝ)/112 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (17 : ℝ) * Flanks.flankOpening 8 14 3 = (89 : ℝ)/112 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 14 3 = (52 : ℝ)/112 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (26 : ℝ) * Flanks.flankOpening 8 14 3 = (90 : ℝ)/112 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 14 3 = (28 : ℝ)/112 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 14 6 = (35 : ℝ)/112 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 14 6 = (14 : ℝ)/112 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (17 : ℝ) * Flanks.flankOpening 8 14 6 = (49 : ℝ)/112 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 14 6 = (84 : ℝ)/112 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (26 : ℝ) * Flanks.flankOpening 8 14 6 = (42 : ℝ)/112 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 14 6 = (28 : ℝ)/112 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 14 7 = (59 : ℝ)/112 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 14 7 = (14 : ℝ)/112 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (17 : ℝ) * Flanks.flankOpening 8 14 7 = (73 : ℝ)/112 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 14 7 = (20 : ℝ)/112 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
      · rw [h, show (26 : ℝ) * Flanks.flankOpening 8 14 7 = (26 : ℝ)/112 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 14 7 = (28 : ℝ)/112 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 14 10 = (19 : ℝ)/112 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 14 10 = (14 : ℝ)/112 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
      · rw [h, show (17 : ℝ) * Flanks.flankOpening 8 14 10 = (33 : ℝ)/112 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 14 10 = (52 : ℝ)/112 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
      · rw [h, show (26 : ℝ) * Flanks.flankOpening 8 14 10 = (90 : ℝ)/112 + ((18 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 18 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 14 10 = (28 : ℝ)/112 + ((20 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 20 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (3 : ℝ) * Flanks.flankOpening 8 14 12 = (67 : ℝ)/112 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 14 12 = (14 : ℝ)/112 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
      · rw [h, show (17 : ℝ) * Flanks.flankOpening 8 14 12 = (81 : ℝ)/112 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 14 12 = (36 : ℝ)/112 + ((17 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 17 (by norm_num) (by norm_num)
      · rw [h, show (26 : ℝ) * Flanks.flankOpening 8 14 12 = (58 : ℝ)/112 + ((22 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 22 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 14 12 = (28 : ℝ)/112 + ((24 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 24 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 27 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 28 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 28 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 14 = 3 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 3 = (25 : ℝ)/112 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 14 = 3 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 3 = (50 : ℝ)/112 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 14 = 3 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 3 = (75 : ℝ)/112 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 14 = 6 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 6 = (84 : ℝ)/112 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 14 = 6 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 6 = (21 : ℝ)/112 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 14 = 3 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 3 = (38 : ℝ)/112 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 14 = 3 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 3 = (63 : ℝ)/112 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 14 = 3 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 3 = (88 : ℝ)/112 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨7, by decide, 0, ?_⟩
      rw [show (7 : ℕ) + 0 * 14 = 7 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 7 = (65 : ℝ)/112 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 14 = 3 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 3 = (26 : ℝ)/112 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 14 = 3 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 3 = (51 : ℝ)/112 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 14 = 3 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 3 = (76 : ℝ)/112 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 14 = 6 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 6 = (77 : ℝ)/112 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 14 = 3 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 3 = (14 : ℝ)/112 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 14 = 3 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 3 = (39 : ℝ)/112 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 14 = 3 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 3 = (64 : ℝ)/112 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 14 = 3 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 3 = (89 : ℝ)/112 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 14 = 6 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 6 = (98 : ℝ)/112 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 14 = 3 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 3 = (27 : ℝ)/112 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 14 = 3 from rfl,
        show (((20 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 3 = (52 : ℝ)/112 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 14 = 3 from rfl,
        show (((21 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 3 = (77 : ℝ)/112 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 14 = 6 from rfl,
        show (((22 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 6 = (70 : ℝ)/112 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 14 = 3 from rfl,
        show (((23 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 3 = (15 : ℝ)/112 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 14 = 3 from rfl,
        show (((24 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 3 = (40 : ℝ)/112 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 14 = 3 from rfl,
        show (((25 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 3 = (65 : ℝ)/112 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 14 = 3 from rfl,
        show (((26 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 3 = (90 : ℝ)/112 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 14 = 6 from rfl,
        show (((27 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 6 = (91 : ℝ)/112 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)

/-- **Family 56**: differences `{1, 21, 22, 23, 24, x, 30}`, flank `21`, period `21`, uncovered residues `{3, 5, 7, 12, 14, 15}`.  Covers 2 census rows. -/
theorem family56_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 30) :
    ∃ k : ℕ, Lonely 8 ({1, 21, 22, 23, 24, x, 30} : Finset ℝ) (Flanks.flankOpening 8 21 k) := by
  have hq : ((21 : ℕ) : ℝ) * (x / 21) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 21
    {3, 5, 7, 12, 14, 15} ⟨3, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((21 : ℕ) : ℝ) * (d / 21) = d * 21 / 21 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 21 / 21 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (21 : ℝ) * 21 / 21 = ((21 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 21
    · rw [show (22 : ℝ) * 21 / 21 = ((22 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 22
    · rw [show (23 : ℝ) * 21 / 21 = ((23 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 23
    · rw [show (24 : ℝ) * 21 / 21 = ((24 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 24
    · exact absurd h hdx
    · rw [show (30 : ℝ) * 21 / 21 = ((30 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 30
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr | hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 21 3 = (25 : ℝ)/168 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (21 : ℝ) * Flanks.flankOpening 8 21 3 = (21 : ℝ)/168 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (22 : ℝ) * Flanks.flankOpening 8 21 3 = (46 : ℝ)/168 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (23 : ℝ) * Flanks.flankOpening 8 21 3 = (71 : ℝ)/168 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (24 : ℝ) * Flanks.flankOpening 8 21 3 = (96 : ℝ)/168 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (30 : ℝ) * Flanks.flankOpening 8 21 3 = (78 : ℝ)/168 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 21 5 = (41 : ℝ)/168 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (21 : ℝ) * Flanks.flankOpening 8 21 5 = (21 : ℝ)/168 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (22 : ℝ) * Flanks.flankOpening 8 21 5 = (62 : ℝ)/168 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (23 : ℝ) * Flanks.flankOpening 8 21 5 = (103 : ℝ)/168 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (24 : ℝ) * Flanks.flankOpening 8 21 5 = (144 : ℝ)/168 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (30 : ℝ) * Flanks.flankOpening 8 21 5 = (54 : ℝ)/168 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 21 7 = (57 : ℝ)/168 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (21 : ℝ) * Flanks.flankOpening 8 21 7 = (21 : ℝ)/168 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (22 : ℝ) * Flanks.flankOpening 8 21 7 = (78 : ℝ)/168 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (23 : ℝ) * Flanks.flankOpening 8 21 7 = (135 : ℝ)/168 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (24 : ℝ) * Flanks.flankOpening 8 21 7 = (24 : ℝ)/168 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (30 : ℝ) * Flanks.flankOpening 8 21 7 = (30 : ℝ)/168 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 21 12 = (97 : ℝ)/168 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (21 : ℝ) * Flanks.flankOpening 8 21 12 = (21 : ℝ)/168 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
      · rw [h, show (22 : ℝ) * Flanks.flankOpening 8 21 12 = (118 : ℝ)/168 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
      · rw [h, show (23 : ℝ) * Flanks.flankOpening 8 21 12 = (47 : ℝ)/168 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
      · rw [h, show (24 : ℝ) * Flanks.flankOpening 8 21 12 = (144 : ℝ)/168 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (30 : ℝ) * Flanks.flankOpening 8 21 12 = (54 : ℝ)/168 + ((17 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 17 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 21 14 = (113 : ℝ)/168 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (21 : ℝ) * Flanks.flankOpening 8 21 14 = (21 : ℝ)/168 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
      · rw [h, show (22 : ℝ) * Flanks.flankOpening 8 21 14 = (134 : ℝ)/168 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
      · rw [h, show (23 : ℝ) * Flanks.flankOpening 8 21 14 = (79 : ℝ)/168 + ((15 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 15 (by norm_num) (by norm_num)
      · rw [h, show (24 : ℝ) * Flanks.flankOpening 8 21 14 = (24 : ℝ)/168 + ((16 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 16 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (30 : ℝ) * Flanks.flankOpening 8 21 14 = (30 : ℝ)/168 + ((20 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 20 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 21 15 = (121 : ℝ)/168 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (21 : ℝ) * Flanks.flankOpening 8 21 15 = (21 : ℝ)/168 + ((15 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 15 (by norm_num) (by norm_num)
      · rw [h, show (22 : ℝ) * Flanks.flankOpening 8 21 15 = (142 : ℝ)/168 + ((15 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 15 (by norm_num) (by norm_num)
      · rw [h, show (23 : ℝ) * Flanks.flankOpening 8 21 15 = (95 : ℝ)/168 + ((16 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 16 (by norm_num) (by norm_num)
      · rw [h, show (24 : ℝ) * Flanks.flankOpening 8 21 15 = (48 : ℝ)/168 + ((17 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 17 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (30 : ℝ) * Flanks.flankOpening 8 21 15 = (102 : ℝ)/168 + ((21 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 21 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 29 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 30 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 30 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 21 = 3 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 3 = (25 : ℝ)/168 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 21 = 3 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 3 = (50 : ℝ)/168 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 21 = 3 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 3 = (75 : ℝ)/168 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 21 = 3 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 3 = (100 : ℝ)/168 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 21 = 3 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 3 = (125 : ℝ)/168 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 21 = 5 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 5 = (78 : ℝ)/168 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 21 = 5 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 5 = (119 : ℝ)/168 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 21 = 3 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 3 = (32 : ℝ)/168 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 21 = 3 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 3 = (57 : ℝ)/168 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 21 = 3 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 3 = (82 : ℝ)/168 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 21 = 3 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 3 = (107 : ℝ)/168 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 21 = 3 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 3 = (132 : ℝ)/168 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 21 = 5 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 5 = (29 : ℝ)/168 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 21 = 5 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 5 = (70 : ℝ)/168 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 21 = 3 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 3 = (39 : ℝ)/168 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 21 = 3 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 3 = (64 : ℝ)/168 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 21 = 3 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 3 = (89 : ℝ)/168 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 21 = 3 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 3 = (114 : ℝ)/168 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 21 = 3 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 3 = (139 : ℝ)/168 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨7, by decide, 0, ?_⟩
      rw [show (7 : ℕ) + 0 * 21 = 7 from rfl,
        show (((20 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 7 = (132 : ℝ)/168 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 21 = 3 from rfl,
        show (((21 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 3 = (21 : ℝ)/168 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 21 = 3 from rfl,
        show (((22 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 3 = (46 : ℝ)/168 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 21 = 3 from rfl,
        show (((23 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 3 = (71 : ℝ)/168 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 21 = 3 from rfl,
        show (((24 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 3 = (96 : ℝ)/168 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 21 = 3 from rfl,
        show (((25 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 3 = (121 : ℝ)/168 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 21 = 3 from rfl,
        show (((26 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 3 = (146 : ℝ)/168 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 21 = 5 from rfl,
        show (((27 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 5 = (99 : ℝ)/168 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 21 = 3 from rfl,
        show (((28 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 3 = (28 : ℝ)/168 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 21 = 3 from rfl,
        show (((29 : ℤ)) : ℝ) * Flanks.flankOpening 8 21 3 = (53 : ℝ)/168 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)

/-- **Family 57**: differences `{4, 16, 20, 24, 28, x, 33}`, flank `28`, period `28`, uncovered residues `{2, 3, 6, 9, 13, 17, 20, 23, 24}`.  Covers 1 census rows. -/
theorem family57_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 33) :
    ∃ k : ℕ, Lonely 8 ({4, 16, 20, 24, 28, x, 33} : Finset ℝ) (Flanks.flankOpening 8 28 k) := by
  have hq : ((28 : ℕ) : ℝ) * (x / 28) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 28
    {2, 3, 6, 9, 13, 17, 20, 23, 24} ⟨2, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((28 : ℕ) : ℝ) * (d / 28) = d * 28 / 28 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (4 : ℝ) * 28 / 28 = ((4 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 4
    · rw [show (16 : ℝ) * 28 / 28 = ((16 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 16
    · rw [show (20 : ℝ) * 28 / 28 = ((20 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 20
    · rw [show (24 : ℝ) * 28 / 28 = ((24 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 24
    · rw [show (28 : ℝ) * 28 / 28 = ((28 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 28
    · exact absurd h hdx
    · rw [show (33 : ℝ) * 28 / 28 = ((33 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 33
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 28 2 = (68 : ℝ)/224 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 28 2 = (48 : ℝ)/224 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 28 2 = (116 : ℝ)/224 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (24 : ℝ) * Flanks.flankOpening 8 28 2 = (184 : ℝ)/224 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 28 2 = (28 : ℝ)/224 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (33 : ℝ) * Flanks.flankOpening 8 28 2 = (113 : ℝ)/224 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 28 3 = (100 : ℝ)/224 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 28 3 = (176 : ℝ)/224 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 28 3 = (52 : ℝ)/224 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (24 : ℝ) * Flanks.flankOpening 8 28 3 = (152 : ℝ)/224 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 28 3 = (28 : ℝ)/224 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (33 : ℝ) * Flanks.flankOpening 8 28 3 = (153 : ℝ)/224 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 28 6 = (196 : ℝ)/224 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 28 6 = (112 : ℝ)/224 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 28 6 = (84 : ℝ)/224 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (24 : ℝ) * Flanks.flankOpening 8 28 6 = (56 : ℝ)/224 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 28 6 = (28 : ℝ)/224 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (33 : ℝ) * Flanks.flankOpening 8 28 6 = (49 : ℝ)/224 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 28 9 = (68 : ℝ)/224 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 28 9 = (48 : ℝ)/224 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 28 9 = (116 : ℝ)/224 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (24 : ℝ) * Flanks.flankOpening 8 28 9 = (184 : ℝ)/224 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 28 9 = (28 : ℝ)/224 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (33 : ℝ) * Flanks.flankOpening 8 28 9 = (169 : ℝ)/224 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 28 13 = (196 : ℝ)/224 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 28 13 = (112 : ℝ)/224 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 28 13 = (84 : ℝ)/224 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
      · rw [h, show (24 : ℝ) * Flanks.flankOpening 8 28 13 = (56 : ℝ)/224 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 28 13 = (28 : ℝ)/224 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (33 : ℝ) * Flanks.flankOpening 8 28 13 = (105 : ℝ)/224 + ((15 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 15 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 28 17 = (100 : ℝ)/224 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 28 17 = (176 : ℝ)/224 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 28 17 = (52 : ℝ)/224 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
      · rw [h, show (24 : ℝ) * Flanks.flankOpening 8 28 17 = (152 : ℝ)/224 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 28 17 = (28 : ℝ)/224 + ((17 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 17 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (33 : ℝ) * Flanks.flankOpening 8 28 17 = (41 : ℝ)/224 + ((20 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 20 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 28 20 = (196 : ℝ)/224 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 28 20 = (112 : ℝ)/224 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 28 20 = (84 : ℝ)/224 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
      · rw [h, show (24 : ℝ) * Flanks.flankOpening 8 28 20 = (56 : ℝ)/224 + ((17 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 17 (by norm_num) (by norm_num)
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 28 20 = (28 : ℝ)/224 + ((20 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 20 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (33 : ℝ) * Flanks.flankOpening 8 28 20 = (161 : ℝ)/224 + ((23 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 23 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 28 23 = (68 : ℝ)/224 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 28 23 = (48 : ℝ)/224 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 28 23 = (116 : ℝ)/224 + ((16 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 16 (by norm_num) (by norm_num)
      · rw [h, show (24 : ℝ) * Flanks.flankOpening 8 28 23 = (184 : ℝ)/224 + ((19 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 19 (by norm_num) (by norm_num)
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 28 23 = (28 : ℝ)/224 + ((23 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 23 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (33 : ℝ) * Flanks.flankOpening 8 28 23 = (57 : ℝ)/224 + ((27 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 27 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 28 24 = (100 : ℝ)/224 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 28 24 = (176 : ℝ)/224 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 28 24 = (52 : ℝ)/224 + ((17 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 17 (by norm_num) (by norm_num)
      · rw [h, show (24 : ℝ) * Flanks.flankOpening 8 28 24 = (152 : ℝ)/224 + ((20 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 20 (by norm_num) (by norm_num)
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 28 24 = (28 : ℝ)/224 + ((24 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 24 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (33 : ℝ) * Flanks.flankOpening 8 28 24 = (97 : ℝ)/224 + ((28 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 28 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 32 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 33 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 33 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 28 = 6 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 6 = (49 : ℝ)/224 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 28 = 2 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 2 = (34 : ℝ)/224 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 28 = 2 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 2 = (51 : ℝ)/224 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 28 = 2 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 2 = (68 : ℝ)/224 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 28 = 2 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 2 = (85 : ℝ)/224 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 28 = 2 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 2 = (102 : ℝ)/224 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 28 = 2 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 2 = (119 : ℝ)/224 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 28 = 2 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 2 = (136 : ℝ)/224 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 28 = 2 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 2 = (153 : ℝ)/224 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 28 = 2 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 2 = (170 : ℝ)/224 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 28 = 2 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 2 = (187 : ℝ)/224 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 28 = 3 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 3 = (76 : ℝ)/224 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 28 = 3 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 3 = (101 : ℝ)/224 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 28 = 3 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 3 = (126 : ℝ)/224 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 28 = 2 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 2 = (31 : ℝ)/224 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 28 = 2 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 2 = (48 : ℝ)/224 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 28 = 2 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 2 = (65 : ℝ)/224 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 28 = 2 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 2 = (82 : ℝ)/224 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 28 = 2 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 2 = (99 : ℝ)/224 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 28 = 2 from rfl,
        show (((20 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 2 = (116 : ℝ)/224 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 28 = 2 from rfl,
        show (((21 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 2 = (133 : ℝ)/224 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 28 = 2 from rfl,
        show (((22 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 2 = (150 : ℝ)/224 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 28 = 2 from rfl,
        show (((23 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 2 = (167 : ℝ)/224 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 28 = 2 from rfl,
        show (((24 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 2 = (184 : ℝ)/224 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 28 = 3 from rfl,
        show (((25 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 3 = (177 : ℝ)/224 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 28 = 6 from rfl,
        show (((26 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 6 = (154 : ℝ)/224 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨9, by decide, 0, ?_⟩
      rw [show (9 : ℕ) + 0 * 28 = 9 from rfl,
        show (((27 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 9 = (179 : ℝ)/224 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 28 = 2 from rfl,
        show (((28 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 2 = (28 : ℝ)/224 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 28 = 2 from rfl,
        show (((29 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 2 = (45 : ℝ)/224 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 28 = 2 from rfl,
        show (((30 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 2 = (62 : ℝ)/224 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 28 = 2 from rfl,
        show (((31 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 2 = (79 : ℝ)/224 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 28 = 2 from rfl,
        show (((32 : ℤ)) : ℝ) * Flanks.flankOpening 8 28 2 = (96 : ℝ)/224 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)

/-- **Family 58**: differences `{4, 12, 16, 20, 28, x, 35}`, flank `20`, period `20`, uncovered residues `{3, 4, 8, 14, 18, 19}`.  Covers 1 census rows. -/
theorem family58_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 35) :
    ∃ k : ℕ, Lonely 8 ({4, 12, 16, 20, 28, x, 35} : Finset ℝ) (Flanks.flankOpening 8 20 k) := by
  have hq : ((20 : ℕ) : ℝ) * (x / 20) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 20
    {3, 4, 8, 14, 18, 19} ⟨3, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((20 : ℕ) : ℝ) * (d / 20) = d * 20 / 20 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (4 : ℝ) * 20 / 20 = ((4 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 4
    · rw [show (12 : ℝ) * 20 / 20 = ((12 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 12
    · rw [show (16 : ℝ) * 20 / 20 = ((16 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 16
    · rw [show (20 : ℝ) * 20 / 20 = ((20 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 20
    · rw [show (28 : ℝ) * 20 / 20 = ((28 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 28
    · exact absurd h hdx
    · rw [show (35 : ℝ) * 20 / 20 = ((35 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 35
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr | hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 20 3 = (100 : ℝ)/160 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 20 3 = (140 : ℝ)/160 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 20 3 = (80 : ℝ)/160 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 20 3 = (20 : ℝ)/160 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 20 3 = (60 : ℝ)/160 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (35 : ℝ) * Flanks.flankOpening 8 20 3 = (75 : ℝ)/160 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 20 4 = (132 : ℝ)/160 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 20 4 = (76 : ℝ)/160 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 20 4 = (48 : ℝ)/160 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 20 4 = (20 : ℝ)/160 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 20 4 = (124 : ℝ)/160 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (35 : ℝ) * Flanks.flankOpening 8 20 4 = (35 : ℝ)/160 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 20 8 = (100 : ℝ)/160 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 20 8 = (140 : ℝ)/160 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 20 8 = (80 : ℝ)/160 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 20 8 = (20 : ℝ)/160 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 20 8 = (60 : ℝ)/160 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (35 : ℝ) * Flanks.flankOpening 8 20 8 = (35 : ℝ)/160 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 20 14 = (132 : ℝ)/160 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 20 14 = (76 : ℝ)/160 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 20 14 = (48 : ℝ)/160 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 20 14 = (20 : ℝ)/160 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 20 14 = (124 : ℝ)/160 + ((19 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 19 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (35 : ℝ) * Flanks.flankOpening 8 20 14 = (115 : ℝ)/160 + ((24 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 24 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 20 18 = (100 : ℝ)/160 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 20 18 = (140 : ℝ)/160 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 20 18 = (80 : ℝ)/160 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 20 18 = (20 : ℝ)/160 + ((18 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 18 (by norm_num) (by norm_num)
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 20 18 = (60 : ℝ)/160 + ((25 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 25 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (35 : ℝ) * Flanks.flankOpening 8 20 18 = (115 : ℝ)/160 + ((31 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 31 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 20 19 = (132 : ℝ)/160 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 20 19 = (76 : ℝ)/160 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 20 19 = (48 : ℝ)/160 + ((15 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 15 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 20 19 = (20 : ℝ)/160 + ((19 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 19 (by norm_num) (by norm_num)
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 20 19 = (124 : ℝ)/160 + ((26 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 26 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (35 : ℝ) * Flanks.flankOpening 8 20 19 = (75 : ℝ)/160 + ((33 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 33 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 34 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 35 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 35 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (25 : ℝ)/160 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (50 : ℝ)/160 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (75 : ℝ)/160 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (100 : ℝ)/160 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (125 : ℝ)/160 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 20 = 4 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 4 = (38 : ℝ)/160 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 20 = 4 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 4 = (71 : ℝ)/160 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (40 : ℝ)/160 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (65 : ℝ)/160 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (90 : ℝ)/160 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (115 : ℝ)/160 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (140 : ℝ)/160 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 20 = 4 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 4 = (109 : ℝ)/160 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (30 : ℝ)/160 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (55 : ℝ)/160 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (80 : ℝ)/160 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (105 : ℝ)/160 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (130 : ℝ)/160 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨8, by decide, 0, ?_⟩
      rw [show (8 : ℕ) + 0 * 20 = 8 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 8 = (115 : ℝ)/160 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((20 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (20 : ℝ)/160 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((21 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (45 : ℝ)/160 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((22 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (70 : ℝ)/160 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((23 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (95 : ℝ)/160 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((24 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (120 : ℝ)/160 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 20 = 4 from rfl,
        show (((25 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 4 = (25 : ℝ)/160 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 20 = 4 from rfl,
        show (((26 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 4 = (58 : ℝ)/160 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((27 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (35 : ℝ)/160 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((28 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (60 : ℝ)/160 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((29 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (85 : ℝ)/160 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((30 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (110 : ℝ)/160 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((31 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (135 : ℝ)/160 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 20 = 4 from rfl,
        show (((32 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 4 = (96 : ℝ)/160 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((33 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (25 : ℝ)/160 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((34 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (50 : ℝ)/160 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)

/-- **Family 59**: differences `{1, 7, 18, 25, 32, x, 36}`, flank `18`, period `18`, uncovered residues `{3, 4, 8, 9, 11, 12}`.  Covers 1 census rows. -/
theorem family59_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 36) :
    ∃ k : ℕ, Lonely 8 ({1, 7, 18, 25, 32, x, 36} : Finset ℝ) (Flanks.flankOpening 8 18 k) := by
  have hq : ((18 : ℕ) : ℝ) * (x / 18) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 18
    {3, 4, 8, 9, 11, 12} ⟨3, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((18 : ℕ) : ℝ) * (d / 18) = d * 18 / 18 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 18 / 18 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (7 : ℝ) * 18 / 18 = ((7 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 7
    · rw [show (18 : ℝ) * 18 / 18 = ((18 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 18
    · rw [show (25 : ℝ) * 18 / 18 = ((25 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 25
    · rw [show (32 : ℝ) * 18 / 18 = ((32 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 32
    · exact absurd h hdx
    · rw [show (36 : ℝ) * 18 / 18 = ((36 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 36
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr | hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 18 3 = (25 : ℝ)/144 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 18 3 = (31 : ℝ)/144 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (18 : ℝ) * Flanks.flankOpening 8 18 3 = (18 : ℝ)/144 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (25 : ℝ) * Flanks.flankOpening 8 18 3 = (49 : ℝ)/144 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (32 : ℝ) * Flanks.flankOpening 8 18 3 = (80 : ℝ)/144 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (36 : ℝ) * Flanks.flankOpening 8 18 3 = (36 : ℝ)/144 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 18 4 = (33 : ℝ)/144 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 18 4 = (87 : ℝ)/144 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (18 : ℝ) * Flanks.flankOpening 8 18 4 = (18 : ℝ)/144 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (25 : ℝ) * Flanks.flankOpening 8 18 4 = (105 : ℝ)/144 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (32 : ℝ) * Flanks.flankOpening 8 18 4 = (48 : ℝ)/144 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (36 : ℝ) * Flanks.flankOpening 8 18 4 = (36 : ℝ)/144 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 18 8 = (65 : ℝ)/144 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 18 8 = (23 : ℝ)/144 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (18 : ℝ) * Flanks.flankOpening 8 18 8 = (18 : ℝ)/144 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (25 : ℝ) * Flanks.flankOpening 8 18 8 = (41 : ℝ)/144 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
      · rw [h, show (32 : ℝ) * Flanks.flankOpening 8 18 8 = (64 : ℝ)/144 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (36 : ℝ) * Flanks.flankOpening 8 18 8 = (36 : ℝ)/144 + ((16 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 16 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 18 9 = (73 : ℝ)/144 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 18 9 = (79 : ℝ)/144 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (18 : ℝ) * Flanks.flankOpening 8 18 9 = (18 : ℝ)/144 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
      · rw [h, show (25 : ℝ) * Flanks.flankOpening 8 18 9 = (97 : ℝ)/144 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
      · rw [h, show (32 : ℝ) * Flanks.flankOpening 8 18 9 = (32 : ℝ)/144 + ((16 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 16 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (36 : ℝ) * Flanks.flankOpening 8 18 9 = (36 : ℝ)/144 + ((18 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 18 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 18 11 = (89 : ℝ)/144 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 18 11 = (47 : ℝ)/144 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (18 : ℝ) * Flanks.flankOpening 8 18 11 = (18 : ℝ)/144 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
      · rw [h, show (25 : ℝ) * Flanks.flankOpening 8 18 11 = (65 : ℝ)/144 + ((15 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 15 (by norm_num) (by norm_num)
      · rw [h, show (32 : ℝ) * Flanks.flankOpening 8 18 11 = (112 : ℝ)/144 + ((19 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 19 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (36 : ℝ) * Flanks.flankOpening 8 18 11 = (36 : ℝ)/144 + ((22 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 22 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 18 12 = (97 : ℝ)/144 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (7 : ℝ) * Flanks.flankOpening 8 18 12 = (103 : ℝ)/144 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (18 : ℝ) * Flanks.flankOpening 8 18 12 = (18 : ℝ)/144 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
      · rw [h, show (25 : ℝ) * Flanks.flankOpening 8 18 12 = (121 : ℝ)/144 + ((16 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 16 (by norm_num) (by norm_num)
      · rw [h, show (32 : ℝ) * Flanks.flankOpening 8 18 12 = (80 : ℝ)/144 + ((21 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 21 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (36 : ℝ) * Flanks.flankOpening 8 18 12 = (36 : ℝ)/144 + ((24 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 24 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 35 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 36 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 36 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 18 = 3 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 3 = (25 : ℝ)/144 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 18 = 3 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 3 = (50 : ℝ)/144 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 18 = 3 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 3 = (75 : ℝ)/144 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 18 = 3 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 3 = (100 : ℝ)/144 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 18 = 3 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 3 = (125 : ℝ)/144 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 18 = 4 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 4 = (54 : ℝ)/144 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 18 = 3 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 3 = (31 : ℝ)/144 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 18 = 3 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 3 = (56 : ℝ)/144 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 18 = 3 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 3 = (81 : ℝ)/144 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 18 = 3 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 3 = (106 : ℝ)/144 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 18 = 4 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 4 = (75 : ℝ)/144 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 18 = 4 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 4 = (108 : ℝ)/144 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 18 = 3 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 3 = (37 : ℝ)/144 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 18 = 3 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 3 = (62 : ℝ)/144 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 18 = 3 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 3 = (87 : ℝ)/144 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 18 = 3 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 3 = (112 : ℝ)/144 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨8, by decide, 0, ?_⟩
      rw [show (8 : ℕ) + 0 * 18 = 8 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 8 = (97 : ℝ)/144 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 18 = 3 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 3 = (18 : ℝ)/144 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 18 = 3 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 3 = (43 : ℝ)/144 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 18 = 3 from rfl,
        show (((20 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 3 = (68 : ℝ)/144 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 18 = 3 from rfl,
        show (((21 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 3 = (93 : ℝ)/144 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 18 = 3 from rfl,
        show (((22 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 3 = (118 : ℝ)/144 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 18 = 4 from rfl,
        show (((23 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 4 = (39 : ℝ)/144 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 18 = 3 from rfl,
        show (((24 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 3 = (24 : ℝ)/144 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 18 = 3 from rfl,
        show (((25 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 3 = (49 : ℝ)/144 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 18 = 3 from rfl,
        show (((26 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 3 = (74 : ℝ)/144 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 18 = 3 from rfl,
        show (((27 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 3 = (99 : ℝ)/144 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 18 = 3 from rfl,
        show (((28 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 3 = (124 : ℝ)/144 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 18 = 4 from rfl,
        show (((29 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 4 = (93 : ℝ)/144 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 18 = 3 from rfl,
        show (((30 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 3 = (30 : ℝ)/144 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 18 = 3 from rfl,
        show (((31 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 3 = (55 : ℝ)/144 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 18 = 3 from rfl,
        show (((32 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 3 = (80 : ℝ)/144 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 18 = 3 from rfl,
        show (((33 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 3 = (105 : ℝ)/144 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 18 = 4 from rfl,
        show (((34 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 4 = (114 : ℝ)/144 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨8, by decide, 0, ?_⟩
      rw [show (8 : ℕ) + 0 * 18 = 8 from rfl,
        show (((35 : ℤ)) : ℝ) * Flanks.flankOpening 8 18 8 = (115 : ℝ)/144 + ((15 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 15 (by norm_num) (by norm_num)

/-- **Family 60**: differences `{5, 14, 18, 23, 32, x, 36}`, flank `14`, period `14`, uncovered residues `{2, 4, 5, 7}`.  Covers 1 census rows. -/
theorem family60_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 36) :
    ∃ k : ℕ, Lonely 8 ({5, 14, 18, 23, 32, x, 36} : Finset ℝ) (Flanks.flankOpening 8 14 k) := by
  have hq : ((14 : ℕ) : ℝ) * (x / 14) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 14
    {2, 4, 5, 7} ⟨2, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((14 : ℕ) : ℝ) * (d / 14) = d * 14 / 14 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (5 : ℝ) * 14 / 14 = ((5 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 5
    · rw [show (14 : ℝ) * 14 / 14 = ((14 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 14
    · rw [show (18 : ℝ) * 14 / 14 = ((18 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 18
    · rw [show (23 : ℝ) * 14 / 14 = ((23 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 23
    · rw [show (32 : ℝ) * 14 / 14 = ((32 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 32
    · exact absurd h hdx
    · rw [show (36 : ℝ) * 14 / 14 = ((36 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 36
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 14 2 = (85 : ℝ)/112 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 14 2 = (14 : ℝ)/112 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (18 : ℝ) * Flanks.flankOpening 8 14 2 = (82 : ℝ)/112 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (23 : ℝ) * Flanks.flankOpening 8 14 2 = (55 : ℝ)/112 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (32 : ℝ) * Flanks.flankOpening 8 14 2 = (96 : ℝ)/112 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (36 : ℝ) * Flanks.flankOpening 8 14 2 = (52 : ℝ)/112 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 14 4 = (53 : ℝ)/112 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 14 4 = (14 : ℝ)/112 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (18 : ℝ) * Flanks.flankOpening 8 14 4 = (34 : ℝ)/112 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (23 : ℝ) * Flanks.flankOpening 8 14 4 = (87 : ℝ)/112 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (32 : ℝ) * Flanks.flankOpening 8 14 4 = (48 : ℝ)/112 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (36 : ℝ) * Flanks.flankOpening 8 14 4 = (68 : ℝ)/112 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 14 5 = (93 : ℝ)/112 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 14 5 = (14 : ℝ)/112 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (18 : ℝ) * Flanks.flankOpening 8 14 5 = (66 : ℝ)/112 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (23 : ℝ) * Flanks.flankOpening 8 14 5 = (47 : ℝ)/112 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (32 : ℝ) * Flanks.flankOpening 8 14 5 = (80 : ℝ)/112 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (36 : ℝ) * Flanks.flankOpening 8 14 5 = (20 : ℝ)/112 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (5 : ℝ) * Flanks.flankOpening 8 14 7 = (61 : ℝ)/112 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (14 : ℝ) * Flanks.flankOpening 8 14 7 = (14 : ℝ)/112 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (18 : ℝ) * Flanks.flankOpening 8 14 7 = (18 : ℝ)/112 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
      · rw [h, show (23 : ℝ) * Flanks.flankOpening 8 14 7 = (79 : ℝ)/112 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
      · rw [h, show (32 : ℝ) * Flanks.flankOpening 8 14 7 = (32 : ℝ)/112 + ((16 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 16 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (36 : ℝ) * Flanks.flankOpening 8 14 7 = (36 : ℝ)/112 + ((18 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 18 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 35 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 36 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 36 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (17 : ℝ)/112 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (34 : ℝ)/112 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (51 : ℝ)/112 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (68 : ℝ)/112 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (85 : ℝ)/112 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 14 = 4 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 4 = (86 : ℝ)/112 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 14 = 5 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 5 = (63 : ℝ)/112 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (24 : ℝ)/112 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (41 : ℝ)/112 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (58 : ℝ)/112 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (75 : ℝ)/112 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (92 : ℝ)/112 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 14 = 4 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 4 = (93 : ℝ)/112 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (14 : ℝ)/112 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (31 : ℝ)/112 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (48 : ℝ)/112 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (65 : ℝ)/112 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (82 : ℝ)/112 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 14 = 4 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 4 = (67 : ℝ)/112 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 14 = 5 from rfl,
        show (((20 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 5 = (36 : ℝ)/112 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((21 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (21 : ℝ)/112 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((22 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (38 : ℝ)/112 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((23 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (55 : ℝ)/112 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((24 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (72 : ℝ)/112 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((25 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (89 : ℝ)/112 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 14 = 4 from rfl,
        show (((26 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 4 = (74 : ℝ)/112 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨7, by decide, 0, ?_⟩
      rw [show (7 : ℕ) + 0 * 14 = 7 from rfl,
        show (((27 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 7 = (83 : ℝ)/112 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((28 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (28 : ℝ)/112 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((29 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (45 : ℝ)/112 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((30 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (62 : ℝ)/112 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((31 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (79 : ℝ)/112 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((32 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (96 : ℝ)/112 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 14 = 4 from rfl,
        show (((33 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 4 = (81 : ℝ)/112 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((34 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (18 : ℝ)/112 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨2, by decide, 0, ?_⟩
      rw [show (2 : ℕ) + 0 * 14 = 2 from rfl,
        show (((35 : ℤ)) : ℝ) * Flanks.flankOpening 8 14 2 = (35 : ℝ)/112 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)

/-- **Family 61**: differences `{4, 12, 16, 20, 28, x, 37}`, flank `20`, period `20`, uncovered residues `{3, 4, 13, 14, 18, 19}`.  Covers 1 census rows. -/
theorem family61_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 37) :
    ∃ k : ℕ, Lonely 8 ({4, 12, 16, 20, 28, x, 37} : Finset ℝ) (Flanks.flankOpening 8 20 k) := by
  have hq : ((20 : ℕ) : ℝ) * (x / 20) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 20
    {3, 4, 13, 14, 18, 19} ⟨3, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((20 : ℕ) : ℝ) * (d / 20) = d * 20 / 20 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (4 : ℝ) * 20 / 20 = ((4 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 4
    · rw [show (12 : ℝ) * 20 / 20 = ((12 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 12
    · rw [show (16 : ℝ) * 20 / 20 = ((16 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 16
    · rw [show (20 : ℝ) * 20 / 20 = ((20 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 20
    · rw [show (28 : ℝ) * 20 / 20 = ((28 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 28
    · exact absurd h hdx
    · rw [show (37 : ℝ) * 20 / 20 = ((37 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 37
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr | hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 20 3 = (100 : ℝ)/160 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 20 3 = (140 : ℝ)/160 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 20 3 = (80 : ℝ)/160 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 20 3 = (20 : ℝ)/160 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 20 3 = (60 : ℝ)/160 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (37 : ℝ) * Flanks.flankOpening 8 20 3 = (125 : ℝ)/160 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 20 4 = (132 : ℝ)/160 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 20 4 = (76 : ℝ)/160 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 20 4 = (48 : ℝ)/160 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 20 4 = (20 : ℝ)/160 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 20 4 = (124 : ℝ)/160 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (37 : ℝ) * Flanks.flankOpening 8 20 4 = (101 : ℝ)/160 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 20 13 = (100 : ℝ)/160 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 20 13 = (140 : ℝ)/160 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 20 13 = (80 : ℝ)/160 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 20 13 = (20 : ℝ)/160 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 20 13 = (60 : ℝ)/160 + ((18 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 18 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (37 : ℝ) * Flanks.flankOpening 8 20 13 = (45 : ℝ)/160 + ((24 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 24 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 20 14 = (132 : ℝ)/160 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 20 14 = (76 : ℝ)/160 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 20 14 = (48 : ℝ)/160 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 20 14 = (20 : ℝ)/160 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 20 14 = (124 : ℝ)/160 + ((19 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 19 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (37 : ℝ) * Flanks.flankOpening 8 20 14 = (21 : ℝ)/160 + ((26 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 26 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 20 18 = (100 : ℝ)/160 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 20 18 = (140 : ℝ)/160 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 20 18 = (80 : ℝ)/160 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 20 18 = (20 : ℝ)/160 + ((18 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 18 (by norm_num) (by norm_num)
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 20 18 = (60 : ℝ)/160 + ((25 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 25 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (37 : ℝ) * Flanks.flankOpening 8 20 18 = (85 : ℝ)/160 + ((33 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 33 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (4 : ℝ) * Flanks.flankOpening 8 20 19 = (132 : ℝ)/160 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
      · rw [h, show (12 : ℝ) * Flanks.flankOpening 8 20 19 = (76 : ℝ)/160 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
      · rw [h, show (16 : ℝ) * Flanks.flankOpening 8 20 19 = (48 : ℝ)/160 + ((15 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 15 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 20 19 = (20 : ℝ)/160 + ((19 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 19 (by norm_num) (by norm_num)
      · rw [h, show (28 : ℝ) * Flanks.flankOpening 8 20 19 = (124 : ℝ)/160 + ((26 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 26 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (37 : ℝ) * Flanks.flankOpening 8 20 19 = (61 : ℝ)/160 + ((35 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 35 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 36 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 37 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 37 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (25 : ℝ)/160 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (50 : ℝ)/160 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (75 : ℝ)/160 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (100 : ℝ)/160 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (125 : ℝ)/160 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 20 = 4 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 4 = (38 : ℝ)/160 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 20 = 4 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 4 = (71 : ℝ)/160 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (40 : ℝ)/160 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (65 : ℝ)/160 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (90 : ℝ)/160 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (115 : ℝ)/160 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (140 : ℝ)/160 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 20 = 4 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 4 = (109 : ℝ)/160 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (30 : ℝ)/160 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (55 : ℝ)/160 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (80 : ℝ)/160 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (105 : ℝ)/160 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (130 : ℝ)/160 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨13, by decide, 0, ?_⟩
      rw [show (13 : ℕ) + 0 * 20 = 13 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 13 = (75 : ℝ)/160 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((20 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (20 : ℝ)/160 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((21 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (45 : ℝ)/160 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((22 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (70 : ℝ)/160 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((23 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (95 : ℝ)/160 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((24 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (120 : ℝ)/160 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 20 = 4 from rfl,
        show (((25 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 4 = (25 : ℝ)/160 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 20 = 4 from rfl,
        show (((26 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 4 = (58 : ℝ)/160 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((27 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (35 : ℝ)/160 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((28 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (60 : ℝ)/160 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((29 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (85 : ℝ)/160 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((30 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (110 : ℝ)/160 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((31 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (135 : ℝ)/160 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨4, by decide, 0, ?_⟩
      rw [show (4 : ℕ) + 0 * 20 = 4 from rfl,
        show (((32 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 4 = (96 : ℝ)/160 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((33 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (25 : ℝ)/160 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((34 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (50 : ℝ)/160 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((35 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (75 : ℝ)/160 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨3, by decide, 0, ?_⟩
      rw [show (3 : ℕ) + 0 * 20 = 3 from rfl,
        show (((36 : ℤ)) : ℝ) * Flanks.flankOpening 8 20 3 = (100 : ℝ)/160 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)

/-- **Family 62**: differences `{1, 11, 20, 21, 31, x, 40}`, flank `11`, period `11`, uncovered residues `{5, 6, 9}`.  Covers 1 census rows. -/
theorem family62_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < 40) :
    ∃ k : ℕ, Lonely 8 ({1, 11, 20, 21, 31, x, 40} : Finset ℝ) (Flanks.flankOpening 8 11 k) := by
  have hq : ((11 : ℕ) : ℝ) * (x / 11) = x := by push_cast; ring
  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num) 11
    {5, 6, 9} ⟨5, by decide⟩ ?_ ?_ ?_
  · intro d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have hc : ((11 : ℕ) : ℝ) * (d / 11) = d * 11 / 11 := by push_cast; ring
    rw [hc]
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · rw [show (1 : ℝ) * 11 / 11 = ((1 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 1
    · rw [show (11 : ℝ) * 11 / 11 = ((11 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 11
    · rw [show (20 : ℝ) * 11 / 11 = ((20 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 20
    · rw [show (21 : ℝ) * 11 / 11 = ((21 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 21
    · rw [show (31 : ℝ) * 11 / 11 = ((31 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 31
    · exact absurd h hdx
    · rw [show (40 : ℝ) * 11 / 11 = ((40 : ℤ) : ℝ) by norm_num]
      exact Int.fract_intCast 40
  · intro r hr d hd hdx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr
    rcases hr with hr | hr | hr <;> subst hr
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 11 5 = (41 : ℝ)/88 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (11 : ℝ) * Flanks.flankOpening 8 11 5 = (11 : ℝ)/88 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 11 5 = (28 : ℝ)/88 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
      · rw [h, show (21 : ℝ) * Flanks.flankOpening 8 11 5 = (69 : ℝ)/88 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
      · rw [h, show (31 : ℝ) * Flanks.flankOpening 8 11 5 = (39 : ℝ)/88 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (40 : ℝ) * Flanks.flankOpening 8 11 5 = (56 : ℝ)/88 + ((18 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 18 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 11 6 = (49 : ℝ)/88 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (11 : ℝ) * Flanks.flankOpening 8 11 6 = (11 : ℝ)/88 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 11 6 = (12 : ℝ)/88 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
      · rw [h, show (21 : ℝ) * Flanks.flankOpening 8 11 6 = (61 : ℝ)/88 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
      · rw [h, show (31 : ℝ) * Flanks.flankOpening 8 11 6 = (23 : ℝ)/88 + ((17 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 17 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (40 : ℝ) * Flanks.flankOpening 8 11 6 = (24 : ℝ)/88 + ((22 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 22 (by norm_num) (by norm_num)
    · rcases hd with h | h | h | h | h | h | h
      · rw [h, show (1 : ℝ) * Flanks.flankOpening 8 11 9 = (73 : ℝ)/88 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
      · rw [h, show (11 : ℝ) * Flanks.flankOpening 8 11 9 = (11 : ℝ)/88 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
      · rw [h, show (20 : ℝ) * Flanks.flankOpening 8 11 9 = (52 : ℝ)/88 + ((16 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 16 (by norm_num) (by norm_num)
      · rw [h, show (21 : ℝ) * Flanks.flankOpening 8 11 9 = (37 : ℝ)/88 + ((17 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 17 (by norm_num) (by norm_num)
      · rw [h, show (31 : ℝ) * Flanks.flankOpening 8 11 9 = (63 : ℝ)/88 + ((25 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 25 (by norm_num) (by norm_num)
      · exact absurd h hdx
      · rw [h, show (40 : ℝ) * Flanks.flankOpening 8 11 9 = (16 : ℝ)/88 + ((33 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
        exact Flanks.circDist_ge_of_band (n := 8) 33 (by norm_num) (by norm_num)
  · intro hlat
    rw [hq] at hlat
    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hlat] at hh; linarith
    have hm1 : 1 ≤ ⌊x⌋ := by
      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh
      omega
    have hm2 : ⌊x⌋ ≤ 39 := by
      have hh : ((⌊x⌋ : ℤ) : ℝ) < 40 := by rw [← hxi]; exact hxM
      have hh' : (⌊x⌋ : ℤ) < 40 := by exact_mod_cast hh
      omega
    rw [hxi]
    interval_cases h : ⌊x⌋
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((1 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (41 : ℝ)/88 + ((0 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 0 (by norm_num) (by norm_num)
    · refine ⟨9, by decide, 0, ?_⟩
      rw [show (9 : ℕ) + 0 * 11 = 9 from rfl,
        show (((2 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 9 = (58 : ℝ)/88 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((3 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (35 : ℝ)/88 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((4 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (76 : ℝ)/88 + ((1 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 1 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((5 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (29 : ℝ)/88 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((6 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (70 : ℝ)/88 + ((2 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 2 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((7 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (23 : ℝ)/88 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((8 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (64 : ℝ)/88 + ((3 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 3 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((9 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (17 : ℝ)/88 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((10 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (58 : ℝ)/88 + ((4 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 4 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((11 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (11 : ℝ)/88 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((12 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (52 : ℝ)/88 + ((5 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 5 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 11 = 6 from rfl,
        show (((13 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 6 = (21 : ℝ)/88 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((14 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (46 : ℝ)/88 + ((6 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 6 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 11 = 6 from rfl,
        show (((15 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 6 = (31 : ℝ)/88 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((16 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (40 : ℝ)/88 + ((7 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 7 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 11 = 6 from rfl,
        show (((17 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 6 = (41 : ℝ)/88 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((18 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (34 : ℝ)/88 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((19 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (75 : ℝ)/88 + ((8 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 8 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((20 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (28 : ℝ)/88 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((21 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (69 : ℝ)/88 + ((9 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 9 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((22 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (22 : ℝ)/88 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((23 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (63 : ℝ)/88 + ((10 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 10 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((24 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (16 : ℝ)/88 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((25 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (57 : ℝ)/88 + ((11 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 11 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 11 = 6 from rfl,
        show (((26 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 6 = (42 : ℝ)/88 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((27 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (51 : ℝ)/88 + ((12 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 12 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 11 = 6 from rfl,
        show (((28 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 6 = (52 : ℝ)/88 + ((15 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 15 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((29 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (45 : ℝ)/88 + ((13 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 13 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 11 = 6 from rfl,
        show (((30 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 6 = (62 : ℝ)/88 + ((16 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 16 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((31 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (39 : ℝ)/88 + ((14 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 14 (by norm_num) (by norm_num)
    · refine ⟨6, by decide, 0, ?_⟩
      rw [show (6 : ℕ) + 0 * 11 = 6 from rfl,
        show (((32 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 6 = (72 : ℝ)/88 + ((17 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 17 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((33 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (33 : ℝ)/88 + ((15 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 15 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((34 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (74 : ℝ)/88 + ((15 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 15 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((35 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (27 : ℝ)/88 + ((16 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 16 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((36 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (68 : ℝ)/88 + ((16 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 16 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((37 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (21 : ℝ)/88 + ((17 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 17 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((38 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (62 : ℝ)/88 + ((17 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 17 (by norm_num) (by norm_num)
    · refine ⟨5, by decide, 0, ?_⟩
      rw [show (5 : ℕ) + 0 * 11 = 5 from rfl,
        show (((39 : ℤ)) : ℝ) * Flanks.flankOpening 8 11 5 = (15 : ℝ)/88 + ((18 : ℤ) : ℝ) by
          unfold Flanks.flankOpening; push_cast; ring]
      exact Flanks.circDist_ge_of_band (n := 8) 18 (by norm_num) (by norm_num)

end CensusBatch
