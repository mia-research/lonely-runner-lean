import LonelyRunner.LRC.Cascade.Flanks

/-!
# The eighth-family: every member is lonely, at an opening of the `7/8` flank

Part of the cascade artefact (`LRC/Cascade/`).  Threshold `1/8`.

Scale-normalised to `d_max = 8`, the family that shadows the largest flank is the one-parameter set

    Δ(x) = {1, 3, 4, 5, 7, x, 8},   0 < x < 8.

At the `k`-th opening of the flank at difference `7`, `t = (k + 1/8)/7`, a difference `d` sits at
`d·(k + 1/8)/7` laps.  The six fixed differences depend only on `k mod 7`, and they leave exactly the
residues `k ≡ 1` and `k ≡ 3` uncovered (`fixed_clear_one`, `fixed_clear_three`).  The free parameter is
then handled in two cases:

* `x` an integer in `{1,…,7}` — a finite check; `k = 1` serves every value except `x = 6`, which is
  blocked there (`54/56` exceeds the band) and served by `k = 3`;
* `x` not an integer — the phases along `k = 1 + 7j` are `9x/56 + j·x`, which differ from
  `9x/56 + j·Int.fract x` by an integer, so `Flanks.exists_clear_step` supplies a clear `j` outright.

The second case covers rational and irrational `x` alike, from a lemma already in the artefact: no
density, equidistribution or approximation-theoretic input is used anywhere in this file.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace EighthFamily

open ConstructionN MomentIterationN

instance fact_two_le_eight : Fact (2 ≤ 8) := ⟨by norm_num⟩

/-- The clear band at threshold `1/8`, in fifty-sixths: a phase `p/56` (plus any whole number of laps)
is at least `1/8` from every lap line exactly when `7 ≤ p ≤ 49`. -/
theorem clear_of_band (p : ℕ) (c : ℤ) (h1 : 7 ≤ p) (h2 : p ≤ 49) :
    ((8 : ℕ) : ℝ)⁻¹ ≤ circDist ((p : ℝ) / 56 + (c : ℝ)) := by
  rw [circDist_add_int]
  have hp1 : (7 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h1
  have hp2 : (p : ℝ) ≤ 49 := by exact_mod_cast h2
  have h0 : (0 : ℝ) ≤ (p : ℝ) / 56 := by positivity
  have hlt : (p : ℝ) / 56 < 1 := by linarith
  unfold circDist
  rw [Int.fract_eq_self.mpr ⟨h0, hlt⟩, le_min_iff]
  constructor <;> push_cast <;> linarith

/-- The six fixed differences are clear at every opening `k = 1 + 7j` of the flank at difference `7`. -/
theorem fixed_clear_one (j : ℕ) (d : ℝ) (hd : d = 1 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 7 ∨ d = 8) :
    ((8 : ℕ) : ℝ)⁻¹ ≤ circDist (d * ((1 + 7 * (j : ℝ) + 1 / 8) / 7)) := by
  rcases hd with h | h | h | h | h | h <;> rw [h]
  · have e : (1 : ℝ) * ((1 + 7 * (j : ℝ) + 1 / 8) / 7) = (9 : ℝ) / 56 + ((j : ℤ) : ℝ) := by
      push_cast; ring
    rw [e]; exact clear_of_band 9 (j : ℤ) (by norm_num) (by norm_num)
  · have e : (3 : ℝ) * ((1 + 7 * (j : ℝ) + 1 / 8) / 7) = (27 : ℝ) / 56 + ((3 * j : ℤ) : ℝ) := by
      push_cast; ring
    rw [e]; exact clear_of_band 27 (3 * j : ℤ) (by norm_num) (by norm_num)
  · have e : (4 : ℝ) * ((1 + 7 * (j : ℝ) + 1 / 8) / 7) = (36 : ℝ) / 56 + ((4 * j : ℤ) : ℝ) := by
      push_cast; ring
    rw [e]; exact clear_of_band 36 (4 * j : ℤ) (by norm_num) (by norm_num)
  · have e : (5 : ℝ) * ((1 + 7 * (j : ℝ) + 1 / 8) / 7) = (45 : ℝ) / 56 + ((5 * j : ℤ) : ℝ) := by
      push_cast; ring
    rw [e]; exact clear_of_band 45 (5 * j : ℤ) (by norm_num) (by norm_num)
  · have e : (7 : ℝ) * ((1 + 7 * (j : ℝ) + 1 / 8) / 7) = (7 : ℝ) / 56 + ((1 + 7 * j : ℤ) : ℝ) := by
      push_cast; ring
    rw [e]; exact clear_of_band 7 (1 + 7 * j : ℤ) (by norm_num) (by norm_num)
  · have e : (8 : ℝ) * ((1 + 7 * (j : ℝ) + 1 / 8) / 7) = (16 : ℝ) / 56 + ((1 + 8 * j : ℤ) : ℝ) := by
      push_cast; ring
    rw [e]; exact clear_of_band 16 (1 + 8 * j : ℤ) (by norm_num) (by norm_num)

/-- The six fixed differences are clear at the flank's opening `k = 3`. -/
theorem fixed_clear_three (d : ℝ) (hd : d = 1 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 7 ∨ d = 8) :
    ((8 : ℕ) : ℝ)⁻¹ ≤ circDist (d * (((3 : ℝ) + 1 / 8) / 7)) := by
  rcases hd with h | h | h | h | h | h <;> rw [h]
  · have e : (1 : ℝ) * (((3 : ℝ) + 1 / 8) / 7) = (25 : ℝ) / 56 + ((0 : ℤ) : ℝ) := by push_cast; ring
    rw [e]; exact clear_of_band 25 0 (by norm_num) (by norm_num)
  · have e : (3 : ℝ) * (((3 : ℝ) + 1 / 8) / 7) = (19 : ℝ) / 56 + ((1 : ℤ) : ℝ) := by push_cast; ring
    rw [e]; exact clear_of_band 19 1 (by norm_num) (by norm_num)
  · have e : (4 : ℝ) * (((3 : ℝ) + 1 / 8) / 7) = (44 : ℝ) / 56 + ((1 : ℤ) : ℝ) := by push_cast; ring
    rw [e]; exact clear_of_band 44 1 (by norm_num) (by norm_num)
  · have e : (5 : ℝ) * (((3 : ℝ) + 1 / 8) / 7) = (13 : ℝ) / 56 + ((2 : ℤ) : ℝ) := by push_cast; ring
    rw [e]; exact clear_of_band 13 2 (by norm_num) (by norm_num)
  · have e : (7 : ℝ) * (((3 : ℝ) + 1 / 8) / 7) = (7 : ℝ) / 56 + ((3 : ℤ) : ℝ) := by push_cast; ring
    rw [e]; exact clear_of_band 7 3 (by norm_num) (by norm_num)
  · have e : (8 : ℝ) * (((3 : ℝ) + 1 / 8) / 7) = (32 : ℝ) / 56 + ((3 : ℤ) : ℝ) := by push_cast; ring
    rw [e]; exact clear_of_band 32 3 (by norm_num) (by norm_num)

/-- A whole-number parameter at `k = 1`: the phase is `9m/56`, inside the band for every
`m ∈ {1,…,7}` except `m = 6`, whose `54/56` falls outside it. -/
theorem int_clear_one (m : ℤ) (hm1 : 1 ≤ m) (hm7 : m ≤ 7) (hm6 : m ≠ 6) :
    ((8 : ℕ) : ℝ)⁻¹ ≤ circDist (((m : ℤ) : ℝ) * ((1 + 7 * ((0 : ℕ) : ℝ) + 1 / 8) / 7)) := by
  interval_cases m
  · have e : ((1 : ℤ) : ℝ) * ((1 + 7 * ((0 : ℕ) : ℝ) + 1 / 8) / 7) = (9 : ℝ) / 56 + ((0 : ℤ) : ℝ) := by
      push_cast; ring
    rw [e]; exact clear_of_band 9 0 (by norm_num) (by norm_num)
  · have e : ((2 : ℤ) : ℝ) * ((1 + 7 * ((0 : ℕ) : ℝ) + 1 / 8) / 7) = (18 : ℝ) / 56 + ((0 : ℤ) : ℝ) := by
      push_cast; ring
    rw [e]; exact clear_of_band 18 0 (by norm_num) (by norm_num)
  · have e : ((3 : ℤ) : ℝ) * ((1 + 7 * ((0 : ℕ) : ℝ) + 1 / 8) / 7) = (27 : ℝ) / 56 + ((0 : ℤ) : ℝ) := by
      push_cast; ring
    rw [e]; exact clear_of_band 27 0 (by norm_num) (by norm_num)
  · have e : ((4 : ℤ) : ℝ) * ((1 + 7 * ((0 : ℕ) : ℝ) + 1 / 8) / 7) = (36 : ℝ) / 56 + ((0 : ℤ) : ℝ) := by
      push_cast; ring
    rw [e]; exact clear_of_band 36 0 (by norm_num) (by norm_num)
  · have e : ((5 : ℤ) : ℝ) * ((1 + 7 * ((0 : ℕ) : ℝ) + 1 / 8) / 7) = (45 : ℝ) / 56 + ((0 : ℤ) : ℝ) := by
      push_cast; ring
    rw [e]; exact clear_of_band 45 0 (by norm_num) (by norm_num)
  · exact absurd rfl hm6
  · have e : ((7 : ℤ) : ℝ) * ((1 + 7 * ((0 : ℕ) : ℝ) + 1 / 8) / 7) = (7 : ℝ) / 56 + ((1 : ℤ) : ℝ) := by
      push_cast; ring
    rw [e]; exact clear_of_band 7 1 (by norm_num) (by norm_num)

/-- **The free parameter, when it is not a whole number.**  Along the openings `k = 1 + 7j` the phase
of `x` is `9x/56 + j·x`, an integer away from `j·(Int.fract x) + 9x/56`; `exists_clear_step` then gives
a `j` at which `x` is clear — rational and irrational `x` alike, with no density input. -/
theorem free_clear_of_not_int {x : ℝ} (hfx : Int.fract x ≠ 0) :
    ∃ j : ℕ, ((8 : ℕ) : ℝ)⁻¹ ≤ circDist (x * ((1 + 7 * (j : ℝ) + 1 / 8) / 7)) := by
  have hf0 : 0 < Int.fract x := lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm hfx)
  have hf1 : Int.fract x < 1 := Int.fract_lt_one x
  obtain ⟨j, hj⟩ := Flanks.exists_clear_step (n := 8) (by norm_num) hf0 hf1 (c := 9 * x / 56)
  refine ⟨j, ?_⟩
  have hfr : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
  have e : x * ((1 + 7 * (j : ℝ) + 1 / 8) / 7)
      = ((j : ℝ) * Int.fract x + 9 * x / 56) + ((j * ⌊x⌋ : ℤ) : ℝ) := by
    rw [hfr]; push_cast; ring
  rw [e, circDist_add_int]
  exact hj

/-- **Every member of the eighth-family is lonely.**  For every `x` with `0 < x < 8` the difference set
`{1, 3, 4, 5, 7, x, 8}` has a lonely instant, at an opening of the flank at difference `7`: `k = 1 + 7j`
for a `j` the clear-step lemma supplies when `x` is not a whole number, `k = 1` for whole `x ≠ 6`, and
`k = 3` for `x = 6`. -/
theorem eighth_family_lonely (x : ℝ) (hx0 : 0 < x) (hx8 : x < 8) :
    ∃ t : ℝ, 0 < t ∧ Lonely 8 ({1, 3, 4, 5, 7, x, 8} : Finset ℝ) t := by
  by_cases hfx : Int.fract x = 0
  · have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by
      have h : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [hfx] at h; linarith
    by_cases h6 : x = 6
    · refine ⟨((3 : ℝ) + 1 / 8) / 7, by norm_num, ?_⟩
      intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with h | h | h | h | h | h | h <;> rw [h]
      · exact fixed_clear_three 1 (by tauto)
      · exact fixed_clear_three 3 (by tauto)
      · exact fixed_clear_three 4 (by tauto)
      · exact fixed_clear_three 5 (by tauto)
      · exact fixed_clear_three 7 (by tauto)
      · rw [h6]
        have e : (6 : ℝ) * (((3 : ℝ) + 1 / 8) / 7) = (38 : ℝ) / 56 + ((2 : ℤ) : ℝ) := by
          push_cast; ring
        rw [e]; exact clear_of_band 38 2 (by norm_num) (by norm_num)
      · exact fixed_clear_three 8 (by tauto)
    · have hm1 : 1 ≤ ⌊x⌋ := by
        have h : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0
        have h' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast h
        omega
      have hm7 : ⌊x⌋ ≤ 7 := by
        have h : ((⌊x⌋ : ℤ) : ℝ) < 8 := by rw [← hxi]; exact hx8
        have h' : (⌊x⌋ : ℤ) < 8 := by exact_mod_cast h
        omega
      have hm6 : ⌊x⌋ ≠ 6 := by
        intro hc; apply h6; rw [hxi, hc]; norm_num
      refine ⟨(1 + 7 * ((0 : ℕ) : ℝ) + 1 / 8) / 7, by norm_num, ?_⟩
      intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with h | h | h | h | h | h | h <;> rw [h]
      · exact fixed_clear_one 0 1 (by tauto)
      · exact fixed_clear_one 0 3 (by tauto)
      · exact fixed_clear_one 0 4 (by tauto)
      · exact fixed_clear_one 0 5 (by tauto)
      · exact fixed_clear_one 0 7 (by tauto)
      · rw [hxi]; exact int_clear_one ⌊x⌋ hm1 hm7 hm6
      · exact fixed_clear_one 0 8 (by tauto)
  · obtain ⟨j, hj⟩ := free_clear_of_not_int hfx
    refine ⟨(1 + 7 * (j : ℝ) + 1 / 8) / 7, by positivity, ?_⟩
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with h | h | h | h | h | h | h <;> rw [h]
    · exact fixed_clear_one j 1 (by tauto)
    · exact fixed_clear_one j 3 (by tauto)
    · exact fixed_clear_one j 4 (by tauto)
    · exact fixed_clear_one j 5 (by tauto)
    · exact fixed_clear_one j 7 (by tauto)
    · exact hj
    · exact fixed_clear_one j 8 (by tauto)

/-- **The family at its own scale.**  Loneliness is read from the products `d·t`, so the normalised
statement transports: a runner whose differences are `{E/8, 3E/8, E/2, 5E/8, 7E/8, x, E}` for any
`E > 0` and `0 < x < E` is lonely, at `8/E` times the normalised instant. -/
theorem eighth_family_lonely_scaled (E x : ℝ) (hE : 0 < E) (hx0 : 0 < x) (hx8 : x < E) :
    ∃ t : ℝ, 0 < t ∧
      Lonely 8 ({E / 8, 3 * E / 8, 4 * E / 8, 5 * E / 8, 7 * E / 8, x, E} : Finset ℝ) t := by
  have hE' : E ≠ 0 := ne_of_gt hE
  have hu0 : 0 < 8 * x / E := by positivity
  have hu8 : 8 * x / E < 8 := by
    rw [div_lt_iff₀ hE]; nlinarith
  obtain ⟨t, ht0, ht⟩ := eighth_family_lonely (8 * x / E) hu0 hu8
  refine ⟨8 * t / E, by positivity, ?_⟩
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  have h1 := ht 1 (by simp)
  have h3 := ht 3 (by simp)
  have h4 := ht 4 (by simp)
  have h5 := ht 5 (by simp)
  have h7 := ht 7 (by simp)
  have h8 := ht 8 (by simp)
  have hx := ht (8 * x / E) (by simp)
  rcases hd with h | h | h | h | h | h | h <;> rw [h]
  · rw [show E / 8 * (8 * t / E) = 1 * t by field_simp]; exact h1
  · rw [show 3 * E / 8 * (8 * t / E) = 3 * t by field_simp]; exact h3
  · rw [show 4 * E / 8 * (8 * t / E) = 4 * t by field_simp]; exact h4
  · rw [show 5 * E / 8 * (8 * t / E) = 5 * t by field_simp]; exact h5
  · rw [show 7 * E / 8 * (8 * t / E) = 7 * t by field_simp]; exact h7
  · rw [show x * (8 * t / E) = 8 * x / E * t by field_simp]; exact hx
  · rw [show E * (8 * t / E) = 8 * t by field_simp]; exact h8

end EighthFamily
