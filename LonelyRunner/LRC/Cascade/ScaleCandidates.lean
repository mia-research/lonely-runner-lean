import LonelyRunner.LRC.Cascade.Flanks
import LonelyRunner.LRC.ConstructionN.Window

/-!
# The candidate scales: the obligation with no time and no iteration

Part of the cascade artefact (`LRC/Cascade/`).  Threshold `1/n`.

A flank opening is the **first spine instant of a scale read off the arrangement**:

    flankOpening n e k = (k + 1/n)/e = 1 / (n · (e/(n·k+1)))

so the opening of disparity `e` at index `k` *is* the instant `1/(n·D)` for the scale
`D = e/(n·k+1)`.  Nothing is chosen: `e` is one of the subject's own disparities and `k` an index.

* `candidateScale n e k = e/(n·k+1)` — the scale of that opening.
* `flankOpening_eq_spine` — the two descriptions are the same instant.
* `candidate_clear_own` — at its own candidate scale a disparity reads **exactly** `n·k+1`, one
  slot away from the multiple `n·k`, hence clear.  Every candidate is clear by construction for
  the disparity that names it; the content is the *other* disparities.
* `lonely_iff_exists_candidate_scale` — Existence, restated: the subject is lonely at some positive
  instant **iff some candidate scale is clear for every disparity**.  No quantifier over time and
  no iteration; the cascade's fixed point is one of these scales.
* `inWay_at_scale_interval` — a disparity `d` is in the way at scale `D` exactly when `D` lies
  above `d`, or inside one of the open intervals `(d/(n·M+1), d/(n·M−1))`, `M ≥ 1`.  So the bad
  scales are an explicit union of intervals in ONE dimension and the candidates are their left
  endpoints.

Nothing here proves Existence.  It restates the obligation in the framework's own objects.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Flanks

open ConstructionN MomentIterationN

variable {n : ℕ} [Fact (2 ≤ n)]

/-- **The candidate scale** of disparity `e` at opening index `k`. -/
noncomputable def candidateScale (n : ℕ) (e : ℝ) (k : ℕ) : ℝ := e / ((n : ℝ) * k + 1)

theorem nk_add_one_pos (k : ℕ) : (0 : ℝ) < (n : ℝ) * k + 1 := by
  have : (0 : ℝ) ≤ (n : ℝ) * k := by positivity
  linarith

theorem candidateScale_pos {e : ℝ} (he : 0 < e) (k : ℕ) : 0 < candidateScale n e k := by
  unfold candidateScale
  exact div_pos he (nk_add_one_pos (n := n) k)

/-- **The opening is the first spine instant of its candidate scale.** -/
theorem flankOpening_eq_spine {e : ℝ} (he : 0 < e) (k : ℕ) :
    flankOpening n e k = 1 / ((n : ℝ) * candidateScale n e k) := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hd := nk_add_one_pos (n := n) k
  unfold flankOpening candidateScale
  field_simp

/-- **A disparity reads exactly `n·k+1` at its own candidate scale.** -/
theorem own_reading {e : ℝ} (he : 0 < e) (k : ℕ) :
    e / candidateScale n e k = (n : ℝ) * k + 1 := by
  have hd := nk_add_one_pos (n := n) k
  unfold candidateScale
  field_simp

/-- **Every candidate scale is clear for the disparity that names it.**  The reading is exactly
`n·k+1`, at distance exactly `1` from the multiple `n·k` — the threshold case, which is clear. -/
theorem candidate_clear_own {e : ℝ} (he : 0 < e) (k : ℕ) :
    (n : ℝ)⁻¹ ≤ circDist (e * flankOpening n e k) := by
  have hn0 : (0 : ℝ) < n := n_pos
  have h1 : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have h0 : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
  have hval : e * flankOpening n e k = (n : ℝ)⁻¹ + ((k : ℤ) : ℝ) := by
    unfold flankOpening; push_cast; field_simp; ring
  rw [hval, circDist_add_int, window_iff (by linarith) (by linarith)]
  exact ⟨le_refl _, by linarith⟩

/-- **Existence, with no time and no iteration.**  The subject is lonely at some positive instant
iff some candidate scale is clear for every disparity.  The scales are read off the arrangement:
a disparity divided by `n·k+1`. -/
theorem lonely_iff_exists_candidate_scale {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d)
    (hne : ds.Nonempty) :
    (∃ s, 0 < s ∧ Lonely n ds s) ↔
      ∃ e ∈ ds, ∃ k : ℕ, Lonely n ds (1 / ((n : ℝ) * candidateScale n e k)) := by
  rw [lonely_iff_exists_flank hpos hne]
  constructor
  · rintro ⟨e, he, k, hl⟩
    exact ⟨e, he, k, by rwa [← flankOpening_eq_spine (hpos e he) k]⟩
  · rintro ⟨e, he, k, hl⟩
    exact ⟨e, he, k, by rwa [flankOpening_eq_spine (hpos e he) k]⟩

/-- **The bad scales are an explicit union of open intervals, in one dimension.**  A disparity `d`
is in the way at scale `D` exactly when `D` exceeds `d`, or `D` lies inside
`(d/(n·M+1), d/(n·M−1))` for some `M ≥ 1`.  So the good scales are the GAPS of a union of intervals
on the half-line, and the candidate scales `d/(n·M+1)` are precisely their left endpoints. -/
theorem inWay_at_scale_interval {d D : ℝ} (hd : 0 < d) (hD : 0 < D) :
    inWay n d (1 / ((n : ℝ) * D)) ↔
      d < D ∨ ∃ M : ℕ, 1 ≤ M ∧ d / ((n : ℝ) * M + 1) < D ∧ D < d / ((n : ℝ) * M - 1) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Fact.out : 2 ≤ n)
  have hn0 : (0 : ℝ) < n := by linarith
  rw [inWay_at_scale_iff hD]
  constructor
  · rintro ⟨N, hN⟩
    rw [abs_lt] at hN
    by_cases hle : N ≤ 0
    · left
      have hNle : (N : ℝ) ≤ 0 := by exact_mod_cast hle
      have hnN : (n : ℝ) * N ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hn0) hNle
      exact (div_lt_one hD).mp (by linarith [hN.2])
    · right
      have hN1 : (1 : ℤ) ≤ N := by omega
      have hNge : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
      have hcast : ((N.toNat : ℕ) : ℝ) = (N : ℝ) := by
        have hz : ((N.toNat : ℕ) : ℤ) = N := Int.toNat_of_nonneg (by omega)
        exact_mod_cast hz
      have hp1 : (0 : ℝ) < (n : ℝ) * N + 1 := by nlinarith
      have hp2 : (0 : ℝ) < (n : ℝ) * N - 1 := by nlinarith
      refine ⟨N.toNat, by omega, ?_, ?_⟩
      · rw [hcast, div_lt_iff₀ hp1]
        have : d < ((n : ℝ) * N + 1) * D := (div_lt_iff₀ hD).mp (by linarith [hN.2])
        linarith [this]
      · rw [hcast, lt_div_iff₀ hp2]
        have : ((n : ℝ) * N - 1) * D < d := (lt_div_iff₀ hD).mp (by linarith [hN.1])
        linarith [this]
  · rintro (hlt | ⟨M, hM1, hlo, hhi⟩)
    · refine ⟨0, ?_⟩
      have hz : ((0 : ℤ) : ℝ) = 0 := by norm_num
      rw [hz, mul_zero, sub_zero, abs_lt]
      exact ⟨by linarith [div_pos hd hD], (div_lt_one hD).mpr hlt⟩
    · refine ⟨(M : ℤ), ?_⟩
      have hMge : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
      have hp1 : (0 : ℝ) < (n : ℝ) * M + 1 := by nlinarith
      have hp2 : (0 : ℝ) < (n : ℝ) * M - 1 := by nlinarith
      have hcast : (((M : ℤ)) : ℝ) = (M : ℝ) := by push_cast; ring
      rw [hcast, abs_lt]
      constructor
      · have h := (lt_div_iff₀ hp2).mp hhi
        have : (n : ℝ) * M - 1 < d / D := (lt_div_iff₀ hD).mpr (by linarith [h])
        linarith
      · have h := (div_lt_iff₀ hp1).mp hlo
        have : d / D < (n : ℝ) * M + 1 := (div_lt_iff₀ hD).mpr (by linarith [h])
        linarith

end Flanks
