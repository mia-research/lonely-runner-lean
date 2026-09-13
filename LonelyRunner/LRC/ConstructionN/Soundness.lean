import LonelyRunner.LRC.ConstructionN.Window

/-!
# Theorem 7.1 — soundness, as one declaration

**RING-FENCE.** General-`n` line (`LRC/ConstructionN/`). Not the artefact of the `n = 8`
paper, which cites the frozen `LRC/Construction8/`.

`docs/n8/MANUSCRIPT_v4.md` §7.2 states soundness as Theorem 7.1 and its §8 table marks it
`partial`, because it had been assembled from the formalised parts rather than stated once.
This module states it once.

## What the statement says

If the procedure returns `u` — meaning `u` lies in the window, and every reading other than
the nearest runner's is clear at `u` — then the subject is lonely at `t = u / dmin > 0`.

Two things worth recording about it.

**Minimality of `dmin` is not needed.** The hypothesis is only that `dmin` is the distance
to *some* runner `near`. If `dmin` were not the least such distance, the runners closer in
would have readings below `1` and are covered by `hclear` anyway. Minimality is what makes
the window the right place to search — a completeness property — not what makes a returned
`u` correct.

**The subject's index need not be in range.** `hi` is carried because the statement is about
runner `i`, but the proof does not use it.

Part 7 — that the procedure always returns — is **not** stated here and is not approached.
Soundness says a returned `u` is correct; it says nothing about whether one exists.
-/

namespace ConstructionN

/-- **Theorem 7.1 — soundness.** If the procedure returns `u`, the subject is lonely at
`t = u / dmin`, and that time is positive. -/
theorem procedure_sound {n : ℕ} (hn : 0 < n) (v : ℕ → ℝ) (i : ℕ) (hi : i < n)
    (dmin : ℝ) (hdmin : 0 < dmin)
    (u : ℝ) (h0 : 0 ≤ u) (h1 : u < 1)
    (hwin : (n : ℝ)⁻¹ ≤ u ∧ u ≤ 1 - (n : ℝ)⁻¹)
    (near : ℕ) (hnn : near < n) (hnear : |v near - v i| = dmin)
    (hclear : ∀ j, j < n → j ≠ i → j ≠ near →
      (n : ℝ)⁻¹ ≤ circDist (((v j - v i) / dmin) * u)) :
    0 < u / dmin ∧
      ∀ j, j < n → j ≠ i → (n : ℝ)⁻¹ ≤ circDist ((v j - v i) * (u / dmin)) := by
  have hnpos : (0 : ℝ) < (n : ℝ)⁻¹ := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  refine ⟨div_pos (by linarith [hwin.1]) hdmin, ?_⟩
  intro j hjn hji
  have hrw : (v j - v i) * (u / dmin) = ((v j - v i) / dmin) * u := by field_simp
  rw [hrw]
  by_cases hjn' : j = near
  · subst hjn'
    -- the nearest runner's reading is ±1, and the window is exactly its clearance
    have hpm : ((v j - v i) / dmin) = 1 ∨ ((v j - v i) / dmin) = -1 := by
      rcases (abs_eq (le_of_lt hdmin)).mp hnear with h | h
      · left; rw [h]; field_simp
      · right; rw [h]; field_simp
    rcases hpm with h | h
    · rw [h, one_mul]; exact (window_iff h0 h1).mpr hwin
    · rw [h, show (-1 : ℝ) * u = -u by ring, circDist.symm_neg]
      exact (window_iff h0 h1).mpr hwin
  · exact hclear j hjn hji hjn'

/-- **Non-vacuity.**  Two runners at speeds `0` and `1`, `dmin = 1`, `u = 1/2`: every
hypothesis of `procedure_sound` holds, so it is not proved from hypotheses that cannot. -/
theorem procedure_sound_hypotheses_satisfiable :
    ∃ (v : ℕ → ℝ) (i near : ℕ) (dmin u : ℝ),
      i < 2 ∧ near < 2 ∧ 0 < dmin ∧ 0 ≤ u ∧ u < 1 ∧
      (((2 : ℕ) : ℝ)⁻¹ ≤ u ∧ u ≤ 1 - ((2 : ℕ) : ℝ)⁻¹) ∧ |v near - v i| = dmin ∧
      (∀ j, j < 2 → j ≠ i → j ≠ near →
        (((2 : ℕ) : ℝ)⁻¹ ≤ circDist (((v j - v i) / dmin) * u))) := by
  refine ⟨fun k => if k = 0 then 0 else 1, 0, 1, 1, 1/2, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  intro j hj hj0 hj1
  interval_cases j <;> simp_all

end ConstructionN
