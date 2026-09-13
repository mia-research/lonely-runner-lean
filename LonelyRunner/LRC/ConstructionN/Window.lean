import LonelyRunner.LRC.ConstructionN.Flank

/-!

**RING-FENCE.**  This tree is the general-`n` line and is **not** the artefact of
`docs/n8/MANUSCRIPT_v1.md`.  That paper cites `LonelyRunner/LRC/Construction8/`, which is
**frozen**: nothing here may change it, and `scripts/n8/gate.sh` gates it independently.
This file began as a copy of its `Construction8` counterpart with the namespace renamed;
divergence from that starting point is the point of the tree, and is recorded per file as
it happens.
# Parts 4 and 5 — one window, and the reading

`docs/n8/PROOF_CANDIDATE_v3.md` parts 4 and 5; `docs/n8/PROOF_PLAN_v1.md` §2 targets 4
and 5.

Part 4: in the lap coordinate `u = m t`, the nearest runner — whose reading is `s = 1` —
is clear of the threshold exactly on `[1/n, (n-1)/n]`.  That is the one window.

Part 5: at `u`, a runner at relative rate `s` has completed `⌊s u⌋ ` laps and sits at
phase `fract (s u)`, and is clear of the subject exactly when that phase is in the band.
Positions and lap counts are read off, not searched for.

Both are stated without a positivity hypothesis on `n`, because neither proof uses one.
Carrying `0 < n` here would suggest the band needs it, and it does not.

Nothing here states or attempts part 7.
-/

namespace ConstructionN

/-- **Part 4 — one window.**  Inside the first lap the nearest runner is clear of the
threshold exactly on `[1/n, (n-1)/n]`. -/
theorem window_iff {n : ℕ} {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) :
    (n : ℝ)⁻¹ ≤ circDist u ↔ ((n : ℝ)⁻¹ ≤ u ∧ u ≤ 1 - (n : ℝ)⁻¹) := by
  have habs : |u| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hau : |u| = u := abs_of_nonneg h0
  rw [circDist_of_abs_lt_one habs, hau, le_min_iff]
  constructor
  · rintro ⟨ha, hb⟩; exact ⟨ha, by linarith⟩
  · rintro ⟨ha, hb⟩; exact ⟨ha, by linarith⟩

/-- **Part 5 — the reading.**  A runner at relative rate `s` sits at phase `fract (s u)`
and is clear of the subject exactly when that phase lies in the band. -/
theorem reading_clear_iff {n : ℕ} (s u : ℝ) :
    (n : ℝ)⁻¹ ≤ circDist (s * u) ↔
      ((n : ℝ)⁻¹ ≤ Int.fract (s * u) ∧ Int.fract (s * u) ≤ 1 - (n : ℝ)⁻¹) := by
  unfold circDist
  rw [le_min_iff]
  constructor
  · rintro ⟨ha, hb⟩; exact ⟨ha, by linarith⟩
  · rintro ⟨ha, hb⟩; exact ⟨ha, by linarith⟩

/-- **Part 5 — laps and phase.**  At `u` the runner has completed `⌊s u⌋` laps relative to
the subject and sits at phase `fract (s u)`. -/
theorem lap_and_phase (s u : ℝ) : s * u = (⌊s * u⌋ : ℝ) + Int.fract (s * u) :=
  (Int.floor_add_fract (s * u)).symm

end ConstructionN
