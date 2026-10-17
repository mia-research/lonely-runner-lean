import LonelyRunner.LRC.Spec.OrderSevenSpread50N

/-!
# Order seven: reduction to first-stretch localisation for spread `> 50`

`FS50` (**owed, not proved**; experiments/n7_native log E12–E13): whole numbers `0 < v1 < … < v6` with `v6 > 50 v1`
have an instant in the first band stretch of the slowest runner, `t ∈ [1/(7 v1), 6/(7 v1)]`, at which `v2, …, v6` all
read inside `[1/7, 6/7]`.  Exhaustive exact search: every primitive six-set `≤ 60` with `v6 > 7 v1` has such an instant.

`lonely7_of_FS50`: `FS50` and the kernel-checked tree (`lonely7_spread50`, `v6 ≤ 50 v1`) give order seven for every
six-set of positive whole numbers.  This is a conditional theorem: `FS50` is a `Prop`, stated here, proved nowhere.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.O7FirstStretch

open LRC.MirrorCentre

/-- First-stretch localisation for spread `> 50` (owed). -/
def FS50 : Prop :=
  ∀ v1 v2 v3 v4 v5 v6 : ℕ, 0 < v1 → v1 < v2 → v2 < v3 → v3 < v4 → v4 < v5 → v5 < v6 → 50 * v1 < v6 →
    ∃ t : ℝ, 1 / (7 * (v1 : ℝ)) ≤ t ∧ t ≤ 6 / (7 * (v1 : ℝ)) ∧
      ∀ d ∈ ({v2, v3, v4, v5, v6} : Finset ℕ), (1 : ℝ) / 7 ≤ circDist ((d : ℝ) * t)

/-- The slowest runner is in band on its first stretch. -/
theorem first_stretch_band {v1 : ℕ} (h : 0 < v1) {t : ℝ} (h1 : 1 / (7 * (v1 : ℝ)) ≤ t)
    (h2 : t ≤ 6 / (7 * (v1 : ℝ))) : (1 : ℝ) / 7 ≤ circDist ((v1 : ℝ) * t) := by
  have hv : (0 : ℝ) < v1 := by exact_mod_cast h
  apply circDist_ge_of_window (m := 0) _ _ (by norm_num)
  · push_cast; rw [div_le_iff₀ (by positivity)] at h1; nlinarith
  · push_cast; rw [le_div_iff₀ (by positivity)] at h2; nlinarith

/-- **Order seven from `FS50`.** -/
theorem lonely7_of_FS50 (hFS : FS50) {v1 v2 v3 v4 v5 v6 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3)
    (h34 : v3 < v4) (h45 : v4 < v5) (h56 : v5 < v6) :
    ∃ t : ℝ, ∀ d ∈ ({v1, v2, v3, v4, v5, v6} : Finset ℕ), (1 : ℝ) / 7 ≤ circDist ((d : ℝ) * t) := by
  rcases le_or_gt v6 (50 * v1) with hs | hs
  · exact LRC.O7Spread.lonely7_spread50 h0 h12 h23 h34 h45 h56 hs
  · obtain ⟨t, h1, h2, ht⟩ := hFS v1 v2 v3 v4 v5 v6 h0 h12 h23 h34 h45 h56 hs
    refine ⟨t, fun d hd => ?_⟩
    rcases Finset.mem_insert.mp hd with rfl | hd'
    · exact first_stretch_band h0 h1 h2
    · exact ht d hd'

end LRC.O7FirstStretch
