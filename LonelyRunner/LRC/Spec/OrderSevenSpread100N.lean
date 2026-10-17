import LonelyRunner.LRC.Spec.OrderSevenFirstStretchN
import LonelyRunner.LRC.Spec.OrderSevenBox6Tree100N

/-!
# Order seven for bounded spread: `v6 ≤ 100 v1`; reduction to `FS100`

`lonely7_spread100`: the fold (`v6 ≥ 6 v5`) and the kernel-checked six-runner tree on `v1 ≥ v6/100`
(`O7Box6T100`, 944,513 leaves) give order seven whenever `v6 ≤ 100 v1`.

`FS100` (**owed, not proved**): first-stretch localisation for spread `> 100`, as `FS50` with `100` in place of `50`.
`lonely7_of_FS100`: `FS100` gives order seven for every six-set of positive whole numbers.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.O7Spread

theorem lonely7_spread100 {v1 v2 v3 v4 v5 v6 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3) (h34 : v3 < v4)
    (h45 : v4 < v5) (h56 : v5 < v6) (hs : v6 ≤ 100 * v1) :
    ∃ t : ℝ, ∀ d ∈ ({v1, v2, v3, v4, v5, v6} : Finset ℕ), (1 : ℝ) / 7 ≤ circDist ((d : ℝ) * t) := by
  rcases le_or_gt (6 * v5) v6 with h6 | h6
  · exact LRC.O7Fold.lonely7_of_fast6 h0 h12 h23 h34 h45 h6
  · refine LRC.O7Box6T100.lonely h0 h12 h23 h34 h45 h56 ?_ ?_
    · have : (v6 : ℝ) ≤ 100 * v1 := by exact_mod_cast hs
      push_cast; linarith
    · have : (v6 : ℝ) < 6 * v5 := by exact_mod_cast h6
      push_cast; linarith

end LRC.O7Spread

namespace LRC.O7FirstStretch

/-- First-stretch localisation for spread `> 100` (owed). -/
def FS100 : Prop :=
  ∀ v1 v2 v3 v4 v5 v6 : ℕ, 0 < v1 → v1 < v2 → v2 < v3 → v3 < v4 → v4 < v5 → v5 < v6 → 100 * v1 < v6 →
    ∃ t : ℝ, 1 / (7 * (v1 : ℝ)) ≤ t ∧ t ≤ 6 / (7 * (v1 : ℝ)) ∧
      ∀ d ∈ ({v2, v3, v4, v5, v6} : Finset ℕ), (1 : ℝ) / 7 ≤ circDist ((d : ℝ) * t)

theorem FS100_of_FS50 (h : FS50) : FS100 := fun v1 v2 v3 v4 v5 v6 h0 h12 h23 h34 h45 h56 hs =>
  h v1 v2 v3 v4 v5 v6 h0 h12 h23 h34 h45 h56 (by omega)

/-- **Order seven from `FS100`.** -/
theorem lonely7_of_FS100 (hFS : FS100) {v1 v2 v3 v4 v5 v6 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3)
    (h34 : v3 < v4) (h45 : v4 < v5) (h56 : v5 < v6) :
    ∃ t : ℝ, ∀ d ∈ ({v1, v2, v3, v4, v5, v6} : Finset ℕ), (1 : ℝ) / 7 ≤ circDist ((d : ℝ) * t) := by
  rcases le_or_gt v6 (100 * v1) with hs | hs
  · exact LRC.O7Spread.lonely7_spread100 h0 h12 h23 h34 h45 h56 hs
  · obtain ⟨t, h1, h2, ht⟩ := hFS v1 v2 v3 v4 v5 v6 h0 h12 h23 h34 h45 h56 hs
    refine ⟨t, fun d hd => ?_⟩
    rcases Finset.mem_insert.mp hd with rfl | hd'
    · exact first_stretch_band h0 h1 h2
    · exact ht d hd'

end LRC.O7FirstStretch
