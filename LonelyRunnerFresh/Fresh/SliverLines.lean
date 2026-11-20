import Mathlib.Tactic

/-!
# The sliver-closing lines (boundary components die over [25, ∞))

A reading ρ kills a K6 component `[a, b]` at lap j when its OPEN zone
`((8j-1)/ρ, (8j+1)/ρ)` CONTAINS `[a, b]` (the K6-window-inside-a-zone structure; the
entry side is strict — the search's own mode).  The feasible ρ-interval for lap j is
`[(8j-1)/a, (8j+1)/b)`.
* START (`a = 1`): laps j ≤ 3 end below `31·25/33 < 25`; laps j ≥ 4 need
  `b·(8j-1) < 8j+1`, i.e. `b < (8j+1)/(8j-1) ≤ 33/31` (the ratio decreases in j).  So
  `b ≥ 33/31` kills every lap: no ρ ≥ 25 contains `[1, b]` in any zone.
* END (`b = 7`): laps j ≤ 21 end below `169/7 < 25`; laps j ≥ 22 need
  `a > 7(8j-1)/(8j+1) ≥ 1225/177` (the ratio increases in j).  So `a ≤ 1225/177` kills
  every lap.
Pure `ℝ` arithmetic, all linear; no data.
-/

namespace Fresh.SliverLines

/-- **START line.**  No containment of `[1, b]` in any lap-j zone for `b ≥ 33/31`, `ρ ≥ 25`
(the upper containment side is strict — the zone's entry is open). -/
theorem sliverStart_dead (b r : ℝ) (hb : (33:ℝ) / 31 ≤ b) (hr : (25:ℝ) ≤ r) (j : ℕ) :
    ¬ (r < (8 * (j:ℝ) + 1) / b ∧ (8 * (j:ℝ) - 1) ≤ r) := by
  intro ⟨hup, hlow⟩
  have hb0 : (0:ℝ) < b := by linarith
  have hupp : r * b < 8 * (j:ℝ) + 1 := (lt_div_iff₀ hb0).mp hup
  have hchain : 33 * r ≤ 31 * (r * b) := by nlinarith
  -- 33·(8j-1) ≤ 33·r ≤ 31·r·b < 31·(8j+1)  ⟹  16j < 64
  have hjlt : (16:ℝ) * j < 64 := by
    have hboth : 33 * (8 * (j:ℝ) - 1) < 31 * (8 * (j:ℝ) + 1) := by linarith
    linarith
  have hj : j ≤ 3 := by
    have h : (j:ℝ) < 4 := by linarith
    have h3 : j < 4 := by exact_mod_cast h
    omega
  have h25 : (8:ℝ) * j + 1 ≤ 25 := by
    have h : 8 * j + 1 ≤ 25 := by omega
    exact_mod_cast h
  -- r·b < 8j+1 ≤ 25 and 33·r ≤ 31·r·b  ⟹  r < 775/33 < 25
  linarith

/-- **END line.**  No containment of `[a, 7]` in any lap-j zone for `a ≤ 1225/177`, `ρ ≥ 25`. -/
theorem sliverEnd_dead (a r : ℝ) (ha1 : (1:ℝ) ≤ a) (ha : a ≤ (1225:ℝ) / 177) (hr : (25:ℝ) ≤ r) (j : ℕ) :
    ¬ ((8 * (j:ℝ) - 1) / a ≤ r ∧ r < (8 * (j:ℝ) + 1) / 7) := by
  intro ⟨hlow, hup⟩
  have ha0 : (0:ℝ) < a := by linarith
  have hupp : r * 7 < 8 * (j:ℝ) + 1 := (lt_div_iff₀ (by norm_num : (0:ℝ) < 7)).mp hup
  have hlow' : 8 * (j:ℝ) - 1 ≤ r * a := (div_le_iff₀ ha0).mp hlow
  -- (8j-1)·1239 ≤ 7·177·r·a ≤ 1225·7·r < 1225·(8j+1)  ⟹  112j < 2464
  have hkey : (8 * (j:ℝ) - 1) * 1239 < (8 * (j:ℝ) + 1) * 1225 := by
    have h1 : (8 * (j:ℝ) - 1) * 177 * 7 ≤ r * a * 177 * 7 := by nlinarith
    have h2 : r * a * 177 * 7 ≤ r * 7 * 1225 := by nlinarith
    have h3 : r * 7 * 1225 < (8 * (j:ℝ) + 1) * 1225 := by nlinarith
    linarith
  have hj : j ≤ 21 := by
    have h : (j:ℝ) < 22 := by linarith
    have h21 : j < 22 := by exact_mod_cast h
    omega
  have h169 : (8:ℝ) * j + 1 ≤ 169 := by
    have h : 8 * j + 1 ≤ 169 := by omega
    exact_mod_cast h
  -- r·7 < 8j+1 ≤ 169  ⟹  r < 169/7 < 25
  linarith

end Fresh.SliverLines

#print axioms Fresh.SliverLines.sliverStart_dead
#print axioms Fresh.SliverLines.sliverEnd_dead
