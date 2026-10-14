import LonelyRunner.LRC.Construction8.Bounds

/-!
# The buffer-and-room move, over the reals

Experiment, outside both Lean trees.  Generalises `Construction8.blocked_lands_on_threshold` and
`unblocked_stays_clear` (integral readings, one blocked runner) to any real readings.

From a base instant `u₀`, each runner `s` sits at phase `φ = fract (s·u₀)`.  Moving forward by `ε`:

* a clear runner (`1/8 ≤ φ ≤ 7/8`) has **room** `(7/8 − φ)/s`;
* a runner blocked low (`φ < 1/8`) needs `(1/8 − φ)/s` and has room `(7/8 − φ)/s`;
* a runner blocked high (`φ > 7/8`) needs `(9/8 − φ)/s` and has room `(15/8 − φ)/s`.

`clear_after_move`: if a runner's requirement `≤ ε ≤` its room, it is clear at `u₀ + ε`.  So moving
by the largest requirement works whenever that fits inside the smallest room — computed, not searched.
-/

namespace BufferRoom

noncomputable def req (s u₀ : ℝ) : ℝ :=
  if Int.fract (s * u₀) < 1/8 then (1/8 - Int.fract (s * u₀)) / s
  else if 7/8 < Int.fract (s * u₀) then (9/8 - Int.fract (s * u₀)) / s
  else 0

noncomputable def room (s u₀ : ℝ) : ℝ :=
  if 7/8 < Int.fract (s * u₀) then (15/8 - Int.fract (s * u₀)) / s
  else (7/8 - Int.fract (s * u₀)) / s

/-- A point whose phase lies in `[1/8, 7/8]` above an integer `N` is clear. -/
theorem band {x : ℝ} (N : ℤ) (h1 : (N : ℝ) + 1 / 8 ≤ x) (h2 : x ≤ (N : ℝ) + 7 / 8) :
    (8 : ℝ)⁻¹ ≤ circDist x := by
  have hfl : ⌊x⌋ = N := by rw [Int.floor_eq_iff]; constructor <;> linarith
  unfold circDist
  simp only [Int.fract, hfl, le_min_iff]
  constructor <;> linarith

/-- **The move is sound.**  Requirement `≤ ε ≤` room puts the runner clear at `u₀ + ε`. -/
theorem clear_after_move {s u₀ ε : ℝ} (hs : 0 < s)
    (hreq : req s u₀ ≤ ε) (hroom : ε ≤ room s u₀) :
    (8 : ℝ)⁻¹ ≤ circDist (s * (u₀ + ε)) := by
  set φ := Int.fract (s * u₀) with hφ
  set k := ⌊s * u₀⌋ with hk
  have hsplit : s * u₀ = (k : ℝ) + φ := (Int.floor_add_fract (s * u₀)).symm
  have hφ0 : 0 ≤ φ := Int.fract_nonneg _
  have hφ1 : φ < 1 := Int.fract_lt_one _
  have e : s * (u₀ + ε) = (k : ℝ) + φ + s * ε := by rw [mul_add, hsplit]
  rw [e]
  unfold req at hreq; unfold room at hroom
  rw [← hφ] at hreq hroom
  by_cases hlo : φ < 1/8
  · have hhi : ¬ (7/8 < φ) := by linarith
    simp only [hlo, if_true] at hreq
    simp only [hhi, if_false] at hroom
    rw [div_le_iff₀ hs] at hreq; rw [le_div_iff₀ hs] at hroom
    exact band k (by linarith) (by linarith)
  · by_cases hhi : 7/8 < φ
    · simp only [hlo, hhi, if_true, if_false] at hreq
      simp only [hhi, if_true] at hroom
      rw [div_le_iff₀ hs] at hreq; rw [le_div_iff₀ hs] at hroom
      exact band (k + 1) (by push_cast; linarith) (by push_cast; linarith)
    · simp only [hlo, hhi, if_false] at hreq hroom
      rw [le_div_iff₀ hs] at hroom
      have hε : 0 ≤ s * ε := mul_nonneg hs.le hreq
      exact band k (by push_cast at *; linarith) (by linarith)

/-! ## The counterexample's runner at speed 160

Speeds `(1, 31, 75, 97, 128, 160, 176, 225)`.  Differences from 160: `159, 129, 85, 63, 32, 16, 65`;
`d_min = 16`, readings `159/16, 129/16, 85/16, 63/16, 2, 1, 65/16` — not integral, so outside the
integer lemmas.  Base `u₀ = 1/8`; the largest requirement is `ε = 5/344`; `u = 6/43`, `t = 3/344`,
which is this runner's earliest isolation instant. -/

theorem fract_eq {x : ℝ} (k : ℤ) (h1 : (k : ℝ) ≤ x) (h2 : x < k + 1) : Int.fract x = x - k := by
  rw [← Int.self_sub_floor, (Int.floor_eq_iff).mpr ⟨h1, h2⟩]

theorem runner160_lonely : ∀ d ∈ ({159, 129, 85, 63, 32, 16, 65} : Finset ℝ),
    (8 : ℝ)⁻¹ ≤ circDist (d * (3 / 344)) := by
  intro d hd
  have hε : (3 : ℝ) / 344 = (1 / 8 + 5 / 344) / 16 := by norm_num
  rw [hε, show d * ((1 / 8 + 5 / 344) / 16) = (d / 16) * (1 / 8 + 5 / 344) by ring]
  have key : ∀ s : ℝ, 0 < s → req s (1/8) ≤ 5/344 → 5/344 ≤ room s (1/8) →
      (8 : ℝ)⁻¹ ≤ circDist (s * (1/8 + 5/344)) := fun s hs h1 h2 => clear_after_move hs h1 h2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  refine key _ (by norm_num) ?_ ?_ <;> simp only [req, room]
  -- 159/16 · 1/8 = 159/128: phase 31/128, clear
  · rw [fract_eq 1 (by norm_num) (by norm_num)]; norm_num
  · rw [fract_eq 1 (by norm_num) (by norm_num)]; norm_num
  -- 129/16 · 1/8 = 129/128: phase 1/128, blocked low
  · rw [fract_eq 1 (by norm_num) (by norm_num)]; norm_num
  · rw [fract_eq 1 (by norm_num) (by norm_num)]; norm_num
  -- 85/128: clear
  · rw [fract_eq 0 (by norm_num) (by norm_num)]; norm_num
  · rw [fract_eq 0 (by norm_num) (by norm_num)]; norm_num
  -- 63/128: clear
  · rw [fract_eq 0 (by norm_num) (by norm_num)]; norm_num
  · rw [fract_eq 0 (by norm_num) (by norm_num)]; norm_num
  -- 32/16 = 2: 1/4, clear
  · rw [fract_eq 0 (by norm_num) (by norm_num)]; norm_num
  · rw [fract_eq 0 (by norm_num) (by norm_num)]; norm_num
  -- 16/16 = 1: 1/8, clear (on the threshold)
  · rw [fract_eq 0 (by norm_num) (by norm_num)]; norm_num
  · rw [fract_eq 0 (by norm_num) (by norm_num)]; norm_num
  -- 65/128: clear
  · rw [fract_eq 0 (by norm_num) (by norm_num)]; norm_num
  · rw [fract_eq 0 (by norm_num) (by norm_num)]; norm_num

end BufferRoom

#print axioms BufferRoom.clear_after_move
#print axioms BufferRoom.runner160_lonely
