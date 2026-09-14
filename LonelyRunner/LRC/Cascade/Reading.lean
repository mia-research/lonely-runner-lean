import LonelyRunner.LRC.ConstructionN.Band

/-!
# The owner's model: every arrangement is a deviation from an ideal

Part of the cascade artefact (`LRC/Cascade/`).  Owner, 2026-09-14:

> every speed arrangement is individual deviation from an ideal, those ideals we represent as
> either AP or Grid with dmin finding any AP deviation.  The ap gap is coded as 1 e.g. (1...8)
> it can always represent the speed, that's because AP is gap not a number; the cascade is the
> way to deal with it.

Formalised here, over real speeds, no runner pinned, no window, every lap:

* `IdealReading` — an arrangement read as an ideal AP of gap `D` (a real scale) plus each
  runner's deviation.  `reading` gives one for **every** arrangement and **every** gap.
* `gap_is_a_scale` — coding the gap as `1` changes no distance.
* `position_in_eighths` — at the ideal's AP instant `t = r/(8D)`, runner `j` sits
  `(idx j − idx i)·r` eighths from the subject, plus its deviation `× r/D`.
* `clear_iff` — it is clear exactly when that position is at least one eighth from every
  multiple of `8`.
* `on_ideal_clear` — a runner with no deviation relative to the subject is clear at every
  `r` coprime to `8` unless its index difference is a multiple of `8`.
* `nearest_on_ideal_above/below` — read at gap `d_min` from the subject, the nearest runner is
  on the ideal: index `±1`, no deviation.
* `lonely_of_reading` — if every runner lands clear, the subject is lonely at `t = r/(8D)`.

**Not stated here:** which gap the cascade gives for a given arrangement.  `D` is an input.
-/

namespace CascadeRule

/-- An arrangement read as an ideal AP of gap `D`, plus each runner's individual deviation. -/
structure IdealReading (v : Fin 8 → ℝ) where
  D : ℝ
  hD : 0 < D
  base : ℝ
  idx : Fin 8 → ℤ
  dev : Fin 8 → ℝ
  eq : ∀ j, v j = base + idx j * D + dev j

/-- **Every arrangement can be read against an ideal AP of every gap**: index by whole gaps
from `base`, the remainder is the deviation. -/
noncomputable def reading (v : Fin 8 → ℝ) (D : ℝ) (hD : 0 < D) (base : ℝ) : IdealReading v where
  D := D
  hD := hD
  base := base
  idx j := ⌊(v j - base) / D⌋
  dev j := v j - base - ⌊(v j - base) / D⌋ * D
  eq j := by ring

/-- The deviations of `reading` lie in `[0, D)`. -/
theorem reading_dev_bounds (v : Fin 8 → ℝ) (D : ℝ) (hD : 0 < D) (base : ℝ) (j : Fin 8) :
    0 ≤ (reading v D hD base).dev j ∧ (reading v D hD base).dev j < D := by
  simp only [reading]
  set q := (v j - base) / D with hq
  have hqD : q * D = v j - base := by rw [hq]; field_simp
  have h1 : (⌊q⌋ : ℝ) ≤ q := Int.floor_le q
  have h2 : q < (⌊q⌋ : ℝ) + 1 := Int.lt_floor_add_one q
  constructor
  · nlinarith
  · nlinarith

/-- **The AP is a gap, not a number.**  Scaling every speed and the gap by `λ` changes nothing. -/
theorem gap_is_a_scale {a b D lam r : ℝ} (hD : D ≠ 0) (hl : lam ≠ 0) :
    (lam * a - lam * b) * (r / (8 * (lam * D))) = (a - b) * (r / (8 * D)) := by
  field_simp

/-- **Where each runner sits at the ideal's AP instant `t = r/(8D)`**, in eighths. -/
theorem position_in_eighths {v : Fin 8 → ℝ} (R : IdealReading v) (r : ℤ) (i j : Fin 8) :
    (v j - v i) * ((r : ℝ) / (8 * R.D))
      = ((((R.idx j - R.idx i) * r : ℤ) : ℝ) + (R.dev j - R.dev i) * r / R.D) / 8 := by
  have hD := R.hD.ne'
  rw [R.eq j, R.eq i]
  push_cast
  field_simp
  ring

/-- **The clearing test in the ideal's coordinates.** -/
theorem clear_iff {v : Fin 8 → ℝ} (R : IdealReading v) (r : ℤ) (i j : Fin 8) :
    (8 : ℝ)⁻¹ ≤ circDist ((v j - v i) * ((r : ℝ) / (8 * R.D))) ↔
      ∀ k : ℤ, 1 ≤ |((((R.idx j - R.idx i) * r : ℤ) : ℝ) + (R.dev j - R.dev i) * r / R.D)
                    - 8 * k| := by
  rw [position_in_eighths]
  have h := ConstructionN.band_identity 8 (by norm_num)
    ((((R.idx j - R.idx i) * r : ℤ) : ℝ) + (R.dev j - R.dev i) * r / R.D)
  simpa using h

/-- **A runner on the ideal is clear** at every `r` coprime to `8`, unless its index difference
from the subject is a multiple of `8`. -/
theorem on_ideal_clear {v : Fin 8 → ℝ} (R : IdealReading v) {r : ℤ} (hr : IsCoprime (8 : ℤ) r)
    (i j : Fin 8) (hdev : R.dev j = R.dev i) (hidx : ¬ (8 : ℤ) ∣ (R.idx j - R.idx i)) :
    (8 : ℝ)⁻¹ ≤ circDist ((v j - v i) * ((r : ℝ) / (8 * R.D))) := by
  rw [position_in_eighths, hdev, sub_self, zero_mul, zero_div, add_zero]
  have hnd : ¬ ((8 : ℕ) : ℤ) ∣ ((R.idx j - R.idx i) * r) := by
    intro hd
    have hd' : (8 : ℤ) ∣ (R.idx j - R.idx i) * r := by exact_mod_cast hd
    exact hidx (hr.dvd_of_dvd_mul_right hd')
  have h := ConstructionN.circDist_int_div (n := 8) (by norm_num) hnd
  simpa using h

/-- **`d_min` finds the deviation** (neighbour above): read at gap `d_min` from the subject, the
nearest runner is on the ideal, one gap along. -/
theorem nearest_on_ideal_above (v : Fin 8 → ℝ) (i nb : Fin 8) {dmin : ℝ} (hm : 0 < dmin)
    (hnb : v nb - v i = dmin) :
    (reading v dmin hm (v i)).dev nb = (reading v dmin hm (v i)).dev i ∧
      (reading v dmin hm (v i)).idx nb - (reading v dmin hm (v i)).idx i = 1 := by
  simp only [reading, hnb, sub_self, zero_div, Int.floor_zero, div_self hm.ne', Int.floor_one]
  constructor <;> simp

/-- **`d_min` finds the deviation** (neighbour below). -/
theorem nearest_on_ideal_below (v : Fin 8 → ℝ) (i nb : Fin 8) {dmin : ℝ} (hm : 0 < dmin)
    (hnb : v nb - v i = -dmin) :
    (reading v dmin hm (v i)).dev nb = (reading v dmin hm (v i)).dev i ∧
      (reading v dmin hm (v i)).idx nb - (reading v dmin hm (v i)).idx i = -1 := by
  have h : -dmin / dmin = -1 := by field_simp
  simp only [reading, hnb, sub_self, zero_div, Int.floor_zero, h]
  have hf : ⌊(-1 : ℝ)⌋ = -1 := by norm_num
  rw [hf]
  constructor <;> simp

/-- **Soundness of the reading.**  If every other runner lands clear at the ideal's AP instant,
the subject is lonely there, and the instant is a positive time. -/
theorem lonely_of_reading {v : Fin 8 → ℝ} (R : IdealReading v) {r : ℤ} (hr0 : 0 < r) (i : Fin 8)
    (h : ∀ j, j ≠ i → ∀ k : ℤ,
      1 ≤ |((((R.idx j - R.idx i) * r : ℤ) : ℝ) + (R.dev j - R.dev i) * r / R.D) - 8 * k|) :
    0 < (r : ℝ) / (8 * R.D) ∧
      ∀ j, j ≠ i → (8 : ℝ)⁻¹ ≤ circDist ((v j - v i) * ((r : ℝ) / (8 * R.D))) := by
  have hD := R.hD
  have hr : (0 : ℝ) < r := by exact_mod_cast hr0
  exact ⟨by positivity, fun j hj => (clear_iff R r i j).mpr (h j hj)⟩

/-! ## The √2 arrangement, read as a deviation from the ideal `(1, …, 8)` -/

noncomputable def δ : ℝ := Real.sqrt 2 / 100

/-- Speeds `(1, 1+δ, 3, 4, 5, 6, 7, 8)`. -/
noncomputable def W : Fin 8 → ℝ := ![1, 1 + δ, 3, 4, 5, 6, 7, 8]

/-- Read from runner 1 against the ideal AP of gap `1`: one runner deviates, by `δ`. -/
noncomputable def R1 : IdealReading W where
  D := 1
  hD := one_pos
  base := 1
  idx := ![0, 0, 2, 3, 4, 5, 6, 7]
  dev := ![0, δ, 0, 0, 0, 0, 0, 0]
  eq j := by fin_cases j <;> simp [W] <;> norm_num

theorem sqrt2_bounds : (141421 / 100000 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < (141422 / 100000 : ℝ) := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hp : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor <;> nlinarith

/-- **The deviation sets the lap.**  At `r = 69` the deviating runner has moved less than one
eighth; at `r = 71` it has moved at least one. -/
theorem deviation_sets_the_lap : 69 * δ < 1 ∧ 1 ≤ 71 * δ ∧ 71 * δ ≤ 7 := by
  obtain ⟨hlo, hhi⟩ := sqrt2_bounds
  unfold δ
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

/-- **Runner 1 is lonely at the ideal's AP instant `t = 71/8`**, proved in the ideal's
coordinates: the six runners on the ideal by `on_ideal_clear`, the deviating one by its
landing position `71·δ`. -/
theorem r1_lonely : ∀ j : Fin 8, j ≠ 0 →
    (8 : ℝ)⁻¹ ≤ circDist ((W j - W 0) * (((71 : ℤ) : ℝ) / (8 * R1.D))) := by
  obtain ⟨_, h1, h7⟩ := deviation_sets_the_lap
  have hcop : IsCoprime (8 : ℤ) 71 := by
    rw [Int.isCoprime_iff_gcd_eq_one]; rfl
  intro j hj
  fin_cases j
  · exact absurd rfl hj
  · -- the deviating runner
    refine (clear_iff R1 71 0 1).mpr ?_
    intro k
    simp only [R1]
    norm_num
    rcases le_or_gt k 0 with hk | hk
    · have hk' : (k : ℝ) ≤ 0 := by exact_mod_cast hk
      rw [abs_of_nonneg (by nlinarith)]; nlinarith
    · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
      rw [abs_of_neg (by nlinarith)]; nlinarith
  all_goals
    exact on_ideal_clear R1 hcop 0 _ (by simp [R1]) (by simp [R1])

end CascadeRule
