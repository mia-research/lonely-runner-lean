import Mathlib

/-!
# The link rule between consecutive setters

2026-10-02 (running log E319).  In `R = 8·d_min·t` a reading `ρ > 0` blocks the zone `((8j−1)/ρ, (8j+1)/ρ)` on lap `j`.  The cascade moves to the exit
`(8j+1)/ρ_x` of the zone that sets the move.  If that exit lies in the zone of another reading `y` on lap `j'`, then

* `y` slower than `x` (`ρ_y < ρ_x`): `j' ≤ j`;
* `y` faster (`ρ_x < ρ_y`): `j < j'`;
* `ρ_y = ρ_x`: no link (`equal_not_inZone`).

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.ZoneLink

/-- The exit of `x`'s lap-`j` zone lies in `y`'s lap-`j'` zone. -/
def InZone (ρx ρy : ℝ) (j j' : ℕ) : Prop :=
  (8 * (j' : ℝ) - 1) / ρy < (8 * (j : ℝ) + 1) / ρx ∧ (8 * (j : ℝ) + 1) / ρx < (8 * (j' : ℝ) + 1) / ρy

theorem inZone_iff {ρx ρy : ℝ} (hx : 0 < ρx) (hy : 0 < ρy) {j j' : ℕ} :
    InZone ρx ρy j j' ↔ (8 * (j' : ℝ) - 1) * ρx < (8 * (j : ℝ) + 1) * ρy ∧ (8 * (j : ℝ) + 1) * ρy < (8 * (j' : ℝ) + 1) * ρx := by
  unfold InZone
  rw [div_lt_div_iff₀ hy hx, div_lt_div_iff₀ hx hy]

/-- A slower reading enters at the same or a lower lap. -/
theorem slower_lap_le {ρx ρy : ℝ} (hx : 0 < ρx) (hy : 0 < ρy) (hxy : ρy < ρx) {j j' : ℕ}
    (h : InZone ρx ρy j j') : j' ≤ j := by
  rw [inZone_iff hx hy] at h
  obtain ⟨h1, _⟩ := h
  by_contra hc
  push Not at hc
  have hj : (j : ℝ) + 1 ≤ j' := by exact_mod_cast hc
  nlinarith

/-- A faster reading enters at a strictly higher lap. -/
theorem faster_lap_lt {ρx ρy : ℝ} (hx : 0 < ρx) (hy : 0 < ρy) (hxy : ρx < ρy) {j j' : ℕ}
    (h : InZone ρx ρy j j') : j < j' := by
  rw [inZone_iff hx hy] at h
  obtain ⟨_, h2⟩ := h
  by_contra hc
  push Not at hc
  have hj : (j' : ℝ) ≤ j := by exact_mod_cast hc
  nlinarith

/-- Equal readings cannot link: the exit of `x`'s zone is the exit of `y`'s zone on the same lap and not inside any zone of `y`. -/
theorem equal_not_inZone {ρ : ℝ} (hρ : 0 < ρ) {j j' : ℕ} : ¬ InZone ρ ρ j j' := by
  intro h
  rw [inZone_iff hρ hρ] at h
  obtain ⟨h1, h2⟩ := h
  have c1 : (8 * (j' : ℝ) - 1) < 8 * (j : ℝ) + 1 := by nlinarith
  have c2 : (8 * (j : ℝ) + 1) < 8 * (j' : ℝ) + 1 := by nlinarith
  have d1 : j' < j + 1 := by
    have : (j' : ℝ) < j + 1 := by linarith
    exact_mod_cast this
  have d2 : j < j' := by
    have : (j : ℝ) < j' := by linarith
    exact_mod_cast this
  omega

end LRC.ZoneLink
