import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.LonelyCells
import Fresh.DispCell
import Fresh.TwoScale
import Fresh.OneMultiple

/-!
# The second stage of the one-multiple family: the residue of `x = 8c` at an opener (Task CJ)

Written 2026-10-11.  Imports Mathlib and the Fresh modules named in the task.  Nothing is imported from the existing
`LonelyRunner` repo.  Exact reals and integers; every statement is symbolic.

Setting.  `D'` is a set of integer readings (the subject's disparities other than the one multiple of 8), `x = 8c` the
added reading, `c ≥ 1` (no runner at speed 0).  The left end `u` of a later cell of `D'` is an opening of a reading `d`
(`LonelyCells.cell_left_end_is_opening` [L]): `u = (k + 1/8)/d`.  Then
`x u = 8c (k + 1/8)/d = c (8k+1)/d = q + r/d`, `M = c (8k+1)`, `q = M / d`, `r = M % d` (integer division).

Results.
* (1) `clear_at_opening_iff_residue` [L]: `1/8 ≤ distInt (x u)` iff `d ≤ 8 r ≤ 7 d`; the exact displacement of
  `disp x u` in the two blocked cases (`x_mul_displacement_below`, `x_mul_displacement_above`, and the combined
  `displacement_at_opening`): below `(1/8 - r/d)/x`, above `(9/8 - r/d)/x`.
* (2) periodicity in `c` mod `d` (`residue_congr`, `clear_congr`, `x_mul_displacement_congr`), the lap-line case
  `d ∣ c(8k+1)` (`lap_line_iff_dvd`, `displacement_of_dvd`), and the clear residues (`clearResidues`,
  `clearResidues_card`) `[PROVISIONAL: counting tool]`.
* (3) `survives_cell_residue_iff` [L] (a cell `[u,w]` survives `x = 8c` iff the residue is in `[d/8, 7d/8]` or the extra
  step fits in the cell) `[PROVISIONAL: covering]`, with the version for the cells of an integer set
  (`survives_cell_residue_iff_cell`, using `LonelyCells.cell_left_end_is_opening` by name).

Provenance.  Corresponds to the exact data `experiments/n8/one_multiple_residue_v1.py` (prediction) and to
`Fresh.DispCell` (`disp_of_near`, `mul_displacement`, `survives_iff_phase`, `survive_iff`, `disp_eq_self_iff`), which are
reused by name; the residue arithmetic is re-derived here in `ℤ` and `ℝ` (the clear-iff-window step has the same content
as `Localisation.clear_of_window` and `OneMultiple.clear_of_residue`, but is proved as an iff, written for this file;
nothing was copied, and no declaration of the existing repo was used).
-/

open Classical

namespace Fresh.SecondStage

open Fresh Fresh.LonelyCells Fresh.DispCell

/-! ## (0) Clearance in terms of a fractional part -/

/-- Clearance is a statement about every integer [L] (own proof; `distInt x = |x - round x|` is attained at `round x`). -/
theorem eighth_le_distInt_iff (y : ℝ) : (1 / 8 : ℝ) ≤ distInt y ↔ ∀ z : ℤ, (1 / 8 : ℝ) ≤ |y - z| := by
  constructor
  · intro h z; exact h.trans (Cascade.distInt_le y z)
  · intro h; exact h (round y)

#print axioms eighth_le_distInt_iff

/-- **Clearance of `q + s` for `s ∈ [0,1)`** [L]: `1/8 ≤ distInt (q + s)` iff `1/8 ≤ s ≤ 7/8`.  Both hypotheses
`0 ≤ s`, `s < 1` REQUIRED (for `s = 1` or `s = -1/16` the right side is false while the left is not). -/
theorem eighth_le_distInt_add_iff (q : ℤ) {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) :
    (1 / 8 : ℝ) ≤ distInt ((q : ℝ) + s) ↔ 1 / 8 ≤ s ∧ s ≤ 7 / 8 := by
  rw [eighth_le_distInt_iff]
  constructor
  · intro h
    have a := h q
    have b := h (q + 1)
    push_cast at b
    rw [show (q : ℝ) + s - q = s by ring, abs_of_nonneg h0] at a
    rw [show (q : ℝ) + s - (q + 1) = s - 1 by ring, abs_of_neg (by linarith)] at b
    constructor <;> linarith
  · rintro ⟨ha, hb⟩ z
    rcases le_or_gt z q with hz | hz
    · have : (z : ℝ) ≤ q := by exact_mod_cast hz
      rw [abs_of_nonneg (by linarith)]; linarith
    · have : (q : ℝ) + 1 ≤ z := by exact_mod_cast hz
      rw [abs_of_nonpos (by linarith)]; linarith

#print axioms eighth_le_distInt_add_iff

/-- The residue decomposition `M / d = (M / d) + (M % d)/d` in `ℝ` [L], for `0 < d`. -/
theorem div_residue (M d : ℤ) (hd : 0 < d) :
    (M : ℝ) / d = ((M / d : ℤ) : ℝ) + ((M % d : ℤ) : ℝ) / d := by
  have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have h : M = M % d + d * (M / d) := (Int.emod_add_mul_ediv M d).symm
  have h' : (M : ℝ) = ((M % d : ℤ) : ℝ) + d * ((M / d : ℤ) : ℝ) := by exact_mod_cast h
  rw [h']; field_simp; ring

#print axioms div_residue

/-- **Clearance of `M/d` in residue form** [L]: `1/8 ≤ distInt (M/d)` iff `d ≤ 8 (M mod d) ≤ 7 d`.  `0 < d` REQUIRED
(`d = 0`: `M/0 = 0` is blocked while `0 ≤ 0 ≤ 0` holds). -/
theorem clear_div_iff (M d : ℤ) (hd : 0 < d) :
    (1 / 8 : ℝ) ≤ distInt ((M : ℝ) / d) ↔ d ≤ 8 * (M % d) ∧ 8 * (M % d) ≤ 7 * d := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have h0 : (0 : ℝ) ≤ ((M % d : ℤ) : ℝ) / d := by
    have := Int.emod_nonneg M hd.ne'
    positivity
  have h1 : ((M % d : ℤ) : ℝ) / d < 1 := by
    rw [div_lt_one hdr]; exact_mod_cast Int.emod_lt_of_pos M hd
  rw [div_residue M d hd, eighth_le_distInt_add_iff _ h0 h1, le_div_iff₀ hdr, div_le_iff₀ hdr]
  constructor
  · rintro ⟨a, b⟩
    constructor
    · have : ((d : ℤ) : ℝ) ≤ 8 * ((M % d : ℤ) : ℝ) := by linarith
      exact_mod_cast this
    · have : 8 * ((M % d : ℤ) : ℝ) ≤ 7 * (d : ℝ) := by linarith
      exact_mod_cast this
  · rintro ⟨a, b⟩
    have a' : (d : ℝ) ≤ 8 * ((M % d : ℤ) : ℝ) := by exact_mod_cast a
    have b' : 8 * ((M % d : ℤ) : ℝ) ≤ 7 * (d : ℝ) := by exact_mod_cast b
    constructor <;> linarith

#print axioms clear_div_iff

/-! ## (1) The reading `x = 8c` at the opening `u = (k + 1/8)/d` -/

/-- `x u = c (8k+1) / d` for `x = 8c`, `u = (k + 1/8)/d` [L]. -/
theorem xu_eq (c k d : ℤ) (hd : 0 < d) :
    (8 * (c : ℝ)) * (((k : ℝ) + 1 / 8) / d) = ((c * (8 * k + 1) : ℤ) : ℝ) / d := by
  have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast; field_simp

#print axioms xu_eq

/-- **(1a) `clear_at_opening_iff_residue`** [L]: for integers `d ≥ 1`, `k`, `c`, `x = 8c`, `u = (k + 1/8)/d`:
`1/8 ≤ distInt (x u)` iff `d ≤ 8 r ≤ 7 d`, `r = c(8k+1) mod d`.  Hypotheses: `0 < d` REQUIRED; `0 ≤ k` NOT REQUIRED;
`0 < c` NOT REQUIRED here (the clearance of the number `x u` does not see the sign of `c`; it is REQUIRED in the
`disp` statements below, where `x > 0` is needed). -/
theorem clear_at_opening_iff_residue_any (c k d : ℤ) (hd : 0 < d) :
    (1 / 8 : ℝ) ≤ distInt ((8 * (c : ℝ)) * (((k : ℝ) + 1 / 8) / d)) ↔
      d ≤ 8 * ((c * (8 * k + 1)) % d) ∧ 8 * ((c * (8 * k + 1)) % d) ≤ 7 * d := by
  rw [xu_eq c k d hd, clear_div_iff _ d hd]

#print axioms clear_at_opening_iff_residue_any

/-- **`clear_at_opening_iff_residue`** [L]: the statement of the brief, with `c ≥ 1` and `k ≥ 0` kept as hypotheses (the
proof uses neither; see `clear_at_opening_iff_residue_any`), stated for `DispCell.disp`: `disp x u = u` iff `x` is clear
at `u` iff `d ≤ 8 r ≤ 7 d`. -/
theorem clear_at_opening_iff_residue (c k d : ℤ) (hd : 0 < d) (hc : 0 < c) (_hk : 0 ≤ k) :
    (1 / 8 : ℝ) ≤ distInt ((8 * (c : ℝ)) * (((k : ℝ) + 1 / 8) / d)) ↔
      d ≤ 8 * ((c * (8 * k + 1)) % d) ∧ 8 * ((c * (8 * k + 1)) % d) ≤ 7 * d := by
  have _ := hc
  exact clear_at_opening_iff_residue_any c k d hd

#print axioms clear_at_opening_iff_residue

theorem x_pos (c : ℤ) (hc : 0 < c) : (0 : ℝ) < 8 * (c : ℝ) := by
  have : (0 : ℝ) < c := by exact_mod_cast hc
  linarith

/-- `disp x u = u` iff the residue is in `[d/8, 7d/8]` [L] (`DispCell.disp_eq_self_iff`). -/
theorem disp_eq_self_iff_residue (c k d : ℤ) (hd : 0 < d) (hc : 0 < c) :
    disp (8 * (c : ℝ)) (((k : ℝ) + 1 / 8) / d) = ((k : ℝ) + 1 / 8) / d ↔
      d ≤ 8 * ((c * (8 * k + 1)) % d) ∧ 8 * ((c * (8 * k + 1)) % d) ≤ 7 * d := by
  rw [disp_eq_self_iff (x_pos c hc)]
  exact clear_at_opening_iff_residue_any c k d hd

#print axioms disp_eq_self_iff_residue

/-- **Blocked below** [L]: if `x u = q + r/d` with `0 ≤ r`, `8 r < d` then `x * displacement x u = 1/8 - r/d`
(`DispCell.mul_displacement` at lap `q`).  `0 < x` REQUIRED; `0 ≤ r` REQUIRED (for `r < 0` the point is below the lap
line and the formula is the one of `disp_of_near` with the same `q`, but the sign of the step changes meaning). -/
theorem x_mul_displacement_below {x u : ℝ} (hx : 0 < x) {q r d : ℤ} (hd : 0 < d) (hr0 : 0 ≤ r) (hr : 8 * r < d)
    (hxu : x * u = (q : ℝ) + (r : ℝ) / d) : x * displacement x u = 1 / 8 - (r : ℝ) / d := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hr0' : (0 : ℝ) ≤ r := by exact_mod_cast hr0
  have hr' : 8 * (r : ℝ) < d := by exact_mod_cast hr
  have hk : |x * u - q| < 1 / 8 := by
    rw [hxu, show (q : ℝ) + r / d - q = r / d by ring, abs_of_nonneg (by positivity), div_lt_iff₀ hdr]
    linarith
  rw [mul_displacement hx hk, hxu]; ring

#print axioms x_mul_displacement_below

/-- **Blocked above** [L]: if `x u = q + r/d` with `r < d`, `7 d < 8 r` then `x * displacement x u = 9/8 - r/d`
(lap `q + 1`). -/
theorem x_mul_displacement_above {x u : ℝ} (hx : 0 < x) {q r d : ℤ} (hd : 0 < d) (hrd : r < d) (hr : 7 * d < 8 * r)
    (hxu : x * u = (q : ℝ) + (r : ℝ) / d) : x * displacement x u = 9 / 8 - (r : ℝ) / d := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hrd' : (r : ℝ) < d := by exact_mod_cast hrd
  have hr' : 7 * (d : ℝ) < 8 * r := by exact_mod_cast hr
  have h7 : (7 : ℝ) / 8 < (r : ℝ) / d := by rw [lt_div_iff₀ hdr]; linarith
  have h1 : (r : ℝ) / d < 1 := by rw [div_lt_one hdr]; exact hrd'
  have hk : |x * u - ((q + 1 : ℤ) : ℝ)| < 1 / 8 := by
    push_cast
    rw [hxu, show (q : ℝ) + r / d - (q + 1) = r / d - 1 by ring, abs_of_neg (by linarith)]
    linarith
  rw [mul_displacement hx hk, hxu]; push_cast; ring

#print axioms x_mul_displacement_above

/-- **The extra step** of the reading `x` at a left end with residue `r` against `d` (the formula of the brief):
`(1/8 - r/d)/x` below, `(9/8 - r/d)/x` above, `0` when `x` is clear. -/
noncomputable def extraStep (d r : ℤ) (x : ℝ) : ℝ :=
  if 8 * r < d then (1 / 8 - (r : ℝ) / d) / x else if 7 * d < 8 * r then (9 / 8 - (r : ℝ) / d) / x else 0

/-- **(1b) `displacement_at_opening`** [L]: the exact displacement at an opening.  For integers `d ≥ 1`, `k`, `c ≥ 1`,
`x = 8c`, `u = (k+1/8)/d`, `r = c(8k+1) mod d`: `disp x u - u = extraStep d r x`.  In particular `0` when clear, `(1/8 - r/d)/x`
when `8r < d` and `(9/8 - r/d)/x` when `7d < 8r`.  `0 ≤ k` NOT REQUIRED. -/
theorem displacement_at_opening (c k d : ℤ) (hd : 0 < d) (hc : 0 < c) :
    displacement (8 * (c : ℝ)) (((k : ℝ) + 1 / 8) / d) = extraStep d ((c * (8 * k + 1)) % d) (8 * (c : ℝ)) := by
  have hx := x_pos c hc
  set M := c * (8 * k + 1) with hM
  set r := M % d with hr
  have hxu : (8 * (c : ℝ)) * (((k : ℝ) + 1 / 8) / d) = ((M / d : ℤ) : ℝ) + (r : ℝ) / d := by
    rw [xu_eq c k d hd, div_residue M d hd]
  have hr0 : 0 ≤ r := Int.emod_nonneg M hd.ne'
  have hrd : r < d := Int.emod_lt_of_pos M hd
  unfold extraStep
  split_ifs with h1 h2
  · have := x_mul_displacement_below hx hd hr0 h1 hxu
    rw [eq_div_iff hx.ne', mul_comm]; exact this
  · have := x_mul_displacement_above hx hd hrd h2 hxu
    rw [eq_div_iff hx.ne', mul_comm]; exact this
  · have hcl' : d ≤ 8 * r ∧ 8 * r ≤ 7 * d := ⟨by omega, by omega⟩
    have hcl : (1 / 8 : ℝ) ≤ distInt ((8 * (c : ℝ)) * (((k : ℝ) + 1 / 8) / d)) :=
      (clear_at_opening_iff_residue_any c k d hd).mpr hcl'
    unfold displacement
    rw [(disp_eq_self_iff hx _).mpr hcl]; ring

#print axioms displacement_at_opening

/-- The two blocked cases in terms of `disp` itself [L]: below, `disp x u = (q + 1/8)/x`; above, `(q + 1 + 1/8)/x`,
`q = c(8k+1) / d` (integer division). -/
theorem disp_at_opening_below (c k d : ℤ) (hd : 0 < d) (hc : 0 < c) (h : 8 * ((c * (8 * k + 1)) % d) < d) :
    disp (8 * (c : ℝ)) (((k : ℝ) + 1 / 8) / d) = (((c * (8 * k + 1) / d : ℤ) : ℝ) + 1 / 8) / (8 * (c : ℝ)) := by
  have hx := x_pos c hc
  have hxu := (xu_eq c k d hd).trans (div_residue (c * (8 * k + 1)) d hd)
  have hr0 : 0 ≤ (c * (8 * k + 1)) % d := Int.emod_nonneg _ hd.ne'
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hr0' : (0 : ℝ) ≤ (((c * (8 * k + 1)) % d : ℤ) : ℝ) := by exact_mod_cast hr0
  have hr' : 8 * (((c * (8 * k + 1)) % d : ℤ) : ℝ) < d := by exact_mod_cast h
  have hk : |(8 * (c : ℝ)) * (((k : ℝ) + 1 / 8) / d) - ((c * (8 * k + 1) / d : ℤ) : ℝ)| < 1 / 8 := by
    rw [hxu, add_sub_cancel_left, abs_of_nonneg (by positivity), div_lt_iff₀ hdr]
    linarith
  exact disp_of_near hk

#print axioms disp_at_opening_below

theorem disp_at_opening_above (c k d : ℤ) (hd : 0 < d) (_hc : 0 < c) (h : 7 * d < 8 * ((c * (8 * k + 1)) % d)) :
    disp (8 * (c : ℝ)) (((k : ℝ) + 1 / 8) / d) =
      (((c * (8 * k + 1) / d + 1 : ℤ) : ℝ) + 1 / 8) / (8 * (c : ℝ)) := by
  have hxu := (xu_eq c k d hd).trans (div_residue (c * (8 * k + 1)) d hd)
  have hrd : (c * (8 * k + 1)) % d < d := Int.emod_lt_of_pos _ hd
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hrd' : (((c * (8 * k + 1)) % d : ℤ) : ℝ) < d := by exact_mod_cast hrd
  have hr' : 7 * (d : ℝ) < 8 * (((c * (8 * k + 1)) % d : ℤ) : ℝ) := by exact_mod_cast h
  have h7 : (7 : ℝ) / 8 < (((c * (8 * k + 1)) % d : ℤ) : ℝ) / d := by rw [lt_div_iff₀ hdr]; linarith
  have h1 : (((c * (8 * k + 1)) % d : ℤ) : ℝ) / d < 1 := by rw [div_lt_one hdr]; exact hrd'
  have hk : |(8 * (c : ℝ)) * (((k : ℝ) + 1 / 8) / d) - ((c * (8 * k + 1) / d + 1 : ℤ) : ℝ)| < 1 / 8 := by
    push_cast
    rw [hxu, show ((c * (8 * k + 1) / d : ℤ) : ℝ) + (((c * (8 * k + 1)) % d : ℤ) : ℝ) / d
        - (((c * (8 * k + 1) / d : ℤ) : ℝ) + 1) = (((c * (8 * k + 1)) % d : ℤ) : ℝ) / d - 1 by ring,
      abs_of_neg (by linarith)]
    linarith
  have := disp_of_near hk
  push_cast at this ⊢
  exact this

#print axioms disp_at_opening_above

/-! ## (2) Periodicity in `c` mod `d`, the lap-line case, the clear residues -/

/-- The numerator of the extra step in `x`-units: `x * extraStep d r x`. -/
noncomputable def stepNum (d r : ℤ) : ℝ :=
  if 8 * r < d then 1 / 8 - (r : ℝ) / d else if 7 * d < 8 * r then 9 / 8 - (r : ℝ) / d else 0

theorem x_mul_extraStep {x : ℝ} (hx : x ≠ 0) (d r : ℤ) : x * extraStep d r x = stepNum d r := by
  unfold extraStep stepNum
  split_ifs
  · field_simp
  · field_simp
  · simp

#print axioms x_mul_extraStep

/-- The residue depends on `c` only through `c` mod `d` [L]. -/
theorem residue_congr {c c' : ℤ} (k d : ℤ) (h : c ≡ c' [ZMOD d]) :
    (c * (8 * k + 1)) % d = (c' * (8 * k + 1)) % d :=
  Int.ModEq.mul_right _ h

#print axioms residue_congr

/-- **(2a) Period `d` in `c`: clearance** [L].  If `c ≡ c' (mod d)` then `x = 8c` is clear at `u = (k+1/8)/d` iff `x' = 8c'`
is.  `0 < d` REQUIRED; no sign or positivity of `c, c'` needed. -/
theorem clear_congr {c c' : ℤ} (k d : ℤ) (hd : 0 < d) (h : c ≡ c' [ZMOD d]) :
    (1 / 8 : ℝ) ≤ distInt ((8 * (c : ℝ)) * (((k : ℝ) + 1 / 8) / d)) ↔
      (1 / 8 : ℝ) ≤ distInt ((8 * (c' : ℝ)) * (((k : ℝ) + 1 / 8) / d)) := by
  rw [clear_at_opening_iff_residue_any c k d hd, clear_at_opening_iff_residue_any c' k d hd, residue_congr k d h]

#print axioms clear_congr

/-- **(2a) Period `d` in `c`: the displacement in `x`-units** [L].  If `c ≡ c' (mod d)`, `c, c' ≥ 1`, then
`x * displacement x u = x' * displacement x' u`: the phase displacement `1/8 - r/d`, `9/8 - r/d` or `0` depends on `c`
only through `c` mod `d`; the displacement itself is that number divided by `x = 8c`, so it carries the scale of `c`. -/
theorem x_mul_displacement_congr {c c' : ℤ} (k d : ℤ) (hd : 0 < d) (hc : 0 < c) (hc' : 0 < c')
    (h : c ≡ c' [ZMOD d]) :
    (8 * (c : ℝ)) * displacement (8 * (c : ℝ)) (((k : ℝ) + 1 / 8) / d) =
      (8 * (c' : ℝ)) * displacement (8 * (c' : ℝ)) (((k : ℝ) + 1 / 8) / d) := by
  rw [displacement_at_opening c k d hd hc, displacement_at_opening c' k d hd hc',
    x_mul_extraStep (x_pos c hc).ne', x_mul_extraStep (x_pos c' hc').ne', residue_congr k d h]

#print axioms x_mul_displacement_congr

/-- **(2b) The lap-line case** [L]: `x u` is an integer iff `d ∣ c(8k+1)` (iff the residue is `0`). -/
theorem lap_line_iff_dvd (c k d : ℤ) (hd : 0 < d) :
    (∃ N : ℤ, (8 * (c : ℝ)) * (((k : ℝ) + 1 / 8) / d) = N) ↔ d ∣ c * (8 * k + 1) := by
  have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [xu_eq c k d hd]
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, ?_⟩
    rw [div_eq_iff hdr] at hN
    have : ((c * (8 * k + 1) : ℤ) : ℝ) = ((d * N : ℤ) : ℝ) := by rw [hN]; push_cast; ring
    exact_mod_cast this
  · rintro ⟨N, hN⟩
    refine ⟨N, ?_⟩
    rw [hN]; push_cast; field_simp

#print axioms lap_line_iff_dvd

/-- **(2b) `displacement_of_dvd`** [L]: if `d ∣ c(8k+1)` then `x u = N` is an integer (`x` stands on a lap line at `u`),
`r = 0`, `x` is in the way at `u`, and the displacement is exactly `1/(8x)`: the step is `1/(8x)`.  `0 < d`, `0 < c` REQUIRED
(`x > 0`; for `c = 0` see `audit_c_zero`). -/
theorem displacement_of_dvd (c k d : ℤ) (hd : 0 < d) (hc : 0 < c) (hdvd : d ∣ c * (8 * k + 1)) :
    (∃ N : ℤ, (8 * (c : ℝ)) * (((k : ℝ) + 1 / 8) / d) = N) ∧ (c * (8 * k + 1)) % d = 0 ∧
      InWay (8 * (c : ℝ)) (((k : ℝ) + 1 / 8) / d) ∧
      displacement (8 * (c : ℝ)) (((k : ℝ) + 1 / 8) / d) = 1 / (8 * (8 * (c : ℝ))) := by
  have hx := x_pos c hc
  have hr : (c * (8 * k + 1)) % d = 0 := Int.emod_eq_zero_of_dvd hdvd
  refine ⟨(lap_line_iff_dvd c k d hd).mpr hdvd, hr, ?_, ?_⟩
  · obtain ⟨N, hN⟩ := (lap_line_iff_dvd c k d hd).mpr hdvd
    unfold InWay
    rw [hN]
    have : distInt (N : ℝ) = 0 := by
      have := Cascade.distInt_add_int 0 N
      simp [distInt] at this
      simp [distInt]
    rw [this]; norm_num
  · rw [displacement_at_opening c k d hd hc, hr]
    unfold extraStep
    rw [if_pos (by omega)]
    simp
    field_simp

#print axioms displacement_of_dvd

/-- **The step is `1/(8x)` exactly when `d ∣ c(8k+1)`** [L] (the converse of `displacement_of_dvd`): in the clear case the
step is `0`; below it is `(1/8 - r/d)/x < ... ≠ 1/(8x)` unless `r = 0`; above it is `(9/8 - r/d)/x > 1/(8x)`. -/
theorem displacement_eq_eighth_iff_dvd (c k d : ℤ) (hd : 0 < d) (hc : 0 < c) :
    displacement (8 * (c : ℝ)) (((k : ℝ) + 1 / 8) / d) = 1 / (8 * (8 * (c : ℝ))) ↔ d ∣ c * (8 * k + 1) := by
  constructor
  · intro h
    have hx := x_pos c hc
    have hdr : (0 : ℝ) < d := by exact_mod_cast hd
    rw [displacement_at_opening c k d hd hc] at h
    have hr0 : 0 ≤ (c * (8 * k + 1)) % d := Int.emod_nonneg _ hd.ne'
    have hrd : (c * (8 * k + 1)) % d < d := Int.emod_lt_of_pos _ hd
    unfold extraStep at h
    split_ifs at h with h1 h2
    · have h' : 1 / 8 - (((c * (8 * k + 1)) % d : ℤ) : ℝ) / d = 1 / 8 := by
        have := congrArg (fun z => z * (8 * (c : ℝ))) h
        simp only at this
        field_simp at this ⊢
        linarith
      have h'' : (((c * (8 * k + 1)) % d : ℤ) : ℝ) / d = 0 := by linarith
      rw [div_eq_zero_iff] at h''
      rcases h'' with h0 | h0
      · have : (c * (8 * k + 1)) % d = 0 := by exact_mod_cast h0
        exact Int.dvd_of_emod_eq_zero this
      · exact absurd h0 hdr.ne'
    · have hrd' : (((c * (8 * k + 1)) % d : ℤ) : ℝ) < d := by exact_mod_cast hrd
      have h' : 9 / 8 - (((c * (8 * k + 1)) % d : ℤ) : ℝ) / d = 1 / 8 := by
        have := congrArg (fun z => z * (8 * (c : ℝ))) h
        simp only at this
        field_simp at this ⊢
        linarith
      have h1' : (((c * (8 * k + 1)) % d : ℤ) : ℝ) / d < 1 := by rw [div_lt_one hdr]; exact hrd'
      linarith
    · exfalso
      have : (0 : ℝ) < 1 / (8 * (8 * (c : ℝ))) := by positivity
      linarith
  · intro h
    exact (displacement_of_dvd c k d hd hc h).2.2.2

#print axioms displacement_eq_eighth_iff_dvd

/-- **(2c) The clear residues**: the residues `r ∈ Z/d` (as representatives `0 ≤ r < d`) with `d ≤ 8 r ≤ 7 d`. -/
noncomputable def clearResidues (d : ℤ) : Finset ℤ := (Finset.Ico 0 d).filter (fun r => d ≤ 8 * r ∧ 8 * r ≤ 7 * d)

theorem mem_clearResidues {d r : ℤ} : r ∈ clearResidues d ↔ 0 ≤ r ∧ r < d ∧ d ≤ 8 * r ∧ 8 * r ≤ 7 * d := by
  unfold clearResidues
  simp only [Finset.mem_filter, Finset.mem_Ico]
  tauto

/-- **The exact set of clear residues** [L]: for `d ≥ 1`, `clearResidues d = {r : ⌈d/8⌉ ≤ r ≤ ⌊7d/8⌋}`, with
`⌈d/8⌉ = (d+7)/8` and `⌊7d/8⌋ = 7d/8` in integer division.  `1 ≤ d` REQUIRED for `r < d` to be automatic. -/
theorem clearResidues_eq_Icc (d : ℤ) (hd : 0 < d) : clearResidues d = Finset.Icc ((d + 7) / 8) (7 * d / 8) := by
  ext r
  rw [mem_clearResidues, Finset.mem_Icc]
  omega

#print axioms clearResidues_eq_Icc

/-- **(2c) `clearResidues_card`** [L] `[PROVISIONAL: counting tool]` (supports the description of how many residues of the
reading `r = c(8k+1) mod d` leave `x` clear, and no existence claim; serves step D: the isolation of the d_min window
[1,7] is displaced by the setters and the cascade shows where it lands): the number of clear residues is
`⌊7d/8⌋ - ⌈d/8⌉ + 1`. -/
theorem clearResidues_card (d : ℤ) (hd : 0 < d) :
    ((clearResidues d).card : ℤ) = 7 * d / 8 - (d + 7) / 8 + 1 := by
  rw [clearResidues_eq_Icc d hd, Int.card_Icc]
  have : 0 ≤ 7 * d / 8 + 1 - (d + 7) / 8 := by omega
  rw [Int.toNat_of_nonneg this]; ring

#print axioms clearResidues_card

/-- The same count with the floor and ceiling of the reals `7d/8` and `d/8` [L] `[PROVISIONAL: counting tool]`. -/
theorem clearResidues_card_floor_ceil (d : ℤ) (hd : 0 < d) :
    ((clearResidues d).card : ℤ) = ⌊(7 * (d : ℝ)) / 8⌋ - ⌈(d : ℝ) / 8⌉ + 1 := by
  have hf : ⌊(7 * (d : ℝ)) / 8⌋ = 7 * d / 8 := by
    rw [Int.floor_eq_iff]
    have h1 : 8 * (7 * d / 8) ≤ 7 * d := by omega
    have h2 : 7 * d < 8 * (7 * d / 8) + 8 := by omega
    have h1' : (8 : ℝ) * ((7 * d / 8 : ℤ) : ℝ) ≤ 7 * (d : ℝ) := by exact_mod_cast h1
    have h2' : 7 * (d : ℝ) < 8 * ((7 * d / 8 : ℤ) : ℝ) + 8 := by exact_mod_cast h2
    constructor <;> linarith
  have hc : ⌈(d : ℝ) / 8⌉ = (d + 7) / 8 := by
    rw [Int.ceil_eq_iff]
    have h1 : 8 * ((d + 7) / 8) ≥ d := by omega
    have h2 : 8 * ((d + 7) / 8) < d + 8 := by omega
    have h1' : (d : ℝ) ≤ 8 * (((d + 7) / 8 : ℤ) : ℝ) := by exact_mod_cast h1
    have h2' : 8 * (((d + 7) / 8 : ℤ) : ℝ) < d + 8 := by exact_mod_cast h2
    constructor
    · linarith
    · linarith
  rw [hf, hc]
  exact clearResidues_card d hd

#print axioms clearResidues_card_floor_ceil

/-- **Clear iff the residue is a clear residue** [L]. -/
theorem clear_iff_mem_clearResidues (c k d : ℤ) (hd : 0 < d) :
    (1 / 8 : ℝ) ≤ distInt ((8 * (c : ℝ)) * (((k : ℝ) + 1 / 8) / d)) ↔ (c * (8 * k + 1)) % d ∈ clearResidues d := by
  rw [clear_at_opening_iff_residue_any c k d hd, mem_clearResidues]
  have h0 := Int.emod_nonneg (c * (8 * k + 1)) hd.ne'
  have h1 := Int.emod_lt_of_pos (c * (8 * k + 1)) hd
  tauto

#print axioms clear_iff_mem_clearResidues

/-- **Counting the classes of `c` (coprime case)** [L] `[PROVISIONAL: counting tool]` (supports the description of how many
classes `c` mod `d` leave `x` clear, and no existence claim; serves step D: the isolation of the d_min window [1,7] is
displaced by the setters and the cascade shows where it lands).  If `gcd(8k+1, d) = 1`, multiplication by `8k+1` permutes
the classes of `Z/d`, so exactly `⌊7d/8⌋ - ⌈d/8⌉ + 1` classes of `c` mod `d` leave `x` clear at `u`.  `IsCoprime (8k+1) d`
REQUIRED for this count (without it `c ↦ c(8k+1)` is `g`-to-one onto the multiples of `g = gcd`; the count is then
`g · #{clear residues divisible by g}`, not argued here). -/
theorem clear_classes_card (k d : ℤ) (hd : 0 < d) (hcop : IsCoprime (8 * k + 1) d) :
    (((Finset.Ico 0 d).filter (fun c => (c * (8 * k + 1)) % d ∈ clearResidues d)).card : ℤ) =
      7 * d / 8 - (d + 7) / 8 + 1 := by
  rw [← clearResidues_card d hd]
  norm_cast
  obtain ⟨s, t, hst⟩ := hcop
  refine Finset.card_bij (fun c _ => (c * (8 * k + 1)) % d) ?_ ?_ ?_
  · intro c hc
    exact (Finset.mem_filter.mp hc).2
  · intro c hc c' hc' h
    have hc1 := Finset.mem_Ico.mp (Finset.mem_filter.mp hc).1
    have hc1' := Finset.mem_Ico.mp (Finset.mem_filter.mp hc').1
    have hm : c * (8 * k + 1) ≡ c' * (8 * k + 1) [ZMOD d] := h
    have hdv : d ∣ (c' - c) * (8 * k + 1) := by
      have := (Int.modEq_iff_dvd.mp hm)
      convert this using 1; ring
    have hcop' : IsCoprime d (8 * k + 1) := ⟨t, s, by linarith⟩
    have hdv2 : d ∣ c' - c := hcop'.dvd_of_dvd_mul_right hdv
    have : c ≡ c' [ZMOD d] := Int.modEq_iff_dvd.mpr hdv2
    have h2 : c % d = c' % d := this
    rwa [Int.emod_eq_of_lt hc1.1 hc1.2, Int.emod_eq_of_lt hc1'.1 hc1'.2] at h2
  · intro r hr
    have hr1 := mem_clearResidues.mp hr
    refine ⟨(r * s) % d, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Ico]
      refine ⟨⟨Int.emod_nonneg _ hd.ne', Int.emod_lt_of_pos _ hd⟩, ?_⟩
      have h1 : ((r * s) % d * (8 * k + 1)) % d = (r * s * (8 * k + 1)) % d :=
        (Int.mod_modEq _ _).mul_right _
      have h2 : r * s * (8 * k + 1) = r + d * (-(r * t)) := by linear_combination r * hst
      rw [h1, h2, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hr1.1 hr1.2.1]
      exact hr
    · have h1 : ((r * s) % d * (8 * k + 1)) % d = (r * s * (8 * k + 1)) % d :=
        (Int.mod_modEq _ _).mul_right _
      have h2 : r * s * (8 * k + 1) = r + d * (-(r * t)) := by linear_combination r * hst
      show ((r * s) % d * (8 * k + 1)) % d = r
      rw [h1, h2, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hr1.1 hr1.2.1]

#print axioms clear_classes_card

/-! ## (3) The cell level: survival in residue form -/

/-- **(3) `survives_cell_residue_iff`** [L] `[PROVISIONAL: covering]` at this step: the extra step against the cell length
`w - u`; supports the claim "the cell survives the added reading `x` iff its displacement fits in the cell" and no
existence claim; serves step D: the isolation of the d_min window [1,7] is displaced by the setters and the cascade shows
where it lands.

For a set `S` of readings with `[u, w] ⊆ lonelySet S`, `u ≤ w`, `u = (k + 1/8)/d` (`d ≥ 1`), `x = 8c` (`c ≥ 1`),
`r = c(8k+1) mod d`: some point of `[u, w]` is lonely for `insert x S` iff
`d ≤ 8r ≤ 7d`, or `8r < d` and `(1/8 - r/d)/x ≤ w - u`, or `7d < 8r` and `(9/8 - r/d)/x ≤ w - u`.
Hypotheses: `[u,w] ⊆ lonelySet S` REQUIRED (`survive_iff`); `u ≤ w` REQUIRED (clear case, as in
`survives_iff_opening_or_clear`); `d ∈ S` NOT REQUIRED (only the form of `u` is used; it is the content of
`survives_cell_residue_iff_cell` that a cell end of an integer set has this form); `0 ≤ k` NOT REQUIRED; maximality of
the cell and integrality of the elements of `S` NOT REQUIRED. -/
theorem survives_cell_residue_iff {S : Finset ℝ} {u w : ℝ} (c k d : ℤ) (hd : 0 < d) (hc : 0 < c)
    (hsub : Set.Icc u w ⊆ lonelySet S) (huw : u ≤ w) (hu : u = ((k : ℝ) + 1 / 8) / d) :
    (∃ s ∈ Set.Icc u w, s ∈ lonelySet (insert (8 * (c : ℝ)) S)) ↔
      (d ≤ 8 * ((c * (8 * k + 1)) % d) ∧ 8 * ((c * (8 * k + 1)) % d) ≤ 7 * d) ∨
      (8 * ((c * (8 * k + 1)) % d) < d ∧
        (1 / 8 - (((c * (8 * k + 1)) % d : ℤ) : ℝ) / d) / (8 * (c : ℝ)) ≤ w - u) ∨
      (7 * d < 8 * ((c * (8 * k + 1)) % d) ∧
        (9 / 8 - (((c * (8 * k + 1)) % d : ℤ) : ℝ) / d) / (8 * (c : ℝ)) ≤ w - u) := by
  rw [survive_iff (x_pos c hc) hsub]
  have hdisp : disp (8 * (c : ℝ)) u ≤ w ↔ displacement (8 * (c : ℝ)) u ≤ w - u := by
    unfold displacement; constructor <;> intro h <;> linarith
  rw [hdisp, hu, displacement_at_opening c k d hd hc, ← hu]
  unfold extraStep
  split_ifs with h1 h2
  · constructor
    · intro h; exact Or.inr (Or.inl ⟨h1, h⟩)
    · rintro (⟨a, _⟩ | ⟨_, h⟩ | ⟨a, _⟩)
      · omega
      · exact h
      · omega
  · constructor
    · intro h; exact Or.inr (Or.inr ⟨h2, h⟩)
    · rintro (⟨a, b⟩ | ⟨a, _⟩ | ⟨_, h⟩)
      · omega
      · omega
      · exact h
  · constructor
    · intro _; exact Or.inl ⟨by omega, by omega⟩
    · intro _; linarith

#print axioms survives_cell_residue_iff

/-- The same statement with the extra step as one function [L]: the cell survives iff `extraStep d r x ≤ w - u`
(`extraStep = 0` when `x` is clear at `u`).  `[PROVISIONAL: covering]` at this step: the extra step against the cell
length; supports the displacement-against-cell statement and no existence claim; serves step D. -/
theorem survives_cell_extraStep_iff {S : Finset ℝ} {u w : ℝ} (c k d : ℤ) (hd : 0 < d) (hc : 0 < c)
    (hsub : Set.Icc u w ⊆ lonelySet S) (hu : u = ((k : ℝ) + 1 / 8) / d) :
    (∃ s ∈ Set.Icc u w, s ∈ lonelySet (insert (8 * (c : ℝ)) S)) ↔
      extraStep d ((c * (8 * k + 1)) % d) (8 * (c : ℝ)) ≤ w - u := by
  rw [survive_iff (x_pos c hc) hsub]
  have hdisp : disp (8 * (c : ℝ)) u ≤ w ↔ displacement (8 * (c : ℝ)) u ≤ w - u := by
    unfold displacement; constructor <;> intro h <;> linarith
  rw [hdisp, hu, displacement_at_opening c k d hd hc, ← hu]

#print axioms survives_cell_extraStep_iff

/-- **A failing cell is shorter than the extra step** [L] `[PROVISIONAL: covering]` at this step: the cell length against
the extra step; supports the description of why a cell fails and no existence claim; serves step D.  If no point of
`[u, w]` is lonely for `insert x S` then `x` is blocked at `u` and `x (w - u)` is below `1/8 - r/d` (blocked below) or
below `9/8 - r/d` (blocked above); in particular `r ≠ ` a clear residue. -/
theorem cell_fails_short {S : Finset ℝ} {u w : ℝ} (c k d : ℤ) (hd : 0 < d) (hc : 0 < c)
    (hsub : Set.Icc u w ⊆ lonelySet S) (huw : u ≤ w) (hu : u = ((k : ℝ) + 1 / 8) / d)
    (hno : ∀ s ∈ Set.Icc u w, s ∉ lonelySet (insert (8 * (c : ℝ)) S)) :
    (8 * ((c * (8 * k + 1)) % d) < d ∧
        (8 * (c : ℝ)) * (w - u) < 1 / 8 - (((c * (8 * k + 1)) % d : ℤ) : ℝ) / d) ∨
      (7 * d < 8 * ((c * (8 * k + 1)) % d) ∧
        (8 * (c : ℝ)) * (w - u) < 9 / 8 - (((c * (8 * k + 1)) % d : ℤ) : ℝ) / d) := by
  have hx := x_pos c hc
  have hiff := survives_cell_residue_iff (S := S) c k d hd hc hsub huw hu
  have hn : ¬ ∃ s ∈ Set.Icc u w, s ∈ lonelySet (insert (8 * (c : ℝ)) S) := by
    rintro ⟨s, hs, hl⟩; exact hno s hs hl
  rw [hiff] at hn
  push Not at hn
  obtain ⟨h1, h2, h3⟩ := hn
  by_cases hb : 8 * ((c * (8 * k + 1)) % d) < d
  · left
    refine ⟨hb, ?_⟩
    have := h2 hb
    rw [lt_div_iff₀ hx] at this
    linarith
  · right
    have hb2 : 7 * d < 8 * ((c * (8 * k + 1)) % d) := by
      by_contra hcon
      exact absurd (h1 (by omega)) (by omega)
    refine ⟨hb2, ?_⟩
    have := h3 hb2
    rw [lt_div_iff₀ hx] at this
    linarith

#print axioms cell_fails_short

/-- **(3') The cells of an integer set** [L] `[PROVISIONAL: covering]` at this step (extra step against cell length;
supports the survival statement and no existence claim; serves step D).  `D` a finite set of positive integers, `S` its
image in `ℝ`, `[u, w]` a cell of `S`, `c ≥ 1`.  By `LonelyCells.cell_left_end_is_opening` the left end `u` is
`(k + 1/8)/d` for some `d ∈ D` and `k : ℕ`, and then the cell survives `x = 8c` iff the residue statement of
`survives_cell_residue_iff` holds.  `d ∈ D` and `u > 0` REQUIRED here (they give the form of `u`). -/
theorem survives_cell_residue_iff_cell (D : Finset ℤ) (hD : ∀ d ∈ D, 0 < d) {u w : ℝ} (c : ℤ) (hc : 0 < c)
    (hcell : IsCell (D.image (fun d : ℤ => (d : ℝ))) u w) :
    ∃ d ∈ D, ∃ k : ℕ, u = (((k : ℤ) : ℝ) + 1 / 8) / (d : ℝ) ∧
      ((∃ s ∈ Set.Icc u w, s ∈ lonelySet (insert (8 * (c : ℝ)) (D.image (fun d : ℤ => (d : ℝ))))) ↔
        extraStep d ((c * (8 * (k : ℤ) + 1)) % d) (8 * (c : ℝ)) ≤ w - u) := by
  have hpos : ∀ x ∈ D.image (fun d : ℤ => (d : ℝ)), 0 < x := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    exact_mod_cast hD d hd
  obtain ⟨x, hx, k, hu, -, -, -⟩ := cell_left_end_is_opening hpos hcell
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
  refine ⟨d, hd, k, by rw [hu]; push_cast; rfl, ?_⟩
  exact survives_cell_extraStep_iff c k d (hD d hd) hc hcell.2.2.1 (by rw [hu]; push_cast; rfl)

#print axioms survives_cell_residue_iff_cell

/-! ## (4) Hypothesis audits: counterexamples to the dropped hypotheses -/

/-- `d = 1` is the smallest case allowed; for `d = 0` (with `M = 0`) the residue statement is false: `0/0 = 0` in `ℝ` is blocked, but
`d ≤ 8 (M mod d) ≤ 7 d` reads `0 ≤ 0 ≤ 0` (`d ≥ 1` REQUIRED) [L]. -/
theorem audit_d_zero : ¬ ((1 / 8 : ℝ) ≤ distInt (((0 : ℤ) : ℝ) / ((0 : ℤ) : ℝ)) ↔
    (0 : ℤ) ≤ 8 * ((0 : ℤ) % 0) ∧ 8 * ((0 : ℤ) % 0) ≤ 7 * 0) := by
  intro h
  have h1 : ¬ (1 / 8 : ℝ) ≤ distInt (((0 : ℤ) : ℝ) / ((0 : ℤ) : ℝ)) := by
    simp [distInt]
  exact h1 (h.mpr (by norm_num))

#print axioms audit_d_zero

/-- For `d < 0` the residue statement is false: `M = 1`, `d = -2`, `1/(-2) = -1/2` is clear but
`d ≤ 8 r ≤ 7 d` reads `-2 ≤ 8 ∧ 8 ≤ -14` (`d ≥ 1` REQUIRED) [L]. -/
theorem audit_d_neg : ¬ ((1 / 8 : ℝ) ≤ distInt (((1 : ℤ) : ℝ) / ((-2 : ℤ) : ℝ)) ↔
    (-2 : ℤ) ≤ 8 * ((1 : ℤ) % (-2)) ∧ 8 * ((1 : ℤ) % (-2)) ≤ 7 * (-2)) := by
  intro h
  have h1 : (1 / 8 : ℝ) ≤ distInt (((1 : ℤ) : ℝ) / ((-2 : ℤ) : ℝ)) := by
    have : (((1 : ℤ) : ℝ) / ((-2 : ℤ) : ℝ)) = (-1 : ℝ) + 1 / 2 := by norm_num
    rw [this, show (-1 : ℝ) + 1 / 2 = ((-1 : ℤ) : ℝ) + 1 / 2 by norm_num,
      eighth_le_distInt_add_iff (-1) (by norm_num) (by norm_num)]
    norm_num
  have := h.mp h1
  norm_num at this

#print axioms audit_d_neg

/-- `c = 0` (a runner at speed 0) is excluded: `x = 0`, `k = 0`, `d = 1`, `u = 1/8`: `disp 0 u = 0` so the displacement is
`-1/8`, while the formula gives `extraStep = 0` (`c ≥ 1` REQUIRED for `displacement_at_opening`) [L]. -/
theorem audit_c_zero : displacement (8 * ((0 : ℤ) : ℝ)) ((((0 : ℤ) : ℝ) + 1 / 8) / ((1 : ℤ) : ℝ)) ≠
    extraStep 1 ((0 * (8 * 0 + 1)) % 1) (8 * ((0 : ℤ) : ℝ)) := by
  unfold displacement disp extraStep
  have hw : InWay (8 * ((0 : ℤ) : ℝ)) ((((0 : ℤ) : ℝ) + 1 / 8) / ((1 : ℤ) : ℝ)) := by
    unfold InWay distInt; simp
  rw [if_pos hw]
  unfold nextOpening
  simp

#print axioms audit_c_zero

/-! ## (5) What remains owed -/

/-- **The one-multiple instance at four to six readings (the second-stage statement)**: for every set `D'` of four to six
positive integers, none divisible by 8, and every `c ≥ 1`, some cell `[u, w]` of `D'` has `disp (8c) u ≤ w`, i.e. (by
`survive_iff`, `exists_lonely_iff_cell`) the cell passes: its residue `r = c(8k+1) mod d` at its opener, and its
length, pass `survives_cell_residue_iff`.  Nothing in this folder proves it.  Checked as exact data only in the
populations of `experiments/n8/second_stage_v1.out` [OBS]. -/
-- STANDING: OWED
def OneMultipleCellExists : Prop :=
  ∀ (D : Finset ℤ) (c : ℤ), 0 < c → (∀ d ∈ D, 0 < d ∧ ¬ (8 : ℤ) ∣ d) → 4 ≤ D.card → D.card ≤ 6 →
    ∃ u w : ℝ, IsCell (D.image (fun d : ℤ => (d : ℝ))) u w ∧ disp (8 * (c : ℝ)) u ≤ w

/-- The owed statement is the existence of a lonely instant for `D' ∪ {8c}` [L] (`DispCell.exists_lonely_iff_cell`):
`OneMultipleCellExists` iff for those `D, c` some `t > 0` is lonely for the real set `insert (8c) D'`. -/
theorem oneMultipleCellExists_iff :
    OneMultipleCellExists ↔
      ∀ (D : Finset ℤ) (c : ℤ), 0 < c → (∀ d ∈ D, 0 < d ∧ ¬ (8 : ℤ) ∣ d) → 4 ≤ D.card → D.card ≤ 6 →
        ∃ t : ℝ, 0 < t ∧ t ∈ lonelySet (insert (8 * (c : ℝ)) (D.image (fun d : ℤ => (d : ℝ)))) := by
  unfold OneMultipleCellExists
  refine forall_congr' fun D => forall_congr' fun c => imp_congr_right fun hc => imp_congr_right fun hD =>
    imp_congr_right fun h4 => imp_congr_right fun h6 => ?_
  have hpos : ∀ x ∈ D.image (fun d : ℤ => (d : ℝ)), 0 < x := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    exact_mod_cast (hD d hd).1
  have hne : (D.image (fun d : ℤ => (d : ℝ))).Nonempty := by
    apply Finset.Nonempty.image
    rw [← Finset.card_pos]; omega
  exact (exists_lonely_iff_cell hpos hne (x_pos c hc)).symm

#print axioms oneMultipleCellExists_iff

end Fresh.SecondStage
