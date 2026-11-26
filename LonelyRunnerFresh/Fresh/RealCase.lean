import Mathlib
import Fresh.Framework
import Fresh.Gate
import Fresh.TwoScale
import Fresh.BlockLanding
import Fresh.PathLaws
import Fresh.ZeroMargin

/-!
# The real case: no hypothesis of integrality or commensurability (Task AO)

Written 2026-10-09.  Imports `Mathlib` and the Fresh modules `Framework`, `Gate`, `TwoScale`, `BlockLanding`,
`PathLaws`, `ZeroMargin`; nothing from the existing `LonelyRunner` repo.  Exact reals only; every disparity is
positive (no runner is stationary); no density, coverage, cap, move budget or clock is the shape of any statement.

Owner's point (2026-10-09): the cascade does not see a difference between real and rational disparities; the integer
populations of E440 and E441 are test cases, and what they showed has to be re-read for general positive reals.

Coordinates.  `m > 0` is the base scale (in the application, `d_min`), `R = 8 m t` the gate coordinate, so the
reading of a disparity `d` at `t = R/(8m)` is `d t = ρ R / 8` laps with `ρ = d/m`.  `sres8 x = x - 8 round(x/8)` is the
signed residue of `x` modulo 8 (Lean's `round` sends the tie `x/8 = 1/2 + n` upward, so the range is `[-4, 4)`, not
`(-4, 4]`; nothing below depends on which end of the tie is taken).

Contents.
* (1) Real two-scale.  `clear_shift_iff`: at `R = R0 + ε` runner `e` is clear iff `m8 (δ + ρ ε) ∈ [1,7]`, where
  `ρ R0 = 8 z + δ`.  `blocked_iff`, `clear_iff`, `slack_iff`: with `|δ| ≤ 4`, blocked at `ε = 0` iff `|δ| < 1`, clear
  iff `|δ| ≥ 1`, clear with slack iff `|δ| > 1`.  `lonelyAt_gate_iff`: the same for a whole finite set.
  `nextOpening_gate`, `isMove_gate`, `isMove_of_gate`: the cascade move from `R0` is `ε = max over blocked e of (1 − δ_e)/ρ_e`.
  `dev_scale`: scale covariance (rational and integer disparities are the same case for the cascade).  `eps_strictAnti`: the
  residue alone does not determine the move.
  `sres_eq_mul_sres8`, `nextOpening_bound_gate`: the case `R0 = 1` is `BlockLanding.nextOpening_bound`.
  `blocked_integer_iff`: for integer `d` and odd integer `R0 = a`, blocked iff `8 ∣ d`, i.e. `δ = 0` exactly
  (TwoScale's multiples of 8): TwoScale is the special case `δ_e ∈ {0}` for the blocked set, where blocked means
  `δ = 0`; for real `ρ` the blocked set is `|δ| < 1`, an interval of offsets.
* (2) The non-generic locus.  `tie_ratio`; `touch_ratio`, `touch_of_ratio`: an (opener of `x`, entry of `y`) coincidence at a common
  instant is exactly `x (8k'+7) = y (8k+1)` with `k, k'` naturals.  `Generic`; `irrational_not_ratioForm`;
  `generic_cell_pos_width`; `generic_margin_point`; `isoSet_open_at_generic`.  `ratio_value_at_most_one`,
  `pair_ratio_dichotomy`, `nongeneric_params_countable`: along an affine path.
* The result the brief states as "every lonely instant is a point of positive margin" is FALSE even for generic sets:
  the left end of every cell has a runner at exactly `1/8` (`cell_end_zero_margin`).  What is true is that every cell
  of a generic set has positive width, so it contains lonely instants of positive margin.

Provenance (existing declarations whose argument was read and understood; no proof was copied).
* Part 1: `Fresh.TwoScale.reading_shift_real`, `eighth_le_distInt_iff_m8`; `Fresh.BlockLanding.nextOpening_bound`
  (existing repo counterpart: `LRC/Cascade/*` displacement at the bound, read for the idea only).
* Part 2: `Fresh.LonelyCells.cell_width`, `cell_nondegenerate_iff`, `cell_of_lonely`; `Fresh.Gate.interior_strictly_clear`;
  `Fresh.PathLaws.isoSet_open_of_strict`, `isoSet_dichotomy`.

Counting tool: none.  Covering: none used in any proof.
-/

open Classical Filter Topology

namespace Fresh.RealCase

open Fresh

/-! ## (1) Real two-scale -/

/-- The signed residue of `x` modulo `8`, `x = 8 z + sres8 x` with `z = round (x/8)`. -/
noncomputable def sres8 (x : ℝ) : ℝ := x - 8 * (round (x / 8) : ℝ)

theorem sres8_decomp (x : ℝ) : x = 8 * (round (x / 8) : ℝ) + sres8 x := by unfold sres8; ring

theorem abs_sres8_le (x : ℝ) : |sres8 x| ≤ 4 := by
  have h := abs_sub_round (x / 8)
  unfold sres8
  have e : x - 8 * (round (x / 8) : ℝ) = 8 * (x / 8 - (round (x / 8) : ℝ)) := by ring
  rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
  linarith

#print axioms abs_sres8_le

/-- Near an integer (`|y| ≤ 1/2`) the circle distance is `|y|`. -/
theorem distInt_of_abs_le {y : ℝ} (h : |y| ≤ 1 / 2) : distInt y = |y| := by
  apply le_antisymm
  · have := Cascade.distInt_le y 0
    simpa using this
  · unfold distInt
    by_cases hn : round y = 0
    · rw [hn]; simp
    · have h1 : (1 : ℝ) ≤ |((round y : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]
        have : 1 ≤ |round y| := Int.one_le_abs hn
        exact_mod_cast this
      have h2 : |((round y : ℤ) : ℝ)| ≤ |y - (round y : ℝ)| + |y| := by
        have := abs_sub_abs_le_abs_sub ((round y : ℤ) : ℝ) y
        have e : |((round y : ℤ) : ℝ) - y| = |y - (round y : ℝ)| := abs_sub_comm _ _
        linarith
      linarith

#print axioms distInt_of_abs_le

/-- A residue `δ` with `|δ| ≤ 4` has `distInt (δ/8) = |δ|/8`. -/
theorem distInt_resid {δ : ℝ} (h : |δ| ≤ 4) : distInt (δ / 8) = |δ| / 8 := by
  rw [distInt_of_abs_le (by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8)]; linarith),
    abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8)]

#print axioms distInt_resid

/-- **The exact decomposition at `R = R0 + ε`** [L].  If `ρ R0 = 8 z + δ`, runner `ρ` is clear at `R0 + ε` iff
`m8 (δ + ρ ε) ∈ [1, 7]`.  No hypothesis on `ρ`, `R0`, `δ` beyond the displayed equation. -/
theorem clear_shift_iff (ρ R0 ε δ : ℝ) (z : ℤ) (h : ρ * R0 = 8 * (z : ℝ) + δ) :
    (1 / 8 : ℝ) ≤ distInt (ρ * (R0 + ε) / 8) ↔ (1 ≤ TwoScale.m8 (δ + ρ * ε) ∧ TwoScale.m8 (δ + ρ * ε) ≤ 7) := by
  rw [TwoScale.reading_shift_real ρ R0 ε δ z h]
  exact TwoScale.eighth_le_distInt_iff_m8 _

#print axioms clear_shift_iff

/-- Same, with the canonical residue `δ = sres8 (ρ R0)`. -/
theorem clear_shift_iff' (ρ R0 ε : ℝ) :
    (1 / 8 : ℝ) ≤ distInt (ρ * (R0 + ε) / 8) ↔
      (1 ≤ TwoScale.m8 (sres8 (ρ * R0) + ρ * ε) ∧ TwoScale.m8 (sres8 (ρ * R0) + ρ * ε) ≤ 7) :=
  clear_shift_iff ρ R0 ε _ (round (ρ * R0 / 8)) (sres8_decomp _)

#print axioms clear_shift_iff'

/-- **Blocked at `ε = 0` iff `|δ| < 1`** [L] (the real analogue of "a multiple of 8"). -/
theorem blocked_iff {ρ R0 δ : ℝ} {z : ℤ} (h : ρ * R0 = 8 * (z : ℝ) + δ) (hδ : |δ| ≤ 4) :
    distInt (ρ * R0 / 8) < 1 / 8 ↔ |δ| < 1 := by
  have h0 := TwoScale.reading_shift_real ρ R0 0 δ z h
  simp only [add_zero, mul_zero] at h0
  rw [h0, distInt_resid hδ]
  constructor <;> intro hh <;> linarith

/-- **Clear at `ε = 0` iff `|δ| ≥ 1`** [L]. -/
theorem clear_iff {ρ R0 δ : ℝ} {z : ℤ} (h : ρ * R0 = 8 * (z : ℝ) + δ) (hδ : |δ| ≤ 4) :
    (1 / 8 : ℝ) ≤ distInt (ρ * R0 / 8) ↔ 1 ≤ |δ| := by
  rw [← not_lt, blocked_iff h hδ, not_lt]

/-- **Clear with slack at `ε = 0` iff `|δ| > 1`** [L]: positive margin, the runner survives small perturbations. -/
theorem slack_iff {ρ R0 δ : ℝ} {z : ℤ} (h : ρ * R0 = 8 * (z : ℝ) + δ) (hδ : |δ| ≤ 4) :
    (1 / 8 : ℝ) < distInt (ρ * R0 / 8) ↔ 1 < |δ| := by
  have h0 := TwoScale.reading_shift_real ρ R0 0 δ z h
  simp only [add_zero, mul_zero] at h0
  rw [h0, distInt_resid hδ]
  constructor <;> intro hh <;> linarith

/-- With `|δ| ≤ 4`, `δ mod 8 ∈ [1,7]` iff `|δ| ≥ 1`: the two descriptions of "clear at `ε = 0`" agree [L]. -/
theorem m8_window_iff_abs {δ : ℝ} (hδ : |δ| ≤ 4) :
    (1 ≤ TwoScale.m8 δ ∧ TwoScale.m8 δ ≤ 7) ↔ 1 ≤ |δ| := by
  rw [← TwoScale.eighth_le_distInt_iff_m8, distInt_resid hδ]
  constructor <;> intro hh <;> linarith

#print axioms blocked_iff
#print axioms clear_iff
#print axioms slack_iff
#print axioms m8_window_iff_abs

/-- The offset at which a blocked runner (`|δ| < 1`) opens, `ε = (1 − δ)/ρ`, is positive [L]. -/
theorem eps_pos {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : |δ| < 1) : 0 < (1 - δ) / ρ := by
  have := (abs_lt.mp hδ).2
  exact div_pos (by linarith) hρ

/-- At `ε = (1 − δ)/ρ` the shifted residue `δ + ρ ε` is exactly `1`: the opening [L]. -/
theorem reading_at_opening {ρ δ : ℝ} (hρ : 0 < ρ) : δ + ρ * ((1 - δ) / ρ) = 1 := by
  field_simp; ring

/-- **Same residue, different disparity, different move** [L]: the opening offset `(1 − δ)/ρ` is strictly decreasing in
`ρ` for fixed `δ < 1`.  So the rule "the residue `δ` determines the move" is false as a statement about the cascade;
this is the mechanism behind AN's pair `(1,…,8)` versus `(1,…,16)`, and it holds for every real `ρ`. -/
theorem eps_strictAnti {δ ρ ρ' : ℝ} (hδ : δ < 1) (hρ : 0 < ρ) (hlt : ρ < ρ') : (1 - δ) / ρ' < (1 - δ) / ρ := by
  have h1 : 0 < 1 - δ := by linarith
  exact div_lt_div_of_pos_left h1 hρ hlt

#print axioms eps_strictAnti

/-- A blocked runner stays blocked on `[0, (1 − δ)/ρ)`: its shifted residue stays in `(−1, 1)` [L]. -/
theorem blocked_until_opening {ρ δ ε : ℝ} (hρ : 0 < ρ) (hδ : |δ| < 1) (h0 : 0 ≤ ε) (h1 : ε < (1 - δ) / ρ) :
    |δ + ρ * ε| < 1 := by
  rw [lt_div_iff₀ hρ] at h1
  have := abs_lt.mp hδ
  rw [abs_lt]
  constructor <;> nlinarith

#print axioms eps_pos
#print axioms reading_at_opening
#print axioms blocked_until_opening

/-! ### The gate coordinate for a base scale `m` -/

/-- The reading of `d` at `t = R/(8m)` is `(d/m) R / 8` laps [L]. -/
theorem gate_reading {d m R : ℝ} (hm : 0 < m) : d * (R / (8 * m)) = (d / m) * R / 8 := by
  field_simp

/-- The signed residue of the runner `d` at the base point `R0` (base scale `m`). -/
noncomputable def dev (m R0 d : ℝ) : ℝ := sres8 (d / m * R0)

/-- **Scale covariance** [L]: the residue at the base point depends on `d` and `m` only through the ratio `d/m`.
Rescaling every disparity and the base scale by `c > 0` changes nothing in the gate coordinate.  This is the exact sense
in which the cascade does not distinguish rational from integer disparities (multiply by the common denominator), and
it is why the statements of this file carry no integrality hypothesis. -/
theorem dev_scale {c m R0 d : ℝ} (hc : 0 < c) : dev (c * m) R0 (c * d) = dev m R0 d := by
  unfold dev
  rw [mul_div_mul_left _ _ hc.ne']

#print axioms dev_scale

theorem abs_dev_le (m R0 d : ℝ) : |dev m R0 d| ≤ 4 := abs_sres8_le _

/-- Blocked at `R0` iff `|dev| < 1` [L]. -/
theorem inWay_gate_iff {d m R0 : ℝ} (hm : 0 < m) : InWay d (R0 / (8 * m)) ↔ |dev m R0 d| < 1 := by
  unfold InWay
  rw [gate_reading hm]
  exact blocked_iff (sres8_decomp _) (abs_dev_le m R0 d)

/-- Lonely at `(R0 + ε)/(8m)` iff every runner has `m8 (dev + ρ ε) ∈ [1,7]` [L]. -/
theorem lonelyAt_gate_iff {ds : Finset ℝ} {m R0 ε : ℝ} (hm : 0 < m) :
    Cascade.LonelyAt ds ((R0 + ε) / (8 * m)) ↔
      ∀ d ∈ ds, 1 ≤ TwoScale.m8 (dev m R0 d + d / m * ε) ∧ TwoScale.m8 (dev m R0 d + d / m * ε) ≤ 7 := by
  unfold Cascade.LonelyAt
  refine forall₂_congr (fun d _ => ?_)
  rw [gate_reading hm]
  exact clear_shift_iff' _ _ _

#print axioms gate_reading
#print axioms inWay_gate_iff
#print axioms lonelyAt_gate_iff

/-- **The next opening of a blocked runner in the gate coordinate** [L]:
`8 m · nextOpening d (R0/(8m)) = R0 + (1 − δ)/ρ`, `ρ = d/m`, `δ = dev m R0 d`.  Hypotheses: `m, d > 0` and `d` in the
way; nothing about integrality. -/
theorem nextOpening_gate {d m R0 : ℝ} (hm : 0 < m) (hd : 0 < d) (hw : InWay d (R0 / (8 * m))) :
    8 * m * nextOpening d (R0 / (8 * m)) = R0 + (1 - dev m R0 d) / (d / m) := by
  have hdev := (inWay_gate_iff hm).mp hw
  set x : ℝ := d / m * R0 with hx
  have hz : d * (R0 / (8 * m)) = x / 8 := by rw [gate_reading hm]
  have hk : |d * (R0 / (8 * m)) - ((round (x / 8) : ℤ) : ℝ)| < 1 / 8 := by
    rw [hz]
    have e : x / 8 - ((round (x / 8) : ℤ) : ℝ) = dev m R0 d / 8 := by
      unfold dev sres8; rw [← hx]; ring
    rw [e, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
    linarith
  rw [Cascade.nextOpening_eq hk]
  have hρ : 0 < d / m := div_pos hd hm
  have hdev' : dev m R0 d = x - 8 * (round (x / 8) : ℝ) := rfl
  have : (1 - dev m R0 d) / (d / m) = (8 * (round (x / 8) : ℝ) + 1) / (d / m) - R0 := by
    rw [hdev']
    field_simp
    rw [hx]; field_simp; ring
  rw [this]
  field_simp
  ring

#print axioms nextOpening_gate

/-- **The cascade move from `R0`, as a statement about residues** [L].  Let `ds` be positive disparities, `m > 0`,
`t0 = R0/(8m)`.  If `t'` is the cascade's move from `t0` and some runner is blocked at `R0`, then there is a blocked
runner `e` with `8 m t' = R0 + ε_e`, `ε_e = (1 − δ_e)/ρ_e`, and `ε_{e'} ≤ ε_e` for every blocked `e'`.  So the move is
`ε = max over blocked e of (1 − δ_e)/ρ_e`.  If none is blocked the move is the identity. -/
theorem isMove_gate {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m R0 t' : ℝ} (hm : 0 < m)
    (hmv : IsMove ds (R0 / (8 * m)) t') :
    ((∀ d ∈ ds, 1 ≤ |dev m R0 d|) ∧ t' = R0 / (8 * m)) ∨
    (∃ e ∈ ds, |dev m R0 e| < 1 ∧ 8 * m * t' = R0 + (1 - dev m R0 e) / (e / m) ∧
      ∀ e' ∈ ds, |dev m R0 e'| < 1 → (1 - dev m R0 e') / (e' / m) ≤ (1 - dev m R0 e) / (e / m)) := by
  rcases hmv with ⟨hn, rfl⟩ | ⟨e, he, hw, ht', hmax⟩
  · left
    refine ⟨fun d hd => ?_, rfl⟩
    have := hn d hd
    rw [inWay_gate_iff hm] at this
    exact not_lt.mp this
  · right
    refine ⟨e, he, (inWay_gate_iff hm).mp hw, ?_, ?_⟩
    · rw [ht']; exact nextOpening_gate hm (hpos e he) hw
    · intro e' he' hb
      have hw' : InWay e' (R0 / (8 * m)) := (inWay_gate_iff hm).mpr hb
      have h1 := hmax e' he' hw'
      have h2 := nextOpening_gate hm (hpos e' he') hw'
      have h3 : 8 * m * nextOpening e' (R0 / (8 * m)) ≤ 8 * m * t' := by gcongr
      rw [h2, ht', nextOpening_gate hm (hpos e he) hw] at h3
      linarith

#print axioms isMove_gate

/-- The converse: a blocked runner whose opening offset is maximal among the blocked runners gives the cascade
move [L].  Together with `isMove_gate`: `IsMove` from `R0/(8m)` is exactly "go to `R0 + max (1 − δ)/ρ`". -/
theorem isMove_of_gate {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m R0 t' : ℝ} (hm : 0 < m) {e : ℝ} (he : e ∈ ds)
    (hb : |dev m R0 e| < 1) (ht' : 8 * m * t' = R0 + (1 - dev m R0 e) / (e / m))
    (hmax : ∀ e' ∈ ds, |dev m R0 e'| < 1 → (1 - dev m R0 e') / (e' / m) ≤ (1 - dev m R0 e) / (e / m)) :
    IsMove ds (R0 / (8 * m)) t' := by
  right
  have hw : InWay e (R0 / (8 * m)) := (inWay_gate_iff hm).mpr hb
  have ht : t' = nextOpening e (R0 / (8 * m)) := by
    have h1 := nextOpening_gate hm (hpos e he) hw
    have h2 : 8 * m * t' = 8 * m * nextOpening e (R0 / (8 * m)) := by rw [h1, ht']
    exact mul_left_cancel₀ (by positivity) h2
  refine ⟨e, he, hw, ht, fun d' hd' hw' => ?_⟩
  have hb' := (inWay_gate_iff hm).mp hw'
  have h2 := nextOpening_gate hm (hpos d' hd') hw'
  have h3 := hmax d' hd' hb'
  rw [ht]
  have : 8 * m * nextOpening d' (R0 / (8 * m)) ≤ 8 * m * nextOpening e (R0 / (8 * m)) := by
    rw [h2, nextOpening_gate hm (hpos e he) hw]; linarith
  exact le_of_mul_le_mul_left this (by positivity)

#print axioms isMove_of_gate

/-- **`sres` at the base `m` is `m · sres8 (x/m)`** [L]: `BlockLanding.sres m x = x − 8m·round(x/(8m))`. -/
theorem sres_eq_mul_sres8 {m x : ℝ} (hm : 0 < m) : BlockLanding.sres m x = m * sres8 (x / m) := by
  unfold BlockLanding.sres sres8
  have : x / m / 8 = x / (8 * m) := by field_simp
  rw [this]
  field_simp

/-- **The case `R0 = 1` is `BlockLanding.nextOpening_bound`** [L]: `nextOpening_gate` at `R0 = 1` is that theorem,
re-expressed with `sres` replaced by `m · dev`. -/
theorem nextOpening_bound_gate {m x : ℝ} (hm : 0 < m) (hx : 0 < x) (hw : InWay x (1 / (8 * m))) :
    8 * m * nextOpening x (1 / (8 * m)) = 1 + (m - BlockLanding.sres m x) / x := by
  have h := nextOpening_gate (R0 := 1) hm hx hw
  rw [h]
  have e1 : dev m 1 x = BlockLanding.sres m x / m := by
    unfold dev
    rw [sres_eq_mul_sres8 hm, mul_one]
    field_simp
  rw [e1]
  field_simp

#print axioms sres_eq_mul_sres8
#print axioms nextOpening_bound_gate

/-! ### The integer special case (TwoScale) -/

/-- The signed residue of an integer is an integer in `[-4, 4]`, and is `0` exactly when `8 ∣` it [L]. -/
theorem sres8_int_zero_iff (n : ℤ) : |sres8 (n : ℝ)| < 1 ↔ (8 : ℤ) ∣ n := by
  constructor
  · intro h
    have e : sres8 (n : ℝ) = ((n - 8 * round ((n : ℝ) / 8) : ℤ) : ℝ) := by
      unfold sres8; push_cast; ring
    rw [e] at h
    have h' : |n - 8 * round ((n : ℝ) / 8)| < 1 := by exact_mod_cast h
    have h0 : n - 8 * round ((n : ℝ) / 8) = 0 := by
      have := abs_lt.mp h'
      omega
    exact ⟨round ((n : ℝ) / 8), by omega⟩
  · rintro ⟨c, rfl⟩
    have : ((8 * c : ℤ) : ℝ) / 8 = (c : ℝ) := by push_cast; ring
    unfold sres8
    rw [this, round_intCast]
    push_cast
    simp

theorem blocked_integer_iff {d a : ℤ} (ha : a % 2 = 1) :
    |dev 1 (a : ℝ) (d : ℝ)| < 1 ↔ (8 : ℤ) ∣ d := by
  have e : dev 1 (a : ℝ) (d : ℝ) = sres8 ((d * a : ℤ) : ℝ) := by
    unfold dev; push_cast; simp
  rw [e, sres8_int_zero_iff]
  constructor
  · intro h
    have h8 : (8 : ℤ) ∣ d * a := h
    have hc : IsCoprime (8 : ℤ) a := by
      obtain ⟨b, hb⟩ : Odd a := Int.odd_iff.mpr ha
      have h2 : IsCoprime (2 : ℤ) a := ⟨-b, 1, by rw [hb]; ring⟩
      simpa using h2.pow_left (m := 3)
    exact hc.dvd_of_dvd_mul_right h8
  · intro h
    exact Dvd.dvd.mul_right h a

#print axioms sres8_int_zero_iff
#print axioms blocked_integer_iff

/-- **A runner with `δ = 0` reads the shift alone** [L]: if `ρ R0 = 8 z` then
`distInt (ρ (R0 + ε)/8) = distInt (ρ ε/8)`.  With `ρ = 8c` this is `distInt (c ε)`, the sub-instance of TwoScale
(`TwoScale.multiple_window`).  TwoScale's multiples of 8 at an odd integer base point are exactly the `δ = 0` runners
(`blocked_integer_iff`); for general real `ρ` the blocked runners are those with `|δ| < 1`, whose offset `δ` need not
vanish, and they read `(δ + ρ ε)/8`: the sub-instance with an offset. -/
theorem delta_zero_shift {ρ R0 ε : ℝ} {z : ℤ} (h : ρ * R0 = 8 * (z : ℝ)) :
    distInt (ρ * (R0 + ε) / 8) = distInt (ρ * ε / 8) := by
  have := TwoScale.reading_shift_real ρ R0 ε 0 z (by simpa using h)
  simpa using this

#print axioms delta_zero_shift

/-! ## (2) The non-generic locus -/

/-- The ratio form of a touch: `x/y = (8k+1)/(8k'+7)` with `k, k'` natural numbers, written without division. -/
-- STANDING: DEFINITION
def RatioForm (x y : ℝ) : Prop := ∃ k k' : ℕ, x * (8 * (k' : ℝ) + 7) = y * (8 * (k : ℝ) + 1)

/-- **A set of disparities is generic** if no ordered pair of its elements has a ratio of the form
`(8k+1)/(8k'+7)` with `k, k'` natural numbers. -/
-- STANDING: DEFINITION
def Generic (ds : Finset ℝ) : Prop := ∀ x ∈ ds, ∀ y ∈ ds, ¬ RatioForm x y

/-- **A touch forces the ratio form** [L]: if an opening of `x` and an entry of `y` occur at one positive instant `t`
(`x t = k + 1/8`, `y t = k' + 7/8`), then `x (8k'+7) = y (8k+1)` with `k, k'` natural numbers.  Positivity of `x, y, t`
is the only hypothesis. -/
theorem touch_ratio {x y t : ℝ} (hx : 0 < x) (hy : 0 < y) (ht : 0 < t)
    (h1 : ZeroMargin.IsOpener (x * t)) (h2 : ZeroMargin.IsEntry (y * t)) : RatioForm x y := by
  obtain ⟨k, hk⟩ := h1
  obtain ⟨k', hk'⟩ := h2
  have hxt : 0 < x * t := by positivity
  have hyt : 0 < y * t := by positivity
  have hk0 : 0 ≤ k := by
    have : (-1 : ℝ) < k := by rw [hk] at hxt; linarith
    have : (-1 : ℤ) < k := by exact_mod_cast this
    omega
  have hk0' : 0 ≤ k' := by
    have : (-1 : ℝ) < k' := by rw [hk'] at hyt; linarith
    have : (-1 : ℤ) < k' := by exact_mod_cast this
    omega
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
  obtain ⟨n', rfl⟩ := Int.eq_ofNat_of_zero_le hk0'
  refine ⟨n, n', ?_⟩
  push_cast at hk hk'
  have e : x * (y * t) = y * (x * t) := by ring
  rw [hk, hk'] at e
  linarith

/-- **The converse** [L]: the ratio form gives a common instant, `t = (8k+1)/(8x)`, at which `x` is at an opening and
`y` at an entry. -/
theorem touch_of_ratio {x y : ℝ} (hx : 0 < x) (h : RatioForm x y) :
    ∃ t : ℝ, 0 < t ∧ ZeroMargin.IsOpener (x * t) ∧ ZeroMargin.IsEntry (y * t) := by
  obtain ⟨k, k', h⟩ := h
  have hk : (0 : ℝ) < 8 * (k : ℝ) + 1 := by positivity
  refine ⟨(8 * (k : ℝ) + 1) / (8 * x), by positivity, ⟨k, ?_⟩, ⟨k', ?_⟩⟩
  · push_cast
    field_simp
  · push_cast
    field_simp
    linarith

#print axioms touch_ratio
#print axioms touch_of_ratio

/-- **A tie forces its own ratio form** [L]: two openings at one positive instant (`x t = k + 1/8`, `y t = k' + 1/8`) give
`x (8k'+1) = y (8k+1)` with `k, k'` natural numbers.  Ties are not excluded by `Generic` (they do not narrow a cell:
a tie of two openers is the left end of a cell, `LonelyCells.cell_left_end_is_opening`); they are the same kind of
coincidence, a rational ratio of a stated shape, and are absent when the ratio is irrational. -/
theorem tie_ratio {x y t : ℝ} (hx : 0 < x) (hy : 0 < y) (ht : 0 < t)
    (h1 : ZeroMargin.IsOpener (x * t)) (h2 : ZeroMargin.IsOpener (y * t)) :
    ∃ k k' : ℕ, x * (8 * (k' : ℝ) + 1) = y * (8 * (k : ℝ) + 1) := by
  obtain ⟨k, hk⟩ := h1
  obtain ⟨k', hk'⟩ := h2
  have hxt : 0 < x * t := by positivity
  have hyt : 0 < y * t := by positivity
  have hk0 : 0 ≤ k := by
    have : (-1 : ℝ) < k := by rw [hk] at hxt; linarith
    have : (-1 : ℤ) < k := by exact_mod_cast this
    omega
  have hk0' : 0 ≤ k' := by
    have : (-1 : ℝ) < k' := by rw [hk'] at hyt; linarith
    have : (-1 : ℤ) < k' := by exact_mod_cast this
    omega
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
  obtain ⟨n', rfl⟩ := Int.eq_ofNat_of_zero_le hk0'
  refine ⟨n, n', ?_⟩
  push_cast at hk hk'
  have e : x * (y * t) = y * (x * t) := by ring
  rw [hk, hk'] at e
  linarith

#print axioms tie_ratio

/-- **An irrational ratio is never of the ratio form** [L]: if `x/y` is irrational, no opening of `x` equals an entry
of `y` (indeed `x/y` would equal the rational `(8k+1)/(8k'+7)`). -/
theorem irrational_not_ratioForm {x y : ℝ} (hxy : Irrational (x / y)) : ¬ RatioForm x y := by
  rintro ⟨k, k', h⟩
  by_cases hy : y = 0
  · subst hy
    exact hxy ⟨0, by simp⟩
  · apply hxy
    refine ⟨((8 * (k : ℚ) + 1) / (8 * (k' : ℚ) + 7)), ?_⟩
    have hq : (8 * (k' : ℝ) + 7) ≠ 0 := by positivity
    push_cast
    field_simp
    linarith

/-- A positive disparity is never of the ratio form with itself [L]: `8k'+7 ≠ 8k+1`. -/
theorem not_ratioForm_self {x : ℝ} (hx : 0 < x) : ¬ RatioForm x x := by
  rintro ⟨k, k', h⟩
  have h2 : (8 * (k' : ℝ) + 7) = 8 * (k : ℝ) + 1 := mul_left_cancel₀ hx.ne' h
  have h3 : 8 * k' + 7 = 8 * k + 1 := by exact_mod_cast h2
  omega

/-- Hence a set of positive disparities in which every pair of distinct elements has an irrational ratio is generic
[L]. -/
theorem generic_of_irrational {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d)
    (h : ∀ x ∈ ds, ∀ y ∈ ds, x ≠ y → Irrational (x / y)) : Generic ds := by
  intro x hx y hy hr
  by_cases hxy : x = y
  · subst hxy
    exact not_ratioForm_self (hpos x hx) hr
  · exact irrational_not_ratioForm (h x hx y hy hxy) hr

#print axioms irrational_not_ratioForm
#print axioms not_ratioForm_self
#print axioms generic_of_irrational

/-- **Every cell of a generic set has positive width** [L]. -/
theorem generic_cell_pos_width {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hg : Generic ds) {u w : ℝ}
    (h : LonelyCells.IsCell ds u w) : u < w := by
  obtain ⟨x, hx, k, y, hy, k', hu, hw, -⟩ := LonelyCells.cell_width hpos h
  rw [LonelyCells.cell_nondegenerate_iff h hu hw]
  intro heq
  apply hg x hx y hy
  refine ⟨k, k', ?_⟩
  have hx0 := hpos x hx
  have hy0 := hpos y hy
  rw [div_eq_div_iff hx0.ne' hy0.ne'] at heq
  nlinarith [heq]

#print axioms generic_cell_pos_width

/-- **The left end of every cell has a runner at exactly `1/8`** [L], generic or not: a lonely instant of zero margin.
So "every lonely instant has positive margin" is false even for generic sets; the true statement is that every cell has
positive width (`generic_cell_pos_width`), hence interior points, which have positive margin. -/
theorem cell_end_zero_margin {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {u w : ℝ} (h : LonelyCells.IsCell ds u w) :
    ∃ x ∈ ds, distInt (x * u) = 1 / 8 := by
  obtain ⟨x, hx, k, -, -, hd, -⟩ := LonelyCells.cell_left_end_is_opening hpos h
  exact ⟨x, hx, hd⟩

/-- **Every lonely instant of a generic set lies in a cell with a lonely point of positive margin** [L]: if `t > 0`
is lonely for a generic `ds`, there is `t' > 0` with every runner strictly clear (`1/8 < distInt (d t')`), namely the
midpoint of the cell containing `t`. -/
theorem generic_margin_point {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hne : ds.Nonempty) (hg : Generic ds) {t : ℝ}
    (ht : 0 < t) (hl : Cascade.LonelyAt ds t) :
    ∃ t' : ℝ, 0 < t' ∧ ∀ d ∈ ds, (1 / 8 : ℝ) < distInt (d * t') := by
  obtain ⟨x, hx, y, hy, hc, -, -⟩ := LonelyCells.cell_of_lonely hpos hne ht hl
  have hlt := generic_cell_pos_width hpos hg hc
  refine ⟨(Localisation.lastOpening x t + LonelyCells.nextEntry y t) / 2, by linarith [hc.1], fun d hd => ?_⟩
  exact Gate.interior_strictly_clear hpos hc.2.2.1 (by linarith) (by linarith) hd

#print axioms cell_end_zero_margin
#print axioms generic_margin_point

/-- **The isolation set is open at every generic parameter** [L].  Let `v` be a path continuous on `[0,1]`, `s₀ ∈ [0,1]`,
and suppose the disparity set of subject `k` at `s₀` is generic and subject `k` is isolated at `s₀`.  Then every `s`
near `s₀` in `[0,1]` is in the isolation set. -/
theorem isoSet_open_at_generic {v : ℝ → Fin 8 → ℝ} (hv : ContinuousOn v (Set.Icc 0 1)) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Set.Icc (0 : ℝ) 1) {k : Fin 8}
    (hg : Generic (Finset.univ.image (PathLaws.absRead (v s₀) k))) (hiso : Isolation (v s₀) k) :
    ∀ᶠ s in 𝓝[Set.Icc 0 1] s₀, s ∈ PathLaws.isoSet v k := by
  obtain ⟨t, ht, hI⟩ := hiso
  have hpos : ∀ d ∈ Finset.univ.image (PathLaws.absRead (v s₀) k), 0 < d := by
    intro d hd
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hd
    have h1 := hI i.1 i.2
    have hne : v s₀ i.1 - v s₀ k ≠ 0 := by
      intro h0
      have : distInt ((v s₀ i.1 - v s₀ k) * t) = 0 := by simp [h0, distInt]
      linarith
    exact abs_pos.mpr hne
  have hne : (Finset.univ.image (PathLaws.absRead (v s₀) k)).Nonempty := by
    obtain ⟨j, hj⟩ := PathLaws.exists_ne k
    exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨j, hj⟩)⟩
  obtain ⟨t', ht', hs⟩ := generic_margin_point hpos hne hg ht ((PathLaws.isolatedAt_iff_lonelyAt _ _ _).mp hI)
  refine PathLaws.isoSet_open_of_strict hv hs₀ ht' (fun i hi => ?_)
  have := hs _ (Finset.mem_image_of_mem _ (Finset.mem_univ ⟨i, hi⟩))
  simp only [PathLaws.absRead] at this
  rwa [Localisation.distInt_abs_mul] at this

#print axioms isoSet_open_at_generic

/-! ### Along an affine path -/

/-- **A ratio value is taken at most once along an affine path (Möbius injectivity)** [L].  For `x s = a₁ + b₁ s`,
`y s = a₂ + b₂ s` with `a₁ b₂ ≠ a₂ b₁` and a value `c`, at most one `s` has `y s ≠ 0` and `x s / y s = c`. -/
theorem moebius_value_subsingleton {a₁ b₁ a₂ b₂ : ℝ} (hdet : a₁ * b₂ ≠ a₂ * b₁) (c : ℝ) :
    Set.Subsingleton {s : ℝ | a₂ + b₂ * s ≠ 0 ∧ (a₁ + b₁ * s) / (a₂ + b₂ * s) = c} := by
  rintro s ⟨hs, hc⟩ s' ⟨hs', hc'⟩
  rw [div_eq_iff hs] at hc
  rw [div_eq_iff hs'] at hc'
  have hcoef : b₁ - c * b₂ ≠ 0 := by
    intro h0
    apply hdet
    have h1 : b₁ = c * b₂ := by linarith
    have h2 : a₁ = c * a₂ := by
      have : (b₁ - c * b₂) * s = c * a₂ - a₁ := by nlinarith [hc]
      rw [h0] at this
      linarith
    rw [h1, h2]; ring
  have e1 : (b₁ - c * b₂) * s = c * a₂ - a₁ := by nlinarith [hc]
  have e2 : (b₁ - c * b₂) * s' = c * a₂ - a₁ := by nlinarith [hc']
  exact mul_left_cancel₀ hcoef (e1.trans e2.symm)

/-- **The pair equation `x (8k'+7) = y (8k+1)` has at most one solution `s` along a non-proportional affine pair**
[L]: the form used for the generic condition, with no division. -/
theorem pair_equation_subsingleton {a₁ b₁ a₂ b₂ : ℝ} (hdet : a₁ * b₂ ≠ a₂ * b₁) (p q : ℝ) (hq : q ≠ 0) :
    Set.Subsingleton {s : ℝ | (a₁ + b₁ * s) * q = (a₂ + b₂ * s) * p} := by
  rintro s hs s' hs'
  simp only [Set.mem_setOf_eq] at hs hs'
  have hcoef : b₁ * q - b₂ * p ≠ 0 := by
    intro h0
    apply hdet
    have e : (b₁ * q - b₂ * p) * s = a₂ * p - a₁ * q := by nlinarith [hs]
    rw [h0] at e
    have h2 : a₂ * p = a₁ * q := by linarith
    have h1 : b₁ * q = b₂ * p := by linarith
    apply mul_right_cancel₀ hq
    calc a₁ * b₂ * q = a₁ * q * b₂ := by ring
      _ = a₂ * p * b₂ := by rw [h2]
      _ = a₂ * (b₂ * p) := by ring
      _ = a₂ * (b₁ * q) := by rw [h1]
      _ = a₂ * b₁ * q := by ring
  have e1 : (b₁ * q - b₂ * p) * s = a₂ * p - a₁ * q := by nlinarith [hs]
  have e2 : (b₁ * q - b₂ * p) * s' = a₂ * p - a₁ * q := by nlinarith [hs']
  exact mul_left_cancel₀ hcoef (e1.trans e2.symm)

/-- **The dichotomy for a pair along an affine path** [L]: either the pair is proportional (`a₁ b₂ = a₂ b₁`) and then
the ratio `x s / y s` is the same at every parameter where it is defined, so the pair is either ratio-form at all
parameters or at none; or it is not proportional and every ratio value is taken at most once. -/
theorem pair_ratio_dichotomy (a₁ b₁ a₂ b₂ : ℝ) :
    (a₁ * b₂ = a₂ * b₁ ∧ ∀ s s' : ℝ, a₂ + b₂ * s ≠ 0 → a₂ + b₂ * s' ≠ 0 →
        (a₁ + b₁ * s) / (a₂ + b₂ * s) = (a₁ + b₁ * s') / (a₂ + b₂ * s')) ∨
    (a₁ * b₂ ≠ a₂ * b₁ ∧ ∀ c : ℝ, Set.Subsingleton {s : ℝ | a₂ + b₂ * s ≠ 0 ∧ (a₁ + b₁ * s) / (a₂ + b₂ * s) = c}) := by
  by_cases h : a₁ * b₂ = a₂ * b₁
  · left
    refine ⟨h, fun s s' hs hs' => ?_⟩
    rw [div_eq_div_iff hs hs']
    have : (a₁ + b₁ * s) * (a₂ + b₂ * s') - (a₁ + b₁ * s') * (a₂ + b₂ * s) = (a₁ * b₂ - a₂ * b₁) * (s' - s) := by
      ring
    rw [h, sub_self, zero_mul] at this
    linarith
  · right
    exact ⟨h, moebius_value_subsingleton h⟩

/-- **The non-generic parameters of an affine path are countable** [L].  Let `d i s = a i + b i s` be the disparities
along the path (each positive on the set considered; a runner whose difference from the subject is negative has
`(a, b)` negated, which keeps the hypothesis), with every pair non-proportional.  Then the set of parameters `s` at
which some pair `(i, j)` has the ratio form for some `k, k'` is countable. -/
theorem nongeneric_params_countable {ι : Type*} [Finite ι] (a b : ι → ℝ)
    (hdet : ∀ i j, i ≠ j → a i * b j ≠ a j * b i) :
    Set.Countable {s : ℝ | (∀ i, 0 < a i + b i * s) ∧
      ∃ i j : ι, ∃ k k' : ℕ, (a i + b i * s) * (8 * (k' : ℝ) + 7) = (a j + b j * s) * (8 * (k : ℝ) + 1)} := by
  have hsub : {s : ℝ | (∀ i, 0 < a i + b i * s) ∧
      ∃ i j : ι, ∃ k k' : ℕ, (a i + b i * s) * (8 * (k' : ℝ) + 7) = (a j + b j * s) * (8 * (k : ℝ) + 1)} ⊆
      ⋃ (i : ι) (j : ι) (k : ℕ) (k' : ℕ), {s : ℝ | i ≠ j ∧
        (a i + b i * s) * (8 * (k' : ℝ) + 7) = (a j + b j * s) * (8 * (k : ℝ) + 1)} := by
    rintro s ⟨hpos, i, j, k, k', h⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨i, j, k, k', ?_, h⟩
    rintro rfl
    exact not_ratioForm_self (hpos i) ⟨k, k', h⟩
  refine Set.Countable.mono hsub ?_
  refine Set.countable_iUnion (fun i => Set.countable_iUnion (fun j => Set.countable_iUnion
    (fun k => Set.countable_iUnion (fun k' => ?_))))
  by_cases hij : i = j
  · have : {s : ℝ | i ≠ j ∧ (a i + b i * s) * (8 * (k' : ℝ) + 7) = (a j + b j * s) * (8 * (k : ℝ) + 1)} = ∅ := by
      ext s; simp [hij]
    rw [this]; exact Set.countable_empty
  · refine Set.Subsingleton.countable ?_
    have := pair_equation_subsingleton (hdet i j hij) (8 * (k : ℝ) + 1) (8 * (k' : ℝ) + 7) (by positivity)
    intro s hs s' hs'
    exact this hs.2 hs'.2

#print axioms moebius_value_subsingleton
#print axioms pair_equation_subsingleton
#print axioms pair_ratio_dichotomy
#print axioms nongeneric_params_countable

/-! ### What the openness at generic parameters does and does not give

`isoSet_open_at_generic` is a statement at one parameter `s₀` where isolation holds and the disparities are generic: the
isolation set contains a neighbourhood of `s₀` in `[0,1]`.  `nongeneric_params_countable` says the parameters excluded
by genericity form a countable set along an affine path with no proportional pair.  Neither statement bears on closedness
of the isolation set.  Closedness asks, for a sequence `s_n → s₀` of parameters with lonely instants `t_n`, whether `s₀`
has one; `PathLaws.isoSet_dichotomy` gives the alternative "`t_n → ∞` or `s₀` is in the set" and nothing here touches the
first branch: genericity at `s₀` is a hypothesis about `s₀` and its own cells, while the escaping instants `t_n` are
instants of the nearby parameters, which may be non-generic or generic alike.  The example `PathLaws.escapeEx_escape`
is a path on which every `s_n` is isolated at `t_n → ∞` and the limit is not (there the limit is not an arrangement).
[reasoned]; no Lean statement is offered for it beyond the dichotomy already in `PathLaws`.
-/

end Fresh.RealCase
