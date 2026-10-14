import Mathlib
import Fresh.Grid

/-!
# Boundaries of a lonely cell, totients and units mod 8 (Task AL)

Written 2026-10-09.  Imports Mathlib and `Fresh.Grid` only (for `distInt_int_div_eight`, `distInt_add_int`,
`distInt_intCast`).  Nothing is imported from the existing `LonelyRunner` repo.  The data that suggested these
statements is in `experiments/n8/totient_boundaries_v1.py` and `.out` (exact integer arithmetic).

Scope.  Disparities here are INTEGERS (a commensurable population: test cases, not a reduction).  Where a statement
needs that, it says so.  No density, coverage, cap, move budget or clock appears; no grand return or half period is
used inside an argument (the instant `1/2` appears only as the object of `half_lonely_iff_odd`).

Contents.
* `distInt_neg`, `distInt_int_sub`, `lonely_mirror`: the lonely test is symmetric under `t ↦ 1 - t` for integer
  disparities (provenance: `GrandReturnN.lonely_mirror` in the existing repo; re-derived, not copied).
* `half_lonely_iff_odd`, `finset_half_lonely_iff`: `1/2` is lonely iff every disparity is odd.
* `half_nbhd_lonely`: for an odd disparity `d` the instants `1/2 + ε`, `|ε| ≤ 3/(8 d)`, are clear; with
  `d_max` the largest, this is the central cell (exact endpoints `1/2 ± 3/(8 d_max)` by a hand argument, reported).
* `unit_lonely`: if `8 ∤ d` and `a` is odd, `t = a/8` is clear (the individual form of the φ(8) law, v9 section 2).
* `blocked_between`: for an integer disparity `d ≥ 4` every open interval `(j/8, (j+2)/8)`, `j` odd, contains an
  instant at which `d` is exactly on a lap line.
* `four_cells`: for a finite set of integers with no multiple of 8 and some element `≥ 4`, the four instants
  `a/8` (`a = 1,3,5,7`) are lonely and are separated from each other by non-lonely instants, so lie in four distinct
  cells.  `exists_ge_four`: seven distinct positive integers contain an element `≥ 4`.
* `opener_unit`, `entry_unit`, `touch_units`: at a reduced rational instant `t = p/q`, a runner `x` standing exactly
  1/8 past a lap line has `8x = q c` with `c p = 8k + 1`, `p` odd, `8 ∣ q`, and `c ≡ p (mod 8)`; a runner standing
  1/8 before a lap line has `c' p = 8k' + 7` and `c' ≡ -p (mod 8)`; hence at a touch point the two cofactors sum to
  `0 (mod 8)` (the units 1 and 7 attached to the instant are inverse and negative: units mod 8 are self-inverse).
* `mirror_opening`: the mirror of an opening at lap `k` of `x` is an entry at lap `x - 1 - k` of `x`.
* `width_congruence`: the width of a cell with opener `(x,k)` and entry `(y,k')` is `m/(8xy)` with
  `m ≡ -(x+y) (mod 8)`.

Counting tool: none is used.  Every claim is graded in the report; the data-only claims are not in this file.
-/

open Classical

namespace Fresh

namespace Boundaries

/-! ## Symmetry of the lonely test -/

theorem distInt_neg (x : ℝ) : distInt (-x) = distInt x := by
  have key : ∀ y : ℝ, distInt (-y) ≤ distInt y := by
    intro y
    unfold distInt
    have h : |(-y) - (round (-y) : ℝ)| ≤ |(-y) - ((-(round y) : ℤ) : ℝ)| := by
      have := round_le (-y) (-(round y))
      simpa [distInt] using this
    have e : |(-y) - ((-(round y) : ℤ) : ℝ)| = |y - (round y : ℝ)| := by
      push_cast
      rw [show -y - -(round y : ℝ) = -(y - round y) by ring, abs_neg]
    exact e ▸ h
  exact le_antisymm (key x) (by simpa using key (-x))

#print axioms distInt_neg

/-- Reflection about an integer. -/
theorem distInt_int_sub (n : ℤ) (x : ℝ) : distInt ((n : ℝ) - x) = distInt x := by
  have : (n : ℝ) - x = -x + n := by ring
  rw [this, distInt_add_int, distInt_neg]

#print axioms distInt_int_sub

/-- `t ↦ 1 - t` preserves the lonely test of an integer disparity (so the lonely set is mirror symmetric). -/
theorem lonely_mirror (d : ℤ) (t : ℝ) :
    (1 / 8 : ℝ) ≤ distInt ((d : ℝ) * (1 - t)) ↔ (1 / 8 : ℝ) ≤ distInt ((d : ℝ) * t) := by
  have : (d : ℝ) * (1 - t) = (d : ℝ) - (d : ℝ) * t := by ring
  rw [this, distInt_int_sub]

#print axioms lonely_mirror

/-! ## The instant 1/2 -/

theorem half_lonely_iff_odd (d : ℤ) :
    (1 / 8 : ℝ) ≤ distInt ((d : ℝ) * (1 / 2)) ↔ Odd d := by
  have e : (d : ℝ) * (1 / 2) = ((4 * d : ℤ) : ℝ) / 8 := by push_cast; ring
  rw [e]
  constructor
  · intro h
    by_contra hodd
    have hev : Even d := Int.not_odd_iff_even.mp hodd
    obtain ⟨m, hm⟩ := hev
    have h8 : (8 : ℤ) ∣ 4 * d := ⟨m, by omega⟩
    rw [Fresh.distInt_int_div_eight_of_dvd h8] at h
    norm_num at h
  · intro hodd
    apply Fresh.distInt_int_div_eight
    obtain ⟨m, hm⟩ := hodd
    omega

#print axioms half_lonely_iff_odd

theorem finset_half_lonely_iff (D : Finset ℤ) :
    (∀ d ∈ D, (1 / 8 : ℝ) ≤ distInt ((d : ℝ) * (1 / 2))) ↔ ∀ d ∈ D, Odd d :=
  forall₂_congr fun d _ => half_lonely_iff_odd d

#print axioms finset_half_lonely_iff

/-- Near `1/2` an odd disparity reads `1/2 - d|ε|` from the nearest lap: clear while `d |ε| ≤ 3/8`. -/
theorem half_nbhd_lonely (d : ℤ) (hd : Odd d) (ε : ℝ) (hε : |ε| * |(d : ℝ)| ≤ 3 / 8) :
    (1 / 8 : ℝ) ≤ distInt ((d : ℝ) * (1 / 2 + ε)) := by
  obtain ⟨m, hm⟩ := hd
  have e : (d : ℝ) * (1 / 2 + ε) = (1 / 2 + (d : ℝ) * ε) + (m : ℝ) := by
    rw [hm]; push_cast; ring
  rw [e, distInt_add_int]
  set s : ℝ := (d : ℝ) * ε with hs
  have hs' : |s| ≤ 3 / 8 := by
    rw [hs, abs_mul]; nlinarith [abs_nonneg ε, abs_nonneg (d : ℝ)]
  unfold distInt
  set z : ℤ := round (1 / 2 + s)
  have hz : (1 / 2 : ℝ) ≤ |(1 / 2 : ℝ) - z| := by
    rcases le_or_gt z 0 with h | h
    · have : (z : ℝ) ≤ 0 := by exact_mod_cast h
      rw [abs_of_pos (by linarith)]; linarith
    · have : (1 : ℝ) ≤ z := by exact_mod_cast h
      rw [abs_of_neg (by linarith)]; linarith
  have tri : |(1 / 2 : ℝ) - z| ≤ |1 / 2 + s - z| + |s| := by
    have := abs_sub_le (1 / 2 : ℝ) (1 / 2 + s) (z : ℝ)
    have e2 : |(1 / 2 : ℝ) - (1 / 2 + s)| = |s| := by rw [show (1 / 2 : ℝ) - (1 / 2 + s) = -s by ring, abs_neg]
    have e3 : |(1 / 2 : ℝ) + s - z| = |(1 / 2 + s) - z| := rfl
    linarith [abs_sub_comm (1 / 2 : ℝ) (1 / 2 + s)]
  have := abs_le.mp hs'
  linarith [abs_nonneg s, le_abs_self s, neg_abs_le s]

#print axioms half_nbhd_lonely

/-! ## The four instants a/8 and the units -/

/-- Individual form of the φ(8) law: with `8 ∤ d` and `a` odd, the instant `a/8` is clear for `d`. -/
theorem unit_lonely (d a : ℤ) (hd : ¬ (8 : ℤ) ∣ d) (ha : Odd a) :
    (1 / 8 : ℝ) ≤ distInt ((d : ℝ) * ((a : ℝ) / 8)) := by
  have e : (d : ℝ) * ((a : ℝ) / 8) = ((d * a : ℤ) : ℝ) / 8 := by push_cast; ring
  rw [e]
  apply Fresh.distInt_int_div_eight
  intro h8
  have hc : IsCoprime (8 : ℤ) a := by
    obtain ⟨m, hm⟩ := ha
    have h2 : IsCoprime (2 : ℤ) a := ⟨-m, 1, by rw [hm]; ring⟩
    simpa using h2.pow_left (m := 3)
  exact hd (hc.dvd_of_dvd_mul_right h8)

#print axioms unit_lonely

/-- For an integer disparity `d ≥ 4` and odd `j`, some instant strictly between `j/8` and `(j+2)/8` has `d` exactly
on a lap line (so is blocked). -/
theorem blocked_between (d j : ℤ) (hd : 4 ≤ d) (hj : Odd j) :
    ∃ t : ℝ, (j : ℝ) / 8 < t ∧ t < ((j : ℝ) + 2) / 8 ∧ distInt ((d : ℝ) * t) = 0 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : (0 : ℤ) < d)
  by_cases h4 : d = 4
  · subst h4
    obtain ⟨a, ha⟩ := hj
    refine ⟨((a + 1 : ℤ) : ℝ) / 4, ?_, ?_, ?_⟩
    · rw [ha]; push_cast; linarith
    · rw [ha]; push_cast; linarith
    · have : ((4 : ℤ) : ℝ) * (((a + 1 : ℤ) : ℝ) / 4) = ((a + 1 : ℤ) : ℝ) := by push_cast; ring
      rw [this, Fresh.distInt_intCast]
  · have hd5 : 5 ≤ d := by omega
    have hd5r : (5 : ℝ) ≤ d := by exact_mod_cast hd5
    set m : ℤ := ⌊(j : ℝ) * d / 8⌋ + 1 with hm
    have h1 : (j : ℝ) * d / 8 < m := by
      rw [hm]; push_cast; exact Int.lt_floor_add_one _
    have h2 : (m : ℝ) ≤ (j : ℝ) * d / 8 + 1 := by
      rw [hm]; push_cast; linarith [Int.floor_le ((j : ℝ) * d / 8)]
    refine ⟨(m : ℝ) / d, ?_, ?_, ?_⟩
    · rw [div_lt_div_iff₀ (by norm_num) hd0]; nlinarith
    · rw [div_lt_div_iff₀ hd0 (by norm_num)]; nlinarith
    · have : (d : ℝ) * ((m : ℝ) / d) = (m : ℝ) := by field_simp
      rw [this, Fresh.distInt_intCast]

#print axioms blocked_between

/-- Seven (indeed four) distinct positive integers contain one `≥ 4`. -/
theorem exists_ge_four (D : Finset ℤ) (hpos : ∀ d ∈ D, 0 < d) (hc : 4 ≤ D.card) : ∃ d ∈ D, 4 ≤ d := by
  by_contra hno
  push Not at hno
  have hsub : D ⊆ Finset.Icc (1 : ℤ) 3 := by
    intro d hd
    have := hno d hd
    have := hpos d hd
    simp only [Finset.mem_Icc]; omega
  have := Finset.card_le_card hsub
  simp at this
  omega

#print axioms exists_ge_four

/-- **Four cells.**  A finite set of integer disparities with no multiple of 8 and some element `≥ 4`: the instants
`1/8, 3/8, 5/8, 7/8` are all clear, and between consecutive ones some instant is blocked.  Hence the lonely set
(period 1) has at least four cells; this holds for every such set, whatever the gcd. -/
theorem four_cells (D : Finset ℤ) (h8 : ∀ d ∈ D, ¬ (8 : ℤ) ∣ d) (h4 : ∃ d ∈ D, 4 ≤ d) :
    (∀ a : ℤ, Odd a → ∀ d ∈ D, (1 / 8 : ℝ) ≤ distInt ((d : ℝ) * ((a : ℝ) / 8))) ∧
    (∀ j : ℤ, Odd j → ∃ t : ℝ, (j : ℝ) / 8 < t ∧ t < ((j : ℝ) + 2) / 8 ∧
        ∃ d ∈ D, distInt ((d : ℝ) * t) = 0) := by
  refine ⟨fun a ha d hd => unit_lonely d a (h8 d hd) ha, fun j hj => ?_⟩
  obtain ⟨d, hdD, hd4⟩ := h4
  obtain ⟨t, h1, h2, h3⟩ := blocked_between d j hd4 hj
  exact ⟨t, h1, h2, d, hdD, h3⟩

#print axioms four_cells

/-! ## Units attached to a boundary instant (commensurable: the instant is rational `p/q`) -/

/-- In `ZMod 8` the units are their own inverses: `a * b = 1 → a = b`. -/
theorem zmod8_inv_eq : ∀ a b : ZMod 8, a * b = 1 → a = b := by decide

/-- **Opener.**  Let `t = p/q` in lowest terms (`IsCoprime p q`, `q ≠ 0`) and let the integer disparity `x` stand
exactly 1/8 past lap `k` at `t`: `x t = k + 1/8`.  Then `8x = q c` for an integer `c` (the cofactor of `x` at `t`), and
`c p = 8k + 1`, `p` and `c` are odd, `8 ∣ q`, and `c ≡ p (mod 8)`. -/
theorem opener_unit (p q x k : ℤ) (hq : q ≠ 0) (hpq : IsCoprime p q)
    (h : (x : ℝ) * ((p : ℝ) / q) = (k : ℝ) + 1 / 8) :
    ∃ c : ℤ, 8 * x = q * c ∧ c * p = 8 * k + 1 ∧ Odd p ∧ Odd c ∧ (8 : ℤ) ∣ q ∧ (8 : ℤ) ∣ (c - p) := by
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hz : 8 * x * p = q * (8 * k + 1) := by
    have : (8 * x * p : ℝ) = q * (8 * k + 1) := by
      field_simp at h; linarith
    exact_mod_cast this
  have hdvd : q ∣ 8 * x := by
    have : q ∣ (8 * x) * p := ⟨8 * k + 1, hz⟩
    exact hpq.symm.dvd_of_dvd_mul_right this
  obtain ⟨c, hc⟩ := hdvd
  have hcp : c * p = 8 * k + 1 := by
    have : q * (c * p) = q * (8 * k + 1) := by rw [← hz, hc]; ring
    exact mul_left_cancel₀ hq this
  have hodd : Odd (c * p) := ⟨4 * k, by omega⟩
  have hoc : Odd c := (Int.odd_mul.mp hodd).1
  have hop : Odd p := (Int.odd_mul.mp hodd).2
  have hcop : IsCoprime (8 : ℤ) c := by
    obtain ⟨m, hm⟩ := hoc
    have h2 : IsCoprime (2 : ℤ) c := ⟨-m, 1, by rw [hm]; ring⟩
    simpa using h2.pow_left (m := 3)
  have h8q : (8 : ℤ) ∣ q := by
    have : (8 : ℤ) ∣ q * c := ⟨x, by rw [← hc]⟩
    exact hcop.dvd_of_dvd_mul_right this
  refine ⟨c, hc, hcp, hop, hoc, h8q, ?_⟩
  have h1 : ((c : ZMod 8)) * (p : ZMod 8) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod 8) hcp
    push_cast at this
    rw [this]
    have : (8 : ZMod 8) = 0 := by decide
    rw [this]; simp
  have h2 := zmod8_inv_eq _ _ h1
  have h3 : ((c - p : ℤ) : ZMod 8) = 0 := by push_cast; rw [h2]; ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp h3

#print axioms opener_unit

/-- **Entry.**  The same for a runner standing exactly 1/8 before lap `k + 1`: `x t = k + 7/8`.  Then `8x = q c`,
`c p = 8k + 7`, `p` odd, `8 ∣ q`, and `c ≡ -p (mod 8)`. -/
theorem entry_unit (p q x k : ℤ) (hq : q ≠ 0) (hpq : IsCoprime p q)
    (h : (x : ℝ) * ((p : ℝ) / q) = (k : ℝ) + 7 / 8) :
    ∃ c : ℤ, 8 * x = q * c ∧ c * p = 8 * k + 7 ∧ Odd p ∧ Odd c ∧ (8 : ℤ) ∣ q ∧ (8 : ℤ) ∣ (c + p) := by
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hz : 8 * x * p = q * (8 * k + 7) := by
    have : (8 * x * p : ℝ) = q * (8 * k + 7) := by
      field_simp at h; linarith
    exact_mod_cast this
  have hdvd : q ∣ 8 * x := by
    have : q ∣ (8 * x) * p := ⟨8 * k + 7, hz⟩
    exact hpq.symm.dvd_of_dvd_mul_right this
  obtain ⟨c, hc⟩ := hdvd
  have hcp : c * p = 8 * k + 7 := by
    have : q * (c * p) = q * (8 * k + 7) := by rw [← hz, hc]; ring
    exact mul_left_cancel₀ hq this
  have hodd : Odd (c * p) := ⟨4 * k + 3, by omega⟩
  have hoc : Odd c := (Int.odd_mul.mp hodd).1
  have hop : Odd p := (Int.odd_mul.mp hodd).2
  have hcop : IsCoprime (8 : ℤ) c := by
    obtain ⟨m, hm⟩ := hoc
    have h2 : IsCoprime (2 : ℤ) c := ⟨-m, 1, by rw [hm]; ring⟩
    simpa using h2.pow_left (m := 3)
  have h8q : (8 : ℤ) ∣ q := by
    have : (8 : ℤ) ∣ q * c := ⟨x, by rw [← hc]⟩
    exact hcop.dvd_of_dvd_mul_right this
  refine ⟨c, hc, hcp, hop, hoc, h8q, ?_⟩
  have h1 : ((c : ZMod 8)) * ((-p : ℤ) : ZMod 8) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod 8) hcp
    push_cast at this ⊢
    have h8 : (8 : ZMod 8) = 0 := by decide
    have h7 : (7 : ZMod 8) = -1 := by decide
    rw [mul_neg, this, h8, h7]; simp
  have h2 := zmod8_inv_eq _ _ h1
  have h3 : ((c + p : ℤ) : ZMod 8) = 0 := by
    push_cast at h2 ⊢; rw [h2]; ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp h3

#print axioms entry_unit

/-- **Touch.**  If one runner opens and another enters at the same reduced instant `p/q`, their cofactors sum to
`0 (mod 8)`: they carry the units `p` and `-p` (e.g. at the AP instant 3/8: runner 3 with cofactor 3 and runner 5 with
cofactor 5). -/
theorem touch_units (p q x y k k' : ℤ) (hq : q ≠ 0) (hpq : IsCoprime p q)
    (hx : (x : ℝ) * ((p : ℝ) / q) = (k : ℝ) + 1 / 8)
    (hy : (y : ℝ) * ((p : ℝ) / q) = (k' : ℝ) + 7 / 8) :
    ∃ c c' : ℤ, 8 * x = q * c ∧ 8 * y = q * c' ∧ (8 : ℤ) ∣ (c + c') := by
  obtain ⟨c, hc, -, -, -, -, h1⟩ := opener_unit p q x k hq hpq hx
  obtain ⟨c', hc', -, -, -, -, h2⟩ := entry_unit p q y k' hq hpq hy
  refine ⟨c, c', hc, hc', ?_⟩
  have : c + c' = (c - p) + (c' + p) := by ring
  rw [this]; exact dvd_add h1 h2

#print axioms touch_units

/-! ## Mirror and widths -/

/-- Mirror of an opening: if `x t = k + 1/8` then `x (1 - t) = (x - 1 - k) + 7/8`. -/
theorem mirror_opening (x k : ℤ) (t : ℝ) (h : (x : ℝ) * t = (k : ℝ) + 1 / 8) :
    (x : ℝ) * (1 - t) = ((x - 1 - k : ℤ) : ℝ) + 7 / 8 := by
  push_cast; linarith

#print axioms mirror_opening

/-- Width of a cell with opener `(x,k)` at the left end and entry `(y,k')` at the right end is `m/(8xy)` with the
integer `m = (8k'+7) x - (8k+1) y`, and `m ≡ -(x+y) (mod 8)`. -/
theorem width_congruence (x y k k' : ℤ) (hx : 0 < x) (hy : 0 < y) :
    ((8 * k' + 7 : ℝ) / (8 * y) - (8 * k + 1 : ℝ) / (8 * x)
      = (((8 * k' + 7) * x - (8 * k + 1) * y : ℤ) : ℝ) / (8 * x * y)) ∧
    (8 : ℤ) ∣ (((8 * k' + 7) * x - (8 * k + 1) * y) + (x + y)) := by
  constructor
  · have hx' : (x : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
    have hy' : (y : ℝ) ≠ 0 := by exact_mod_cast hy.ne'
    push_cast; field_simp
  · exact ⟨k' * x - k * y + x, by ring⟩

#print axioms width_congruence

end Boundaries

end Fresh
