import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.Dilation
import Fresh.ChainLaws
import Fresh.FiveReach
import Fresh.Ladder5
import Fresh.FourDistinct
import Fresh.LadderScale

/-!
# Five disparities with the second smallest at least `7 d_min` (Task CB)

Written 2026-10-10.  Nothing is imported from the existing `LonelyRunner` repo.  Exact reals only; every disparity is
positive (no runner is stationary); no floats.  Data (exact fractions, explicit grids): `experiments/n8/five_high_v1.py/.out`.

## What is proved here (grades in the docstrings; each [L] theorem is followed by its `#print axioms` line)

Setting: `E` is a set of at most four readings, `a` its least member, the cascade runs from any positive `seq 0`.

* (1) `return_ratio` [L]: if `a` sets at `n` and is in the way again for the first time at `k` then `k = n + 5`, the lap of
  `a` rises by exactly one, the setters in between are `z, p, q, z` with `z` the largest reading of `E`, `3 a < 2 z`, `3 z < 5 a`,
  and `a` is the SETTER at `k` (it is the only reading in the way there).  No lap hypothesis, no ratio hypothesis.
* (2) `second_return_false` [L]: if `a` sets at `n`, is in the way again at its first return `k` (a setting, by (1)) and is in
  the way again at a first return `k2` after `k`, contradiction.  Why: the first window forces `3/2 < z/a < 5/3`; the second window
  starts one lap of `a` later, so `z` stands one more `z/a` along, and `z` is in the way at both starts, which forces
  `z/a` within `1/4` of an integer.
* (3) `four_cascade_fixes_free` [L]: the cascade over at most four readings is fixed within twenty moves, from any positive
  start, for any readings.  This removes `LapCond` from `LadderScale.four_cascade_fixes` (which gave fifteen moves under it).
* (4) `five_disparities_of_high` [L]: five disparities, second smallest `a` with `20 m <= 3 a`: a lonely instant in `R in [1, 7]`;
  `five_disparities_rho57` is the instance `57 m <= a`; `five_disparities_ge5` [L] joins it to `LadderScale.five_disparities_of_ratio`:
  every set of at most five disparities with `5 d_min <= a` has a lonely instant in `R in [1, 7]`.

## Hypotheses (REQUIRED / NOT REQUIRED / UNDECIDED)

See the table at the end of the file.

Provenance (existing declarations whose argument was read and understood, nothing copied): `Ladder5.return_after_four`,
`Ladder5.budget_sum`, `FourDistinct.three_distinct_shape` (re-used as stated, imported), `LadderScale.window_has_setter`,
`LadderScale.lonely_window_of_moves`.  The ratio window `3/2 < z/a < 5/3` and the shift argument are new here.
-/

open Classical

namespace Fresh

namespace FiveHigh

open Cascade Dilation ChainLaws FiveReachStudy Ladder5 FourDistinct LadderScale

/-! ## (1) The first return of the slowest of at most four readings -/

set_option maxHeartbeats 4000000 in
/-- **The first return of the slowest of at most four readings** [L].  `E` has at most four members, `a` is the least; `a` sets
the move at `n` and is in the way again for the first time at `k`.  Then (i) `k = n + 5`; (ii) the lap of `a` at `k` is one
more than at `n`; (iii) `a` is the setter at `k`; (iv) there is a reading `z`, the largest of `E.erase a`, which sets the
moves at `n + 1` and `n + 4`, with `3 a < 2 z` and `3 z < 5 a`.  Hypotheses: `E.card ≤ 4` REQUIRED for this proof (it makes the
setter values of the window at most three, so the shape applies); `a` least REQUIRED (`a_lt_w`); `0 < seq 0` used;
NOT REQUIRED: any base `m`, `seq 0 = 1/(8m)`, any lap or ratio condition on `a`. -/
theorem return_ratio {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) (hcard : E.card ≤ 4) {a : ℝ} (haE : a ∈ E)
    (ha : ∀ d ∈ E, a ≤ d) {n k : ℕ} (hn : IsSetterAt E seq n a) (hnk : n < k) (hw : InWay a (seq k))
    (hfirst : ∀ s, n < s → s < k → ¬ InWay a (seq s)) :
    k = n + 5 ∧ lap a (seq k) = lap a (seq n) + 1 ∧ IsSetterAt E seq k a ∧
      ∃ z : ℝ, IsSetterAt E seq (n + 1) z ∧ IsSetterAt E seq (n + 4) z ∧ 3 * a < 2 * z ∧ 3 * z < 5 * a ∧
        (∀ d ∈ E, d ≠ a → d ≤ z) := by
  have hex : ∀ s, n < s → s < k → ∃ y, IsSetterAt E seq s y := fun s _ h2 => setter_before_visit hmv haE hw h2
  choose! w hws using hex
  have hlt : ∀ s, n < s → s < k → a < w s := fun s h1 h2 => a_lt_w ha hfirst hws h1 h2
  have hcard3 : ((Finset.Ico (n + 1) k).image w).card ≤ 3 := by
    have hsub : (Finset.Ico (n + 1) k).image w ⊆ E.erase a := by
      intro y hy
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
      have hs' := Finset.mem_Ico.mp hs
      exact Finset.mem_erase.mpr ⟨(hlt s (by omega) hs'.2).ne', (hws s (by omega) hs'.2).1⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_erase_of_mem haE
    omega
  obtain ⟨hk5, x, y, z, hax, hxy, hyz, e1, e4, hmid⟩ :=
    three_distinct_shape hpos h0 hmv ha hn hnk hw hfirst hws hcard3
  subst hk5
  have ha0 : 0 < a := hpos a haE
  have hs1 := hws (n + 1) (by omega) (by omega)
  have hs2 := hws (n + 2) (by omega) (by omega)
  have hs3 := hws (n + 3) (by omega) (by omega)
  have hs4 := hws (n + 4) (by omega) (by omega)
  have hap := hlt (n + 2) (by omega) (by omega)
  have haq := hlt (n + 3) (by omega) (by omega)
  rw [e1] at hs1
  rw [e4] at hs4
  set p := w (n + 2) with hp
  set q := w (n + 3) with hq
  have hpz : p < z := by
    rcases hmid with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> linarith
  have hqz : q < z := by
    rcases hmid with ⟨_, h1⟩ | ⟨_, h1⟩ <;> rw [h1] <;> linarith
  have haz : a < z := by linarith
  have hz0 : 0 < z := by linarith
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  -- increments of the four moves
  obtain ⟨d1p, d1⟩ := incr_setter hpos hs1
  obtain ⟨d2p, d2⟩ := incr_setter hpos hs2
  obtain ⟨d3p, d3⟩ := incr_setter hpos hs3
  obtain ⟨d4p, d4⟩ := incr_setter hpos hs4
  -- products: speed times increment is below 1/4
  have m1 : z * (seq (n + 1 + 1) - seq (n + 1)) < 1 / 4 := by
    have := mul_lt_mul_of_pos_left d1 hz0
    have e : z * (1 / (4 * z)) = 1 / 4 := by field_simp
    linarith
  have m2 : p * (seq (n + 2 + 1) - seq (n + 2)) < 1 / 4 := by
    have := mul_lt_mul_of_pos_left d2 hp0
    have e : p * (1 / (4 * p)) = 1 / 4 := by field_simp
    linarith
  have m3 : q * (seq (n + 3 + 1) - seq (n + 3)) < 1 / 4 := by
    have := mul_lt_mul_of_pos_left d3 hq0
    have e : q * (1 / (4 * q)) = 1 / 4 := by field_simp
    linarith
  have m4 : z * (seq (n + 4 + 1) - seq (n + 4)) < 1 / 4 := by
    have := mul_lt_mul_of_pos_left d4 hz0
    have e : z * (1 / (4 * z)) = 1 / 4 := by field_simp
    linarith
  -- landing readings
  have la0 : a * seq (n + 1) = (lap a (seq n) : ℝ) + 1 / 8 := by
    rw [hn.2.2]; exact setter_reading ha0 hn.2.1
  have lz1 : z * seq (n + 1 + 1) = (lap z (seq (n + 1)) : ℝ) + 1 / 8 := by
    rw [hs1.2.2]; exact setter_reading hz0 hs1.2.1
  have lp2 : p * seq (n + 2 + 1) = (lap p (seq (n + 2)) : ℝ) + 1 / 8 := by
    rw [hs2.2.2]; exact setter_reading hp0 hs2.2.1
  have lq3 : q * seq (n + 3 + 1) = (lap q (seq (n + 3)) : ℝ) + 1 / 8 := by
    rw [hs3.2.2]; exact setter_reading hq0 hs3.2.1
  have lz4 : z * seq (n + 4 + 1) = (lap z (seq (n + 4)) : ℝ) + 1 / 8 := by
    rw [hs4.2.2]; exact setter_reading hz0 hs4.2.1
  have wz1 := abs_lt.mp (abs_sub_lap_lt hs1.2.1)
  have wa := abs_lt.mp (abs_sub_lap_lt hw)
  have hlapJ : lap a (seq n) + 1 ≤ lap a (seq (n + 5)) := setter_later_lap hpos h0 hmv hnk hn hw
  have hrec : lap z (seq (n + 1)) < lap z (seq (n + 4)) :=
    setter_recur_lap hpos h0 hmv (show n + 1 < n + 4 by omega) hs1 hs4
  -- the four increments times `a` are each below 1/4 (every setter is at least `a`)
  have a1 : a * (seq (n + 1 + 1) - seq (n + 1)) < 1 / 4 := by
    have : a * (seq (n + 1 + 1) - seq (n + 1)) ≤ z * (seq (n + 1 + 1) - seq (n + 1)) :=
      mul_le_mul_of_nonneg_right haz.le d1p.le
    linarith
  have a2 : a * (seq (n + 2 + 1) - seq (n + 2)) < 1 / 4 := by
    have : a * (seq (n + 2 + 1) - seq (n + 2)) ≤ p * (seq (n + 2 + 1) - seq (n + 2)) :=
      mul_le_mul_of_nonneg_right hap.le d2p.le
    linarith
  have a3 : a * (seq (n + 3 + 1) - seq (n + 3)) < 1 / 4 := by
    have : a * (seq (n + 3 + 1) - seq (n + 3)) ≤ q * (seq (n + 3 + 1) - seq (n + 3)) :=
      mul_le_mul_of_nonneg_right haq.le d3p.le
    linarith
  have a4 : a * (seq (n + 4 + 1) - seq (n + 4)) < 1 / 4 := by
    have : a * (seq (n + 4 + 1) - seq (n + 4)) ≤ z * (seq (n + 4 + 1) - seq (n + 4)) :=
      mul_le_mul_of_nonneg_right haz.le d4p.le
    linarith
  -- (ii) the lap of `a` at the return
  have hJle : lap a (seq (n + 5)) ≤ lap a (seq n) + 1 := by
    have hupper : a * seq (n + 5) < (lap a (seq n) : ℝ) + 1 / 8 + 1 := by
      have e : a * seq (n + 5) = a * seq (n + 1) + a * (seq (n + 1 + 1) - seq (n + 1)) +
          a * (seq (n + 2 + 1) - seq (n + 2)) + a * (seq (n + 3 + 1) - seq (n + 3)) +
          a * (seq (n + 4 + 1) - seq (n + 4)) := by ring_nf
      linarith
    have : ((lap a (seq (n + 5)) : ℤ) : ℝ) < (lap a (seq n) : ℝ) + 2 := by linarith [wa.1]
    have h2 : (lap a (seq (n + 5)) : ℤ) < lap a (seq n) + 2 := by exact_mod_cast this
    omega
  have hJ : lap a (seq (n + 5)) = lap a (seq n) + 1 := le_antisymm hJle hlapJ
  have hJR : ((lap a (seq (n + 5)) : ℤ) : ℝ) = (lap a (seq n) : ℝ) + 1 := by exact_mod_cast hJ
  -- the elapsed time `Δ = seq (n+5) - seq (n+1)`: `a Δ > 3/4`
  have hsum : seq (n + 5) - seq (n + 1) = (seq (n + 1 + 1) - seq (n + 1)) + (seq (n + 2 + 1) - seq (n + 2)) +
      (seq (n + 3 + 1) - seq (n + 3)) + (seq (n + 4 + 1) - seq (n + 4)) := by ring_nf
  have haD : 3 / 4 < a * (seq (n + 5) - seq (n + 1)) := by
    have : a * (seq (n + 5) - seq (n + 1)) = a * seq (n + 5) - a * seq (n + 1) := by ring
    linarith [wa.1]
  -- z < 2 a
  have hz2 : z < 2 * a := by
    by_contra hcon
    push Not at hcon
    have b1 : 2 * a * (seq (n + 1 + 1) - seq (n + 1)) ≤ z * (seq (n + 1 + 1) - seq (n + 1)) :=
      mul_le_mul_of_nonneg_right hcon d1p.le
    have b4 : 2 * a * (seq (n + 4 + 1) - seq (n + 4)) ≤ z * (seq (n + 4 + 1) - seq (n + 4)) :=
      mul_le_mul_of_nonneg_right hcon d4p.le
    have e : a * (seq (n + 5) - seq (n + 1)) = a * (seq (n + 1 + 1) - seq (n + 1)) +
        a * (seq (n + 2 + 1) - seq (n + 2)) + a * (seq (n + 3 + 1) - seq (n + 3)) +
        a * (seq (n + 4 + 1) - seq (n + 4)) := by rw [hsum]; ring
    linarith
  -- A' - A = 1
  have hAA : lap z (seq (n + 4)) = lap z (seq (n + 1)) + 1 := by
    have e : z * (seq (n + 4 + 1) - seq (n + 2)) = (lap z (seq (n + 4)) : ℝ) - (lap z (seq (n + 1)) : ℝ) := by
      have : z * (seq (n + 4 + 1) - seq (n + 1 + 1)) = z * seq (n + 4 + 1) - z * seq (n + 1 + 1) := by ring
      linarith
    have s2 : z * (seq (n + 2 + 1) - seq (n + 2)) < 1 / 2 := by
      have h1 : z * (seq (n + 2 + 1) - seq (n + 2)) ≤ 2 * p * (seq (n + 2 + 1) - seq (n + 2)) :=
        mul_le_mul_of_nonneg_right (by linarith) d2p.le
      linarith
    have s3 : z * (seq (n + 3 + 1) - seq (n + 3)) < 1 / 2 := by
      have h1 : z * (seq (n + 3 + 1) - seq (n + 3)) ≤ 2 * q * (seq (n + 3 + 1) - seq (n + 3)) :=
        mul_le_mul_of_nonneg_right (by linarith) d3p.le
      linarith
    have e2 : z * (seq (n + 4 + 1) - seq (n + 2)) = z * (seq (n + 2 + 1) - seq (n + 2)) +
        z * (seq (n + 3 + 1) - seq (n + 3)) + z * (seq (n + 4 + 1) - seq (n + 4)) := by ring_nf
    have hlt5 : ((lap z (seq (n + 4)) : ℤ) : ℝ) - (lap z (seq (n + 1)) : ℝ) < 2 := by linarith
    have h5 : lap z (seq (n + 4)) - lap z (seq (n + 1)) < 2 := by exact_mod_cast hlt5
    omega
  have hAAR : ((lap z (seq (n + 4)) : ℤ) : ℝ) = (lap z (seq (n + 1)) : ℝ) + 1 := by exact_mod_cast hAA
  -- the ratio `ζ = z / a`
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℝ, z = ζ * a := ⟨z / a, by field_simp⟩
  have hζ0 : 0 < ζ := by
    by_contra hcon
    push Not at hcon
    have : ζ * a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon ha0.le
    linarith
  have hζ32 : (3 : ℝ) / 2 < ζ := by
    -- 1 = z (seq(n+5) - seq(n+2)) < ζ/4 + ζ/4 + 1/4
    have e : z * (seq (n + 4 + 1) - seq (n + 2)) = 1 := by
      have : z * (seq (n + 4 + 1) - seq (n + 1 + 1)) = z * seq (n + 4 + 1) - z * seq (n + 1 + 1) := by ring
      linarith
    have e2 : z * (seq (n + 4 + 1) - seq (n + 2)) = z * (seq (n + 2 + 1) - seq (n + 2)) +
        z * (seq (n + 3 + 1) - seq (n + 3)) + z * (seq (n + 4 + 1) - seq (n + 4)) := by ring_nf
    have z2 : z * (seq (n + 2 + 1) - seq (n + 2)) < ζ / 4 := by
      have : z * (seq (n + 2 + 1) - seq (n + 2)) = ζ * (a * (seq (n + 2 + 1) - seq (n + 2))) := by rw [hζ]; ring
      rw [this]
      have := mul_lt_mul_of_pos_left a2 hζ0
      linarith
    have z3 : z * (seq (n + 3 + 1) - seq (n + 3)) < ζ / 4 := by
      have : z * (seq (n + 3 + 1) - seq (n + 3)) = ζ * (a * (seq (n + 3 + 1) - seq (n + 3))) := by rw [hζ]; ring
      rw [this]
      have := mul_lt_mul_of_pos_left a3 hζ0
      linarith
    linarith
  have hlow : 3 * a < 2 * z := by
    have := mul_lt_mul_of_pos_right hζ32 ha0
    rw [hζ]; linarith
  have hζ53 : ζ < 5 / 3 := by
    -- z Δ = (A' + 1/8) - z seq(n+1) < 5/4, and a Δ > 3/4
    have e : z * (seq (n + 5) - seq (n + 1)) < 5 / 4 := by
      have : z * (seq (n + 5) - seq (n + 1)) = z * seq (n + 4 + 1) - z * seq (n + 1) := by ring
      linarith [wz1.1]
    have e2 : z * (seq (n + 5) - seq (n + 1)) = ζ * (a * (seq (n + 5) - seq (n + 1))) := by rw [hζ]; ring
    have := mul_lt_mul_of_pos_left haD hζ0
    linarith
  have hup : 3 * z < 5 * a := by
    have := mul_lt_mul_of_pos_right hζ53 ha0
    rw [hζ]; linarith
  -- the largest reading, and the only reading in the way at `seq (n+5)`
  have hxy' : (p = x ∧ q = y) ∨ (p = y ∧ q = x) := hmid
  have hxE : x ∈ E := by
    rcases hxy' with ⟨h1, _⟩ | ⟨_, h1⟩
    · rw [← h1]; exact hs2.1
    · rw [← h1]; exact hs3.1
  have hyE : y ∈ E := by
    rcases hxy' with ⟨_, h1⟩ | ⟨h1, _⟩
    · rw [← h1]; exact hs3.1
    · rw [← h1]; exact hs2.1
  have hzE : z ∈ E := hs1.1
  have hsub : ({x, y, z} : Finset ℝ) ⊆ E.erase a := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact Finset.mem_erase.mpr ⟨by linarith, hxE⟩
    · exact Finset.mem_erase.mpr ⟨by linarith, hyE⟩
    · exact Finset.mem_erase.mpr ⟨by linarith, hzE⟩
  have hc3 : ({x, y, z} : Finset ℝ).card = 3 :=
    Finset.card_eq_three.mpr ⟨x, y, z, ne_of_lt hxy, ne_of_lt (hxy.trans hyz), ne_of_lt hyz, rfl⟩
  have hc : (E.erase a).card ≤ ({x, y, z} : Finset ℝ).card := by
    have := Finset.card_erase_of_mem haE
    omega
  have hEq : ({x, y, z} : Finset ℝ) = E.erase a := Finset.eq_of_subset_of_card_le hsub hc
  have hmem : ∀ d ∈ E, d ≠ a → d = x ∨ d = y ∨ d = z := by
    intro d hdE hda
    have : d ∈ E.erase a := Finset.mem_erase.mpr ⟨hda, hdE⟩
    rw [← hEq] at this
    simpa using this
  have hmax : ∀ d ∈ E, d ≠ a → d ≤ z := by
    intro d hdE hda
    rcases hmem d hdE hda with h | h | h <;> rw [h] <;> linarith
  -- the readings other than `a` are clear at `seq (n+5)`
  have hz_clear : ¬ InWay z (seq (n + 5)) := by
    refine not_inWay_of_between (lap z (seq (n + 4))) ?_ ?_
    · show (lap z (seq (n + 4)) : ℝ) + 1 / 8 ≤ z * seq (n + 5)
      linarith [lz4]
    · show z * seq (n + 5) ≤ (lap z (seq (n + 4)) : ℝ) + 7 / 8
      linarith [lz4]
  have hq_clear : ¬ InWay q (seq (n + 5)) := by
    refine not_inWay_of_between (lap q (seq (n + 3))) ?_ ?_
    · show (lap q (seq (n + 3)) : ℝ) + 1 / 8 ≤ q * seq (n + 5)
      have : q * seq (n + 5) = q * seq (n + 3 + 1) + q * (seq (n + 4 + 1) - seq (n + 4)) := by ring_nf
      have h1 : 0 ≤ q * (seq (n + 4 + 1) - seq (n + 4)) := mul_nonneg hq0.le d4p.le
      linarith [lq3]
    · show q * seq (n + 5) ≤ (lap q (seq (n + 3)) : ℝ) + 7 / 8
      have : q * seq (n + 5) = q * seq (n + 3 + 1) + q * (seq (n + 4 + 1) - seq (n + 4)) := by ring_nf
      have h1 : q * (seq (n + 4 + 1) - seq (n + 4)) ≤ z * (seq (n + 4 + 1) - seq (n + 4)) :=
        mul_le_mul_of_nonneg_right hqz.le d4p.le
      linarith [lq3]
  have hp_clear : ¬ InWay p (seq (n + 5)) := by
    -- p (seq(n+5) - seq(n+3)) < (z/a)/4 + 1/4 < 2/3
    have hpa : p < ζ * a := by rw [← hζ]; exact hpz
    have e : p * seq (n + 5) = p * seq (n + 2 + 1) + p * (seq (n + 3 + 1) - seq (n + 3)) +
        p * (seq (n + 4 + 1) - seq (n + 4)) := by ring_nf
    have h3 : p * (seq (n + 3 + 1) - seq (n + 3)) < ζ / 4 := by
      have h1 : p * (seq (n + 3 + 1) - seq (n + 3)) ≤ (ζ * a) * (seq (n + 3 + 1) - seq (n + 3)) :=
        mul_le_mul_of_nonneg_right hpa.le d3p.le
      have h2 : (ζ * a) * (seq (n + 3 + 1) - seq (n + 3)) = ζ * (a * (seq (n + 3 + 1) - seq (n + 3))) := by ring
      have := mul_lt_mul_of_pos_left a3 hζ0
      linarith
    have h4 : p * (seq (n + 4 + 1) - seq (n + 4)) < 1 / 4 := by
      have h1 : p * (seq (n + 4 + 1) - seq (n + 4)) ≤ z * (seq (n + 4 + 1) - seq (n + 4)) :=
        mul_le_mul_of_nonneg_right hpz.le d4p.le
      linarith
    have h5 : 0 ≤ p * (seq (n + 3 + 1) - seq (n + 3)) := mul_nonneg hp0.le d3p.le
    have h6 : 0 ≤ p * (seq (n + 4 + 1) - seq (n + 4)) := mul_nonneg hp0.le d4p.le
    refine not_inWay_of_between (lap p (seq (n + 2))) ?_ ?_
    · show (lap p (seq (n + 2)) : ℝ) + 1 / 8 ≤ p * seq (n + 5)
      linarith [lp2]
    · show p * seq (n + 5) ≤ (lap p (seq (n + 2)) : ℝ) + 7 / 8
      linarith [lp2]
  have hnoOther : ∀ d ∈ E, d ≠ a → ¬ InWay d (seq (n + 5)) := by
    intro d hdE hda
    rcases hmem d hdE hda with h | h | h
    · rcases hxy' with ⟨h1, _⟩ | ⟨_, h1⟩
      · rw [h, ← h1]; exact hp_clear
      · rw [h, ← h1]; exact hq_clear
    · rcases hxy' with ⟨_, h1⟩ | ⟨h1, _⟩
      · rw [h, ← h1]; exact hq_clear
      · rw [h, ← h1]; exact hp_clear
    · rw [h]; exact hz_clear
  have hset5 : IsSetterAt E seq (n + 5) a := by
    rcases hmv (n + 5) with ⟨hall, _⟩ | ⟨d, hdE, hdw, ht', _⟩
    · exact absurd hw (hall a haE)
    · have hda : d = a := by
        by_contra hne
        exact hnoOther d hdE hne hdw
      subst hda
      exact ⟨haE, hw, ht'⟩
  exact ⟨rfl, hJ, hset5, z, hs1, hs4, hlow, hup, hmax⟩

#print axioms return_ratio

/-! ## (2) A second return is impossible -/

/-- **A first return of `a`, itself a setting, has no first return** [L].  `a` sets at `n`; its first return is `k` (a
setting by `return_ratio`); `k2 > k` would be the first return after `k`.  The two windows share the same largest reading `z`
(`E.erase a` has at most three members, all three setter values of each window).  `z` is in the way at `seq (n + 1)` and at
`seq (k + 1)`, and `a · (seq (k + 1) − seq (n + 1)) = 1` (one lap of `a`), so `z (seq (k + 1) − seq (n + 1)) = z / a`; both
instants put `z` within `1/8` of a lap, so `z / a` lies within `1/4` of an integer.  `return_ratio` gives `3/2 < z / a < 5/3`,
and no number in `(3/2, 5/3)` is within `1/4` of an integer.  Hypotheses: same as `return_ratio`; NOT REQUIRED: any lap or
ratio condition, `m`. -/
theorem second_return_false {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) (hcard : E.card ≤ 4) {a : ℝ} (haE : a ∈ E)
    (ha : ∀ d ∈ E, a ≤ d) {n k k2 : ℕ} (hn : IsSetterAt E seq n a) (hnk : n < k) (hw : InWay a (seq k))
    (hfirst : ∀ s, n < s → s < k → ¬ InWay a (seq s)) (hkk2 : k < k2) (hw2 : InWay a (seq k2))
    (hfirst2 : ∀ s, k < s → s < k2 → ¬ InWay a (seq s)) : False := by
  obtain ⟨hk5, hJ, hsk, z, hz1, hz4, hlow, hup, hmax⟩ := return_ratio hpos h0 hmv hcard haE ha hn hnk hw hfirst
  obtain ⟨hk5', hJ', hsk', z', hz1', hz4', hlow', hup', hmax'⟩ :=
    return_ratio hpos h0 hmv hcard haE ha hsk hkk2 hw2 hfirst2
  have ha0 : 0 < a := hpos a haE
  have hza : z ≠ a := by intro h; subst h; linarith
  have hz'a : z' ≠ a := by intro h; rw [h] at hlow'; linarith
  have hzz : z = z' := le_antisymm (hmax' z hz1.1 hza) (hmax z' hz1'.1 hz'a)
  subst hzz
  subst hk5
  have la1 : a * seq (n + 1) = (lap a (seq n) : ℝ) + 1 / 8 := by
    rw [hn.2.2]; exact setter_reading ha0 hn.2.1
  have la6 : a * seq (n + 5 + 1) = (lap a (seq (n + 5)) : ℝ) + 1 / 8 := by
    rw [hsk.2.2]; exact setter_reading ha0 hsk.2.1
  have hJR : ((lap a (seq (n + 5)) : ℤ) : ℝ) = (lap a (seq n) : ℝ) + 1 := by exact_mod_cast hJ
  have hz0 : 0 < z := by linarith
  have w1 := abs_lt.mp (abs_sub_lap_lt hz1.2.1)
  have w6 := abs_lt.mp (abs_sub_lap_lt hz1'.2.1)
  -- D = z (t6 - t1), with a (t6 - t1) = 1
  have hat : a * (seq (n + 5 + 1) - seq (n + 1)) = 1 := by
    have : a * (seq (n + 5 + 1) - seq (n + 1)) = a * seq (n + 5 + 1) - a * seq (n + 1) := by ring
    linarith
  have hD : z * (seq (n + 5 + 1) - seq (n + 1)) * a = z := by
    have : z * (seq (n + 5 + 1) - seq (n + 1)) * a = z * (a * (seq (n + 5 + 1) - seq (n + 1))) := by ring
    rw [this, hat]; ring
  set D := z * (seq (n + 5 + 1) - seq (n + 1)) with hDdef
  have hD1 : (3 : ℝ) / 2 < D := by
    by_contra hcon
    push Not at hcon
    have := mul_le_mul_of_nonneg_right hcon ha0.le
    linarith
  have hD2 : D < 5 / 3 := by
    by_contra hcon
    push Not at hcon
    have := mul_le_mul_of_nonneg_right hcon ha0.le
    linarith
  have hDe : D = z * seq (n + 5 + 1) - z * seq (n + 1) := by rw [hDdef]; ring
  have hM1 : (5 : ℝ) / 4 < ((lap z (seq (n + 5 + 1)) - lap z (seq (n + 1)) : ℤ) : ℝ) := by
    push_cast; linarith [w1.1, w1.2, w6.1, w6.2]
  have hM2 : ((lap z (seq (n + 5 + 1)) - lap z (seq (n + 1)) : ℤ) : ℝ) < 23 / 12 := by
    push_cast; linarith [w1.1, w1.2, w6.1, w6.2]
  have h1 : (1 : ℤ) < lap z (seq (n + 5 + 1)) - lap z (seq (n + 1)) := by
    have : (1 : ℝ) < ((lap z (seq (n + 5 + 1)) - lap z (seq (n + 1)) : ℤ) : ℝ) := by linarith
    exact_mod_cast this
  have h2 : lap z (seq (n + 5 + 1)) - lap z (seq (n + 1)) < 2 := by
    have : ((lap z (seq (n + 5 + 1)) - lap z (seq (n + 1)) : ℤ) : ℝ) < 2 := by linarith
    exact_mod_cast this
  omega

#print axioms second_return_false

/-! ## (3) The cascade over at most four readings is fixed within twenty moves -/

/-- **The cascade over at most four readings is fixed within twenty moves, with no lap or ratio hypothesis** [L].  `E` has at most
four members, `a` is its least member, the cascade starts at any `seq 0 > 0`.  There is `N ≤ 20` at which nobody is in the way,
and every earlier move has a setter.  Why: within the first eight moves `a` sets (`window_has_setter`), at some `n ≤ 7`; within
the next eight `a` is in the way again, so it has a first return `k`; `return_ratio` puts `k = n + 5 ≤ 12` and makes `a` its
setter; within the next eight moves `a` would be in the way a third time, a second first return, which `second_return_false`
excludes.  `[PROVISIONAL: counting tool]` for the number twenty (7 + 5 + 8): it is an OUTPUT of the laws, used inside
`reach_four_free` to place the fixed point, and is not offered as a bound on where a lonely instant lies.  Hypotheses:
`E.card ≤ 4` REQUIRED for this proof (`window_has_setter`, `return_ratio`); `a` least REQUIRED; `0 < seq 0` used;
`LapCond` NOT REQUIRED (this removes it from `LadderScale.four_cascade_fixes`). -/
theorem four_cascade_fixes_free {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) (hcard : E.card ≤ 4) {a : ℝ} (haE : a ∈ E) (ha : ∀ d ∈ E, a ≤ d) :
    ∃ N, N ≤ 20 ∧ (∀ d ∈ E, ¬ InWay d (seq N)) ∧ ∀ s, s < N → ∃ y, IsSetterAt E seq s y := by
  have hex20 : ∃ N, N ≤ 20 ∧ ∀ d ∈ E, ¬ InWay d (seq N) := by
    by_contra hcon
    push Not at hcon
    have hset : ∀ i, i ≤ 20 → ∃ x, IsSetterAt E seq i x := fun i hi =>
      exists_setter hmv (fun hall => by
        obtain ⟨d, hd, hdw⟩ := hcon i hi
        exact hall d hd hdw)
    obtain ⟨n, hn0, hn7, hna⟩ :=
      window_has_setter hpos h0 hmv hcard haE (s := 0) (fun i h1 h2 => hset i (by omega))
    obtain ⟨n', hn'1, hn'2, hn'a⟩ :=
      window_has_setter hpos h0 hmv hcard haE (s := n + 1) (fun i h1 h2 => hset i (by omega))
    have hex : ∃ k, n < k ∧ InWay a (seq k) := ⟨n', by omega, hn'a.2.1⟩
    have hk := Nat.find_spec hex
    have hfirst : ∀ s, n < s → s < Nat.find hex → ¬ InWay a (seq s) :=
      fun s h1 h2 h => Nat.find_min hex h2 ⟨h1, h⟩
    obtain ⟨hk5, -, hsk, -⟩ := return_ratio hpos h0 hmv hcard haE ha hna hk.1 hk.2 hfirst
    obtain ⟨n'', hn''1, hn''2, hn''a⟩ :=
      window_has_setter hpos h0 hmv hcard haE (s := Nat.find hex + 1) (fun i h1 h2 => hset i (by omega))
    have hex2 : ∃ k2, Nat.find hex < k2 ∧ InWay a (seq k2) := ⟨n'', by omega, hn''a.2.1⟩
    have hk2 := Nat.find_spec hex2
    have hfirst2 : ∀ s, Nat.find hex < s → s < Nat.find hex2 → ¬ InWay a (seq s) :=
      fun s h1 h2 h => Nat.find_min hex2 h2 ⟨h1, h⟩
    exact second_return_false hpos h0 hmv hcard haE ha hna hk.1 hk.2 hfirst hk2.1 hk2.2 hfirst2
  obtain ⟨N0, hN0, hN0f⟩ := hex20
  have hex : ∃ N, ∀ d ∈ E, ¬ InWay d (seq N) := ⟨N0, hN0f⟩
  refine ⟨Nat.find hex, (Nat.find_min' hex hN0f).trans hN0, Nat.find_spec hex, fun s hs => ?_⟩
  have hmin := Nat.find_min hex hs
  exact exists_setter hmv hmin

#print axioms four_cascade_fixes_free

/-! ## (4) Five disparities with the second smallest at least `7 d_min` -/

/-- **Four readings in the first window, no lap hypothesis** [L].  `E` has at most four members, all at least `m > 0`, `a` is the
least and `20 m ≤ 3 a`.  Then `E` has a lonely instant in `[1/(8m), 7/(8m)]` (`R ∈ [1, 7]`): `four_cascade_fixes_free` gives
a fixed point after at most twenty moves and `lonely_window_of_moves` places it.  `[PROVISIONAL: counting tool]` (the twenty)
as `four_cascade_fixes_free`.  Hypotheses: `20 m ≤ 3 a` REQUIRED for this proof (twenty moves against `3 a / m`); not shown
required for the statement.  NOT REQUIRED: `LapCond`, any upper bound on `a`. -/
theorem reach_four_free {E : Finset ℝ} {m a : ℝ} (hm : 0 < m) (hlow : ∀ d ∈ E, m ≤ d) (hcard : E.card ≤ 4)
    (haE : a ∈ E) (ham : ∀ d ∈ E, a ≤ d) (h20 : 20 * m ≤ 3 * a) :
    ∃ s, 1 / (8 * m) ≤ s ∧ s ≤ 7 / (8 * m) ∧ LonelyAt E s := by
  have hpos : ∀ d ∈ E, 0 < d := fun d hd => lt_of_lt_of_le hm (hlow d hd)
  have ha0 : 0 < a := hpos a haE
  have h0 : cascadeSeq E (1 / (8 * m)) 0 = 1 / (8 * m) := cascadeSeq_zero E _
  have h0pos : 0 < cascadeSeq E (1 / (8 * m)) 0 := by rw [h0]; positivity
  have hmv := cascadeSeq_isMove E (1 / (8 * m))
  obtain ⟨N, hN20, hfix, hset⟩ := four_cascade_fixes_free hpos h0pos hmv hcard haE ham
  have hN : (N : ℝ) * m ≤ 3 * a := by
    have : (N : ℝ) ≤ 20 := by exact_mod_cast hN20
    nlinarith
  obtain ⟨h1, h2, h3⟩ := lonely_window_of_moves hm hpos ha0 ham h0 hmv hfix hset hN
  exact ⟨_, h1, h2, h3⟩

#print axioms reach_four_free

/-- **Five disparities, second smallest `a` with `20 d_min ≤ 3 a`** [L].  `ds` has at most five members, least element `m`;
`a` is the least of the other four.  Then `ds` has a lonely instant in `R ∈ [1, 7]`.  The four larger readings are arbitrary
(no ceiling, no commensurability, no lap condition).  `[PROVISIONAL: counting tool]` as `four_cascade_fixes_free`; the
displacement-frame step it serves is rule 1: the isolation of the `d_min` window `[1,7]` is displaced by the setters and the
cascade (not this count) shows where it lands. -/
theorem five_disparities_of_high {ds : Finset ℝ} {m a : ℝ} (hm : IsLeast (ds : Set ℝ) m) (hm0 : 0 < m)
    (hcard : ds.card ≤ 5) (haE : a ∈ ds.erase m) (ham : ∀ d ∈ ds.erase m, a ≤ d) (h20 : 20 * m ≤ 3 * a) :
    ∃ s, 1 / (8 * m) ≤ s ∧ s ≤ 7 / (8 * m) ∧ LonelyAt ds s := by
  have hc : (ds.erase m).card ≤ 4 := by
    have := Finset.card_erase_of_mem hm.1
    omega
  have hlow : ∀ d ∈ ds.erase m, m ≤ d := fun d hd => hm.2 (Finset.mem_of_mem_erase hd)
  exact add_dmin hm hm0 (reach_four_free hm0 hlow hc haE ham h20)

#print axioms five_disparities_of_high

/-- **Five disparities, second smallest at least `57 d_min`** [L]: the instance of `five_disparities_of_high` the task asks for
(`57 m ≤ a` gives `20 m ≤ 3 a`). -/
theorem five_disparities_rho57 {ds : Finset ℝ} {m a : ℝ} (hm : IsLeast (ds : Set ℝ) m) (hm0 : 0 < m)
    (hcard : ds.card ≤ 5) (haE : a ∈ ds.erase m) (ham : ∀ d ∈ ds.erase m, a ≤ d) (h57 : 57 * m ≤ a) :
    ∃ s, 1 / (8 * m) ≤ s ∧ s ≤ 7 / (8 * m) ∧ LonelyAt ds s :=
  five_disparities_of_high hm hm0 hcard haE ham (by linarith)

#print axioms five_disparities_rho57

/-- **Five disparities, second smallest at least `5 d_min`** [L]: `LadderScale.five_disparities_of_ratio` (`5 m ≤ a < 57 m`)
and `five_disparities_rho57` (`57 m ≤ a`) together.  What is left of the five-disparity statement is exactly the part with the
second smallest below `5 d_min` (`LadderScale.FiveDisparitiesLowQuotient`, OWED there). -/
theorem five_disparities_ge5 {ds : Finset ℝ} {m a : ℝ} (hm : IsLeast (ds : Set ℝ) m) (hm0 : 0 < m)
    (hcard : ds.card ≤ 5) (haE : a ∈ ds.erase m) (ham : ∀ d ∈ ds.erase m, a ≤ d) (h5 : 5 * m ≤ a) :
    ∃ s, 1 / (8 * m) ≤ s ∧ s ≤ 7 / (8 * m) ∧ LonelyAt ds s := by
  by_cases h57 : a < 57 * m
  · exact five_disparities_of_ratio hm hm0 hcard haE ham h5 h57
  · exact five_disparities_rho57 hm hm0 hcard haE ham (not_lt.mp h57)

#print axioms five_disparities_ge5

/-! ## (5) The displacement of the unit window's left end -/

/-- **The lonely instant lies within `5/a` of the left end of the `d_min` window** [L].  `E` has at most four members, all at
least `m > 0`, `a` is the least and `20 m ≤ 3 a`.  Then `E` has a lonely instant `s` with `1/(8m) ≤ s ≤ 1/(8m) + 5/a`.  In the
gate coordinate `R = 8 m t` this is `1 ≤ R ≤ 1 + 40 m / a`.  The left end of the unit's first cell `[1/(8m), 7/(8m)]` is
displaced by the four readings by at most `20` zone widths `1/(4a)` of the slowest, and the cascade (not this bound) shows where
it lands.  `[PROVISIONAL: counting tool]` (the twenty) and `[PROVISIONAL: covering]` (a displacement against a cell length
`3/(4m) = 3 ρ_a / (4a)`), supporting the statement that the landing lies in the window; it is not offered as an existence argument
for the conjecture.  This is the quantitative form of the fine-displacement relation `DispCell.displacement_nonneg_lt`. -/
theorem reach_four_free_displacement {E : Finset ℝ} {m a : ℝ} (hm : 0 < m) (hlow : ∀ d ∈ E, m ≤ d) (hcard : E.card ≤ 4)
    (haE : a ∈ E) (ham : ∀ d ∈ E, a ≤ d) :
    ∃ s, 1 / (8 * m) ≤ s ∧ s ≤ 1 / (8 * m) + 5 / a ∧ LonelyAt E s := by
  have hpos : ∀ d ∈ E, 0 < d := fun d hd => lt_of_lt_of_le hm (hlow d hd)
  have ha0 : 0 < a := hpos a haE
  have h0 : cascadeSeq E (1 / (8 * m)) 0 = 1 / (8 * m) := cascadeSeq_zero E _
  have h0pos : 0 < cascadeSeq E (1 / (8 * m)) 0 := by rw [h0]; positivity
  have hmv := cascadeSeq_isMove E (1 / (8 * m))
  obtain ⟨N, hN20, hfix, hset⟩ := four_cascade_fixes_free hpos h0pos hmv hcard haE ham
  have hel := elapsed_le hpos ha0 ham N hset
  rw [h0] at hel
  refine ⟨_, h0 ▸ start_le_seq hpos hmv N, ?_, lonely_of_notInWay hfix⟩
  have hN : (N : ℝ) ≤ 20 := by exact_mod_cast hN20
  have h1 : (N : ℝ) / (4 * a) ≤ 5 / a := by
    rw [div_le_div_iff₀ (by positivity) ha0]; nlinarith
  linarith

#print axioms reach_four_free_displacement

/-- **Five disparities with the displacement stated** [L]: `ds` has at most five members, least `m`, second smallest `a`.  Then
there is a lonely instant `s` of `ds` with `1/(8m) ≤ s ≤ 1/(8m) + 5/a`.  When `20 m ≤ 3 a` this lies in the first window
`[1/(8m), 7/(8m)]`, where `d_min` itself is clear (`Gate.dmin_clear_first_window`); otherwise it is the displaced instant and
`d_min` is not asserted clear (it is not claimed). -/
theorem five_disparities_displacement {ds : Finset ℝ} {m a : ℝ} (hm : IsLeast (ds : Set ℝ) m) (hm0 : 0 < m)
    (hcard : ds.card ≤ 5) (haE : a ∈ ds.erase m) (ham : ∀ d ∈ ds.erase m, a ≤ d) (h20 : 20 * m ≤ 3 * a) :
    ∃ s, 1 / (8 * m) ≤ s ∧ s ≤ 1 / (8 * m) + 5 / a ∧ LonelyAt ds s := by
  have hc : (ds.erase m).card ≤ 4 := by
    have := Finset.card_erase_of_mem hm.1
    omega
  have hlow : ∀ d ∈ ds.erase m, m ≤ d := fun d hd => hm.2 (Finset.mem_of_mem_erase hd)
  obtain ⟨s, hs1, hs2, hsl⟩ := reach_four_free_displacement hm0 hlow hc haE ham
  have ha0 : 0 < a := by
    have := hm0; linarith
  have h7 : s ≤ 7 / (8 * m) := by
    have h5 : 5 / a ≤ 3 / (4 * m) := by
      rw [div_le_div_iff₀ ha0 (by positivity)]; nlinarith
    have : 1 / (8 * m) + 3 / (4 * m) = 7 / (8 * m) := by field_simp; ring
    linarith
  refine ⟨s, hs1, hs2, fun d hd => ?_⟩
  by_cases hdm : d = m
  · subst hdm
    exact Gate.dmin_clear_first_window hm0 hs1 h7
  · exact hsl d (Finset.mem_erase.mpr ⟨hdm, hd⟩)

#print axioms five_disparities_displacement

/-! ## Hypotheses (REQUIRED / NOT REQUIRED / UNDECIDED)

| hypothesis | status |
|---|---|
| `E.card ≤ 4` in `return_ratio`, `second_return_false`, `four_cascade_fixes_free` | REQUIRED for the proof (`three_distinct_shape`, `window_has_setter`: with five readings the setters between two settings of `a` can take four values); the statement at five readings is UNDECIDED (no failure on the grids of `five_high_v1.out` section 5a) |
| `a` the least member | REQUIRED for the proof (`a_lt_w`, `incr_setter` bounds `a · Δ`); REQUIRED for the statement (`FourDistinct`: a non-least setter can return after one move, exact example in `five_high_v1.out` section 5c) |
| `a` the SETTER at `n` (not merely in the way) | REQUIRED for the proof (budget at exact phase `j + 1/8`); the statement with 'in the way' is false (`ladder5_v2.out`, cited in `FourDistinct`) |
| `0 < seq 0` | used (`setter_later_lap`); NOT REQUIRED: any base `m`, `seq 0 = 1/(8m)`, any lap condition, any ratio |
| `LapCond`, `a < 57 m`, `5 m ≤ a` | NOT REQUIRED by `return_ratio`, `second_return_false`, `four_cascade_fixes_free` |
| `20 m ≤ 3 a` in `reach_four_free`, `five_disparities_of_high` | REQUIRED for the proof (twenty moves against `3 a / m`); the statement for `5 m ≤ a < 20 m / 3` is covered by `LadderScale.five_disparities_of_ratio`; the statement for `a < 5 m` is UNDECIDED (`LadderScale.FiveDisparitiesLowQuotient`, OWED) |
| positivity of the disparities | REQUIRED as stated (divisions by them) |
-/

end FiveHigh

end Fresh
