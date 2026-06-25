import LonelyRunner.LRC.Defs
import LonelyRunner.LRC.Theorem61_BSR
import LonelyRunner.LRC.Theorem71_LargeSR
import LonelyRunner.LRC.SmallN.IntLRC_6
import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Main

/-!
# `intLRC 7` — Lonely Runner Conjecture for n = 7

Six moving runners + observer, target gap `1/7`. Literature `n = 6`.
Open-access source: Barajas–Serra 2008
([EJC 15 R48](https://www.combinatorics.org/Volume_15/PDF/v15i1r48.pdf)),
using Prime Filtering Lemma with prime `p = 7`.

Structure mirrors `IntLRC_4.lean`. Hard Case: `6·v_1 < V ≤ 6·v_5`.
**Sorry budget:** 1.
-/

open MeasureTheory Set

theorem H_seven : H 7 := by
  intro m hm
  intro speeds hmono hpos hgcd
  interval_cases m
  · exact ⟨0, fun i => i.elim0⟩
  · exact ⟨0, fun i => i.elim0⟩
  · refine ⟨1 / (2 * (speeds ⟨0, by omega⟩ : ℝ)), fun i => ?_⟩
    have hi : i = ⟨0, by omega⟩ := Fin.ext (by omega)
    subst hi
    have hv : (0 : ℝ) < speeds ⟨0, by omega⟩ := by exact_mod_cast hpos ⟨0, by omega⟩
    rw [show (speeds ⟨0, by omega⟩ : ℝ) * (1 / (2 * speeds ⟨0, by omega⟩)) = 1 / 2
        from by field_simp]
    have h_floor : ⌊(1 / 2 : ℝ)⌋ = (0 : ℤ) := Int.floor_eq_zero_iff.mpr (by norm_num)
    have h_frac : Int.fract (1 / 2 : ℝ) = 1 / 2 := by
      simp only [Int.fract, h_floor, Int.cast_zero, sub_zero]
    change circDist (1 / 2 : ℝ) ≥ (1 : ℝ) / 2
    unfold circDist; rw [h_frac]; norm_num
  · exact intLRC_three speeds hmono hpos hgcd
  · exact intLRC_four speeds hmono hpos hgcd
  · exact intLRC_five speeds hmono hpos hgcd
  · exact intLRC_six speeds hmono hpos hgcd

theorem intLRC_seven : intLRC 7 := by
  intro speeds hmono hpos hgcd
  let V : ℕ := speeds ⟨5, by omega⟩
  let slowSpeeds : Fin 5 → ℕ := fun i => speeds ⟨i.val, by omega⟩
  have hpos_slow : ∀ i, 0 < slowSpeeds i := fun i => hpos ⟨i.val, by omega⟩
  have hmono_slow : StrictMono slowSpeeds := by
    intro a b hab
    show speeds ⟨a.val, by omega⟩ < speeds ⟨b.val, by omega⟩
    exact hmono (show (⟨a.val, by omega⟩ : Fin 6) < ⟨b.val, by omega⟩ from hab)
  by_cases hBSR : V ≤ 6 * speeds ⟨0, by omega⟩
  · refine ⟨bsr_time 7 (speeds ⟨0, by omega⟩), ?_⟩
    intro i
    have hV_bsr : speeds ⟨7 - 2, by omega⟩ ≤ (7 - 1) * speeds ⟨0, by omega⟩ := by
      change speeds ⟨5, by omega⟩ ≤ 6 * speeds ⟨0, by omega⟩; exact hBSR
    exact theorem61_BSR 7 (by norm_num) speeds hpos hmono hV_bsr i
  · push_neg at hBSR
    by_cases hLR : 6 * speeds ⟨4, by omega⟩ < V
    · have hV_large : (7 - 1) * slowSpeeds ⟨7 - 3, by omega⟩ < V := by
        change 6 * speeds ⟨4, by omega⟩ < V; exact hLR
      obtain ⟨t₀, ht₀_slow, ht₀_V⟩ :=
        theorem71_LargeSR 7 (by norm_num) slowSpeeds V hpos_slow hmono_slow hV_large H_seven
      refine ⟨t₀, fun i => ?_⟩
      by_cases hi : i.val < 5
      · have h := ht₀_slow ⟨i.val, hi⟩
        simp only [slowSpeeds] at h
        have heq : (speeds i : ℝ) = (speeds ⟨i.val, by omega⟩ : ℝ) := by rfl
        rw [heq]; exact h
      · push_neg at hi
        have hi5 : i.val = 5 := by omega
        have heq : (speeds i : ℝ) = (V : ℝ) := by
          change (speeds i : ℝ) = (speeds ⟨5, by omega⟩ : ℝ)
          congr 2; exact Fin.ext hi5
        rw [heq]; exact ht₀_V
    · push_neg at hLR
      -- Hard Case: 6·v_1 < V ≤ 6·v_5.
      -- Barajas–Serra 2008 proves intLRC 7 unconditionally (gcd = 1 + positivity);
      -- the hard-case bounds are not needed. The single remaining `sorry` is the
      -- discrete core `IntLRC7BS.bs_discrete`.
      have h := IntLRC7BS.barajas_serra_seven speeds hmono hpos hgcd
      simpa using h
