import LonelyRunner.LRC.Defs
import LonelyRunner.LRC.Theorem61_BSR
import LonelyRunner.LRC.Theorem71_LargeSR
import LonelyRunner.LRC.SmallN.IntLRC_5

/-!
# `intLRC 6` — Lonely Runner Conjecture for n = 6

Five moving runners + observer, target gap `1/6`. Literature `n = 5`.
Open-access source: BHK 2001 ("Six Lonely Runners",
[EJC 8 (2001) R3](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v8i2r3)).

Structure mirrors `IntLRC_4.lean`. Hard Case: `5·v_1 < V ≤ 5·v_4`.
**Sorry budget:** 1.
-/

open MeasureTheory Set

theorem H_six : H 6 := by
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

theorem intLRC_six : intLRC 6 := by
  intro speeds hmono hpos hgcd
  let V : ℕ := speeds ⟨4, by omega⟩
  let slowSpeeds : Fin 4 → ℕ := fun i => speeds ⟨i.val, by omega⟩
  have hpos_slow : ∀ i, 0 < slowSpeeds i := fun i => hpos ⟨i.val, by omega⟩
  have hmono_slow : StrictMono slowSpeeds := by
    intro a b hab
    show speeds ⟨a.val, by omega⟩ < speeds ⟨b.val, by omega⟩
    exact hmono (show (⟨a.val, by omega⟩ : Fin 5) < ⟨b.val, by omega⟩ from hab)
  by_cases hBSR : V ≤ 5 * speeds ⟨0, by omega⟩
  · refine ⟨bsr_time 6 (speeds ⟨0, by omega⟩), ?_⟩
    intro i
    have hV_bsr : speeds ⟨6 - 2, by omega⟩ ≤ (6 - 1) * speeds ⟨0, by omega⟩ := by
      change speeds ⟨4, by omega⟩ ≤ 5 * speeds ⟨0, by omega⟩; exact hBSR
    exact theorem61_BSR 6 (by norm_num) speeds hpos hmono hV_bsr i
  · push_neg at hBSR
    by_cases hLR : 5 * speeds ⟨3, by omega⟩ < V
    · have hV_large : (6 - 1) * slowSpeeds ⟨6 - 3, by omega⟩ < V := by
        change 5 * speeds ⟨3, by omega⟩ < V; exact hLR
      obtain ⟨t₀, ht₀_slow, ht₀_V⟩ :=
        theorem71_LargeSR 6 (by norm_num) slowSpeeds V hpos_slow hmono_slow hV_large H_six
      refine ⟨t₀, fun i => ?_⟩
      by_cases hi : i.val < 4
      · have h := ht₀_slow ⟨i.val, hi⟩
        simp only [slowSpeeds] at h
        have heq : (speeds i : ℝ) = (speeds ⟨i.val, by omega⟩ : ℝ) := by rfl
        rw [heq]; exact h
      · push_neg at hi
        have hi4 : i.val = 4 := by omega
        have heq : (speeds i : ℝ) = (V : ℝ) := by
          change (speeds i : ℝ) = (speeds ⟨4, by omega⟩ : ℝ)
          congr 2; exact Fin.ext hi4
        rw [heq]; exact ht₀_V
    · push_neg at hLR
      -- Hard Case: 5·v_1 < V ≤ 5·v_4
      -- TODO: BHK 2001 geometric covering argument
      sorry
