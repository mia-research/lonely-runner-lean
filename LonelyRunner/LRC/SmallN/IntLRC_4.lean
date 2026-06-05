import LonelyRunner.LRC.Defs
import LonelyRunner.LRC.Theorem61_BSR
import LonelyRunner.LRC.Theorem71_LargeSR
import LonelyRunner.LRC.SmallN.IntLRC_3
import LonelyRunner.LRC.SmallN.IntLRC_4_Bienia

/-!
# `intLRC 4` — Lonely Runner Conjecture for n = 4

Three moving runners + observer, target gap `1/4`. In the literature's
convention (observer omitted) this is the case `n = 3` settled by
Betke–Wills 1972 and Cusick 1974, with shorter modern proofs by Bienia et al.
1998 (flows) and Renault 2004 (congruence classes mod n+1 = 4).

This file structures the proof via our framework's case split
(Lemma 9.1: BSR / LR / Hard). The BSR and LR cases discharge cleanly from
`theorem61_BSR` and `theorem71_LargeSR` respectively. The Hard Case
`3·v_1 < V ≤ 3·v_2` is the residual that requires a classical argument; it is
left as a single `sorry` with a structured TODO.

**Sorry budget:** 1 (the Hard Case body). Everything else, including the
strong-induction premise `H 4`, is fully proved.
-/

open MeasureTheory Set

/-- The strong-induction premise `H 4`.  For `m < 4`:
    `m = 0, 1` are vacuous; `m = 2` has an explicit witness `t = 1/(2v)`;
    `m = 3` is `intLRC_three`. -/
theorem H_four : H 4 := by
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
    unfold circDist
    rw [h_frac]
    norm_num
  · exact intLRC_three speeds hmono hpos hgcd

/-- **Main result for n = 4** (sorry'd at the Hard Case).

    `speeds : Fin 3 → ℕ` distinct positive integers, `gcd = 1`.  Case split via
    Lemma 9.1:
    - BSR `V ≤ 3·v_1`: explicit time `t* = 1/(4·v_1)` via `theorem61_BSR`.
    - LR `3·v_2 < V`: neighbourhood argument via `theorem71_LargeSR` + `H 4`.
    - Hard `3·v_1 < V ≤ 3·v_2`: requires the classical argument
      (Bienia/Renault/Chen). **Currently `sorry`.** -/
theorem intLRC_four : intLRC 4 := by
  intro speeds hmono hpos hgcd
  let V : ℕ := speeds ⟨2, by omega⟩
  let slowSpeeds : Fin 2 → ℕ := fun i => speeds ⟨i.val, by omega⟩
  have hpos_slow : ∀ i, 0 < slowSpeeds i := fun i => hpos ⟨i.val, by omega⟩
  have hmono_slow : StrictMono slowSpeeds := by
    intro a b hab
    show speeds ⟨a.val, by omega⟩ < speeds ⟨b.val, by omega⟩
    exact hmono (show (⟨a.val, by omega⟩ : Fin 3) < ⟨b.val, by omega⟩ from hab)
  -- Case split inline (avoids dependency on Theorem121_Main which has a sorry):
  -- BSR: V ≤ 3 v_1; LR: 3 v_2 < V; Hard: 3 v_1 < V ≤ 3 v_2.
  by_cases hBSR : V ≤ 3 * speeds ⟨0, by omega⟩
  · -- BSR Case: explicit time t* = 1/(4·v_1)
    refine ⟨bsr_time 4 (speeds ⟨0, by omega⟩), ?_⟩
    intro i
    have hV_bsr : speeds ⟨4 - 2, by omega⟩ ≤ (4 - 1) * speeds ⟨0, by omega⟩ := by
      change speeds ⟨2, by omega⟩ ≤ 3 * speeds ⟨0, by omega⟩
      exact hBSR
    exact theorem61_BSR 4 (by norm_num) speeds hpos hmono hV_bsr i
  · push_neg at hBSR
    -- 3·v_1 < V; split LR vs Hard
    by_cases hLR : 3 * speeds ⟨1, by omega⟩ < V
    · -- LR Case: 3·v_2 < V; apply theorem71_LargeSR with H_four
      have hV_large : (4 - 1) * slowSpeeds ⟨4 - 3, by omega⟩ < V := by
        change 3 * speeds ⟨1, by omega⟩ < V
        exact hLR
      obtain ⟨t₀, ht₀_slow, ht₀_V⟩ :=
        theorem71_LargeSR 4 (by norm_num) slowSpeeds V hpos_slow hmono_slow hV_large H_four
      refine ⟨t₀, fun i => ?_⟩
      by_cases hi : i.val < 2
      · -- Slow runner
        have h := ht₀_slow ⟨i.val, hi⟩
        simp only [slowSpeeds] at h
        have heq : (speeds i : ℝ) = (speeds ⟨i.val, by omega⟩ : ℝ) := by
          rfl
        rw [heq]; exact h
      · -- Fast runner: i.val = 2
        push_neg at hi
        have hi2 : i.val = 2 := by omega
        have heq : (speeds i : ℝ) = (V : ℝ) := by
          change (speeds i : ℝ) = (speeds ⟨2, by omega⟩ : ℝ)
          congr 2; exact Fin.ext hi2
        rw [heq]; exact ht₀_V
    · push_neg at hLR
      -- Hard Case: 3·v_1 < V ≤ 3·v_2
      -- Apply Bienia's case split: all-odd vs. else.
      by_cases hall_odd : ∀ i, Odd (speeds i)
      · -- All three speeds odd: Bienia §3 step 1, t = 1/2.
        exact intLRC_four_all_odd speeds hall_odd
      · -- Not all odd: pre-jump reduction (Path A, proved) +
        -- T-interval main argument (Path B, residual sorry inside the lemma).
        exact intLRC_four_not_all_odd speeds hmono hpos hgcd hall_odd
