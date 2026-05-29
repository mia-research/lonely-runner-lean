import LonelyRunner.LRC.Defs
import LonelyRunner.LRC.Theorem61_BSR
import LonelyRunner.LRC.Theorem71_LargeSR

/-!
# `intLRC 3` — Lonely Runner Conjecture for n = 3

For n = 3 the Hard Case of Lemma 9.1 is vacuous: with `speeds : Fin 2 → ℕ`,
`v_{n-2}` and `v_1` are the same speed (both `speeds ⟨0, _⟩`), so the Hard Case
`(n-1)·v_1 < V ≤ (n-1)·v_{n-2}` collapses to `2·v_1 < V ≤ 2·v_1`, which is
empty. Therefore the case split reduces to BSR ∨ LR, neither of which depends
on the sorry'd Theorem 5.2 / DI-MOD branch.

This is a real proof: it discharges `intLRC 3` without any `sorry`.
-/

open MeasureTheory Set

/-- The strong-induction premise `H 3` (intLRC holds for all `m < 3`).
    Adapted from `Theorem121_Main.lean`'s inline construction; isolated here so
    the small-n proofs do not need to depend on `Theorem121_Main`. -/
theorem H_three : H 3 := by
  intro m hm
  intro speeds _hmono hpos _hgcd
  interval_cases m
  · -- m = 0: speeds : Fin 0 → ℕ ; conclusion is over an empty index, vacuous
    exact ⟨0, fun i => i.elim0⟩
  · -- m = 1: speeds : Fin 0 → ℕ ; same as above
    exact ⟨0, fun i => i.elim0⟩
  · -- m = 2: one slow runner; t = 1/(2 v) gives circDist(v · t) = circDist(1/2) = 1/2
    refine ⟨1 / (2 * (speeds ⟨0, by omega⟩ : ℝ)), fun i => ?_⟩
    have hi : i = ⟨0, by omega⟩ := Fin.ext (by omega)
    subst hi
    have hv : (0 : ℝ) < speeds ⟨0, by omega⟩ := by exact_mod_cast hpos ⟨0, by omega⟩
    rw [show (speeds ⟨0, by omega⟩ : ℝ) * (1 / (2 * speeds ⟨0, by omega⟩)) = 1 / 2
        from by field_simp]
    have h_floor : ⌊(1 / 2 : ℝ)⌋ = (0 : ℤ) := Int.floor_eq_zero_iff.mpr (by norm_num)
    have h_frac : Int.fract (1 / 2 : ℝ) = 1 / 2 := by
      simp only [Int.fract, h_floor, Int.cast_zero, sub_zero]
    show circDist (1 / 2 : ℝ) ≥ (1 : ℝ) / 2
    unfold circDist
    rw [h_frac]
    norm_num

/-- **Main result for n = 3.**  The Lonely Runner Conjecture holds with two
    runners (`Fin 2`), positive distinct integer speeds with `gcd = 1`.

    Proof: case split on whether `V := speeds 1 ≤ 2 · speeds 0` (BSR) or not
    (LR; the Hard Case is vacuous as `v_{n-2} = v_1` for n = 3). -/
theorem intLRC_three : intLRC 3 := by
  intro speeds hmono hpos _hgcd
  -- Decompose speeds : Fin 2 → ℕ into V = speeds 1 and slowSpeeds (just speeds 0)
  let V : ℕ := speeds ⟨1, by omega⟩
  let slowSpeeds : Fin 1 → ℕ := fun _ => speeds ⟨0, by omega⟩
  have hpos_slow : ∀ i, 0 < slowSpeeds i := fun _ => hpos ⟨0, by omega⟩
  have hmono_slow : StrictMono slowSpeeds := by
    intro a b hab; exact absurd hab (by fin_cases a <;> fin_cases b <;> decide)
  -- Case split: V ≤ 2·v₁ (BSR) or 2·v₁ < V (LR). The Hard Case is vacuous.
  by_cases hBSR : V ≤ 2 * speeds ⟨0, by omega⟩
  · -- BSR Case: explicit time t* = 1/(3·v₁)
    refine ⟨bsr_time 3 (speeds ⟨0, by omega⟩), ?_⟩
    intro i
    have hV_bsr : speeds ⟨3 - 2, by omega⟩ ≤ (3 - 1) * speeds ⟨0, by omega⟩ := by
      show speeds ⟨1, by omega⟩ ≤ 2 * speeds ⟨0, by omega⟩
      exact hBSR
    exact theorem61_BSR 3 (by norm_num) speeds hpos hmono hV_bsr i
  · -- LR Case: 2·v₁ < V; apply Theorem 7.1 with H 3
    push_neg at hBSR
    have hV_large : (3 - 1) * slowSpeeds ⟨3 - 3, by omega⟩ < V := by
      show 2 * speeds ⟨0, by omega⟩ < V
      exact hBSR
    obtain ⟨t₀, ht₀_slow, ht₀_V⟩ :=
      theorem71_LargeSR 3 (by norm_num) slowSpeeds V hpos_slow hmono_slow hV_large H_three
    refine ⟨t₀, fun i => ?_⟩
    -- speeds : Fin 2 → ℕ; case on i = 0 (slow) vs i = 1 (V)
    by_cases hi : i.val = 0
    · -- Slow runner: speeds i = slowSpeeds ⟨0, _⟩
      have h := ht₀_slow ⟨0, by omega⟩
      simp only [slowSpeeds] at h
      have heq : (speeds i : ℝ) = (speeds ⟨0, by omega⟩ : ℝ) := by
        congr 2; exact Fin.ext hi
      rw [heq]; exact h
    · -- Fast runner: i.val = 1, speeds i = V
      have hi1 : i.val = 1 := by omega
      have heq : (speeds i : ℝ) = (V : ℝ) := by
        show (speeds i : ℝ) = (speeds ⟨1, by omega⟩ : ℝ)
        congr 2; exact Fin.ext hi1
      rw [heq]; exact ht₀_V
