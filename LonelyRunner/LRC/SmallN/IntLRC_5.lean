import LonelyRunner.LRC.Defs
import LonelyRunner.LRC.Theorem61_BSR
import LonelyRunner.LRC.Theorem71_LargeSR
import LonelyRunner.LRC.SmallN.IntLRC_4
import LonelyRunner.LRC.SmallN.IntLRC_5_Bienia

/-!
# `intLRC 5` — Lonely Runner Conjecture for n = 5

Four moving runners + observer, target gap `1/5`. Literature `n = 4`
(observer omitted). Open-access source: Barajas–Serra 2008 §3 (|D|=4 case,
using the Prime Filtering Lemma with prime `p = 5`).

Structure mirrors `IntLRC_4.lean`: BSR and LR cases discharge via
`theorem61_BSR` / `theorem71_LargeSR`; Hard Case `4·v_1 < V ≤ 4·v_3` is closed
via `intLRC_five_residual` (Bienia §4) in `IntLRC_5_Bienia.lean`, covering
`|D| ∈ {1,2,3}` (the `|D| = 1` crux is Bienia's doubling argument).

**Sorry budget:** 0 — `intLRC_five` is sorry-free
(`#print axioms` = `propext, Classical.choice, Quot.sound`).
-/

open MeasureTheory Set

/-- Strong-induction premise `H 5`: chains down to `H_four` and `intLRC_four`. -/
theorem H_five : H 5 := by
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
  · exact intLRC_four speeds hmono hpos hgcd

/-- **Prime trick (p = 5).** If `5 ∤ v`, then at `t = 1/5` runner `v` sits at a
    nonzero multiple of `1/5` (its residue `v mod 5 ∈ {1,2,3,4}`), so
    `circDist (v·(1/5)) ≥ 1/5`.  This discharges the entire "no speed divisible
    by 5" subcase of the Hard Case in one shot. -/
lemma circDist_fifth_of_not_dvd (v : ℕ) (h : ¬ (5 ∣ v)) :
    circDist ((v : ℝ) * (1 / 5)) ≥ 1 / 5 := by
  have hr0 : v % 5 ≠ 0 := fun hh => h (Nat.dvd_of_mod_eq_zero hh)
  have hrlt : v % 5 < 5 := Nat.mod_lt v (by norm_num)
  have hr1R : (1 : ℝ) ≤ (↑(v % 5) : ℝ) := by exact_mod_cast (by omega : 1 ≤ v % 5)
  have hr4R : (↑(v % 5) : ℝ) ≤ 4 := by exact_mod_cast (by omega : v % 5 ≤ 4)
  have hsplit : (v : ℝ) * (1 / 5) = (↑(v % 5) : ℝ) / 5 + (↑(v / 5) : ℝ) := by
    have hvR : (v : ℝ) = 5 * (↑(v / 5) : ℝ) + (↑(v % 5) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod v 5).symm
    rw [hvR]; ring
  rw [hsplit]
  unfold circDist
  rw [Int.fract_add_natCast]
  have hfr : Int.fract ((↑(v % 5) : ℝ) / 5) = (↑(v % 5) : ℝ) / 5 :=
    Int.fract_eq_self.mpr ⟨by positivity, by rw [div_lt_one (by norm_num)]; linarith⟩
  rw [hfr, ge_iff_le, le_min_iff]
  exact ⟨by linarith, by linarith⟩

/-- **Main result for n = 5** (sorry-free).  `speeds : Fin 4 → ℕ`.
    BSR `V ≤ 4·v_1`; LR `4·v_3 < V`; Hard `4·v_1 < V ≤ 4·v_3`.  The Hard Case
    further splits on divisibility by the prime `5`: if no speed is divisible
    by `5`, then `t = 1/5` works (`circDist_fifth_of_not_dvd`); the residual
    (some speed `≡ 0 mod 5`) is closed by `intLRC_five_residual` (Bienia §4). -/
theorem intLRC_five : intLRC 5 := by
  intro speeds hmono hpos hgcd
  let V : ℕ := speeds ⟨3, by omega⟩
  let slowSpeeds : Fin 3 → ℕ := fun i => speeds ⟨i.val, by omega⟩
  have hpos_slow : ∀ i, 0 < slowSpeeds i := fun i => hpos ⟨i.val, by omega⟩
  have hmono_slow : StrictMono slowSpeeds := by
    intro a b hab
    show speeds ⟨a.val, by omega⟩ < speeds ⟨b.val, by omega⟩
    exact hmono (show (⟨a.val, by omega⟩ : Fin 4) < ⟨b.val, by omega⟩ from hab)
  by_cases hBSR : V ≤ 4 * speeds ⟨0, by omega⟩
  · -- BSR Case: t* = 1/(5·v_1)
    refine ⟨bsr_time 5 (speeds ⟨0, by omega⟩), ?_⟩
    intro i
    have hV_bsr : speeds ⟨5 - 2, by omega⟩ ≤ (5 - 1) * speeds ⟨0, by omega⟩ := by
      change speeds ⟨3, by omega⟩ ≤ 4 * speeds ⟨0, by omega⟩; exact hBSR
    exact theorem61_BSR 5 (by norm_num) speeds hpos hmono hV_bsr i
  · push_neg at hBSR
    by_cases hLR : 4 * speeds ⟨2, by omega⟩ < V
    · -- LR Case
      have hV_large : (5 - 1) * slowSpeeds ⟨5 - 3, by omega⟩ < V := by
        change 4 * speeds ⟨2, by omega⟩ < V; exact hLR
      obtain ⟨t₀, ht₀_slow, ht₀_V⟩ :=
        theorem71_LargeSR 5 (by norm_num) slowSpeeds V hpos_slow hmono_slow hV_large H_five
      refine ⟨t₀, fun i => ?_⟩
      by_cases hi : i.val < 3
      · have h := ht₀_slow ⟨i.val, hi⟩
        simp only [slowSpeeds] at h
        have heq : (speeds i : ℝ) = (speeds ⟨i.val, by omega⟩ : ℝ) := by rfl
        rw [heq]; exact h
      · push_neg at hi
        have hi3 : i.val = 3 := by omega
        have heq : (speeds i : ℝ) = (V : ℝ) := by
          change (speeds i : ℝ) = (speeds ⟨3, by omega⟩ : ℝ)
          congr 2; exact Fin.ext hi3
        rw [heq]; exact ht₀_V
    · push_neg at hLR
      -- Hard Case: 4·v_1 < V ≤ 4·v_3.  Split on divisibility by the prime 5.
      by_cases h5 : ∃ i, 5 ∣ speeds i
      · -- Hard residual: some speed ≡ 0 mod 5.  Bienia §4 (`intLRC_five_residual`):
        -- `|D| ∈ {1,2,3}` all closed via `lemma3` (|D|=1 uses Bienia's doubling).
        exact intLRC_five_residual speeds hmono hpos hgcd h5
      · -- Easy subcase: no speed divisible by 5 → t = 1/5 witnesses all distant.
        push_neg at h5
        exact ⟨1 / 5, fun i => circDist_fifth_of_not_dvd (speeds i) (h5 i)⟩
