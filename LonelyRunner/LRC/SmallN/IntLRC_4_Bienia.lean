import LonelyRunner.LRC.Defs
import LonelyRunner.LRC.SmallN.IntLRC_3

/-!
# Bienia et al. 1998 — proof of `intLRC 4`

Source: Bienia, Goddyn, Gvozdjak, Sebő, Tarsi (1998), "Flows, View
Obstructions and the Lonely Runner", JCTB 72:1-9, §3.

Their `k = 3` case = our `intLRC 4` (3 moving + observer, target gap 1/4).

This file builds up the proof in pieces:
1. **`intLRC_four_all_odd`** — if all three speeds are odd, `t = 1/2` works.
   (Fully proved.)
2. **`intLRC_four_pre_jump`** — TODO. If gcd of two speeds doesn't divide
   the third, reduce to `intLRC_three`.
3. **`intLRC_four_main`** — TODO. The T-interval connectedness argument
   under WLOG hypotheses.
4. **`intLRC_four_classical`** — combine 1–3.
-/

open MeasureTheory Set

/-- Periodicity of `Int.fract` under adding a natural-number cast. -/
private lemma fract_add_nat (x : ℝ) (n : ℕ) :
    Int.fract ((n : ℝ) + x) = Int.fract x :=
  Int.fract_natCast_add n x

/-- `circDist (1/2) = 1/2`. -/
private lemma circDist_half : circDist (1 / 2 : ℝ) = 1 / 2 := by
  unfold circDist
  have h_floor : ⌊(1 / 2 : ℝ)⌋ = 0 := Int.floor_eq_zero_iff.mpr (by norm_num)
  have h_fract : Int.fract (1 / 2 : ℝ) = 1 / 2 := by
    simp only [Int.fract, h_floor, Int.cast_zero, sub_zero]
  rw [h_fract]
  norm_num

/-- **Bienia §3 Step 1 — all-odd case.**
    If three positive distinct integer speeds are all odd, then `t = 1/2`
    is a witness (every runner is at distance `1/2 ≥ 1/4` from origin). -/
theorem intLRC_four_all_odd (speeds : Fin 3 → ℕ) (hodd : ∀ i, Odd (speeds i)) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 4 := by
  refine ⟨1 / 2, fun i => ?_⟩
  obtain ⟨k, hk⟩ := hodd i
  -- speeds i = 2k+1, so (speeds i : ℝ) * (1/2) = k + 1/2
  have hcast : (speeds i : ℝ) * (1 / 2) = (k : ℝ) + 1 / 2 := by
    have hnat : (speeds i : ℝ) = ((2 * k + 1 : ℕ) : ℝ) := by exact_mod_cast hk
    rw [hnat]
    push_cast
    ring
  rw [hcast]
  -- circDist((k : ℝ) + 1/2) = circDist(1/2) by periodicity
  have hperiod : circDist ((k : ℝ) + 1 / 2) = circDist (1 / 2 : ℝ) := by
    unfold circDist
    rw [fract_add_nat (1 / 2) k]
  rw [hperiod, circDist_half]
  norm_num
