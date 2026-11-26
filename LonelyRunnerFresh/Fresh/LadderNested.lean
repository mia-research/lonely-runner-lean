import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Admissible
import Fresh.AdmissibleFlank
import Fresh.FastPairReal

/-!
# The nested-window ladder: readings separated by a factor of 3 are jointly clear without any cascade

Written 2026-10-25.  New file.  Worklist tags: G02 (irregular spread or geometric ladder, no compact cluster), G05 (two readings: the pair window), G03 (one reading), G11 (nested scales).
Mechanism M-A applied level by level: a `1/4`-wide phase band of the slowest reading is a time interval `J₁` of width `1/(4 x)` on which `x` is clear; the next reading
`y ≥ 3 x` has a `1/4`-band inside `J₁` (its search window `3/(4 y)` fits in `1/(4 x)`); and so on.  The last reading only needs a clear point in the remaining interval, so
`y ≥ x` suffices for the last step.
`LadderOK L`: positive, ascending list with `L[i+1] ≥ 3 L[i]` except the last step (any `≥ 1` ratio).  `ladder_gap`: every interval of length `3/(4 head)` (`1/(4 x)` for one reading)
contains an instant at which every reading of `L` is `1/8`-clear.  `LadderClass`: the subject's disparities are such a list; `ladder_isolation`.  Grade [L].
For seven disparities the class is: five consecutive ratios at least `3`, the last at least `1`.  Interplay: `FastPairReal.pair_window` is the two-element case.
-/

open Classical

namespace Fresh.LadderNested

open Fresh Fresh.Admissible Fresh.AdmissibleFlank Fresh.FastPairReal

-- STANDING: DEFINITION
def LadderOK : List ℝ → Prop
  | [] => True
  | [x] => 0 < x
  | [x, y] => 0 < x ∧ x ≤ y
  | x :: y :: z :: t => 0 < x ∧ 3 * x ≤ y ∧ LadderOK (y :: z :: t)

noncomputable def LadderGap : List ℝ → ℝ
  | [] => 0
  | [x] => 1 / (4 * x)
  | x :: _ :: _ => 3 / (4 * x)

theorem ladderOK_cons {x y : ℝ} {t : List ℝ} (h : LadderOK (x :: y :: t)) :
    0 < x ∧ LadderGap (y :: t) ≤ 1 / (4 * x) ∧ LadderOK (y :: t) := by
  cases t with
  | nil =>
    obtain ⟨hx, hxy⟩ := h
    refine ⟨hx, ?_, by exact lt_of_lt_of_le hx hxy⟩
    simp only [LadderGap]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  | cons z t' =>
    obtain ⟨hx, h3, hrest⟩ := h
    refine ⟨hx, ?_, hrest⟩
    have hy : 0 < y := by linarith
    simp only [LadderGap]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

theorem ladder_gap : ∀ (L : List ℝ), LadderOK L → ∀ α : ℝ,
    ∃ t : ℝ, α ≤ t ∧ t ≤ α + LadderGap L ∧ ∀ f ∈ L, (1 / 8 : ℝ) ≤ distInt (f * t)
  | [], _, α => ⟨α, le_refl _, by simp [LadderGap], by simp⟩
  | [x], hx0, α => by
    have hx : 0 < x := hx0
    obtain ⟨w, hw1, hw2, m, hm1, hm2⟩ := exists_band_point (x * α)
    refine ⟨w / x, ?_, ?_, ?_⟩
    · rw [le_div_iff₀ hx]; linarith
    · simp only [LadderGap]
      rw [div_le_iff₀ hx]
      have : (α + 1 / (4 * x)) * x = x * α + 1 / 4 := by field_simp
      linarith
    · intro f hf
      rw [List.mem_singleton] at hf
      subst hf
      rw [show f * (w / f) = w by field_simp]
      exact Fresh.Localisation.clear_of_window m hm1 (by linarith)
  | x :: y :: t, h, α => by
    obtain ⟨hx, hgap, hrest⟩ := ladderOK_cons h
    obtain ⟨s, hs1, hs2, m, hm1, hm2⟩ := exists_quarter_band (x * α)
    set α' : ℝ := s / x with hα'
    obtain ⟨u, hu1, hu2, hu3⟩ := ladder_gap (y :: t) hrest α'
    have hα'1 : α ≤ α' := by rw [hα', le_div_iff₀ hx]; linarith
    have hα'2 : α' ≤ α + 1 / (2 * x) := by
      rw [hα', div_le_iff₀ hx]
      have : (α + 1 / (2 * x)) * x = x * α + 1 / 2 := by field_simp
      linarith
    refine ⟨u, by linarith, ?_, ?_⟩
    · have : u ≤ α' + 1 / (4 * x) := by linarith
      have e : 1 / (2 * x) + 1 / (4 * x) = LadderGap (x :: y :: t) := by
        simp only [LadderGap]; field_simp; ring
      linarith
    · intro f hf
      rcases List.mem_cons.1 hf with rfl | hf'
      · have hxs : s ≤ f * u := by
          have : α' ≤ u := hu1
          rw [hα', div_le_iff₀ hx] at this
          linarith
        have hxe : f * u ≤ s + 1 / 4 := by
          have : u ≤ α' + 1 / (4 * f) := by linarith
          have h2 : f * u ≤ f * (α' + 1 / (4 * f)) := mul_le_mul_of_nonneg_left this hx.le
          have h3 : f * (α' + 1 / (4 * f)) = s + 1 / 4 := by rw [hα']; field_simp
          linarith
        exact Fresh.Localisation.clear_of_window m (by linarith) (by linarith)
      · exact hu3 f hf'

-- STANDING: DEFINITION
def LadderClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ L : List ℝ, LadderOK L ∧ ∀ d : ℝ, d ∈ disparitySet v k ↔ d ∈ L

theorem ladder_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : LadderClass v k) : Isolation v k := by
  obtain ⟨L, hL, hmem⟩ := h
  obtain ⟨t, ht1, _, ht3⟩ := ladder_gap L hL 1
  refine ⟨t, by linarith, ?_⟩
  rw [Fresh.Localisation.isolatedAt_iff]
  intro d hd
  exact ht3 d ((hmem d).1 hd)

#print axioms ladder_gap
#print axioms ladder_isolation

end Fresh.LadderNested
