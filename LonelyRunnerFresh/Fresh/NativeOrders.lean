import Mathlib
import Fresh.Framework
import Fresh.DistIntFract
import Fresh.Nv_OrdersThreeFourN
import Fresh.Nv_RealFiveN
import Fresh.Nv_RealSixN
import Fresh.Nv_RealSevenN
import Fresh.FastPairConverse
import Fresh.FreeStepSeven

/-!
# Orders three to seven on real speeds, in `Fresh/`

Written 2026-10-25.  New file.  The nested repo's native lower-order results (owner ruling 2026-09-25: orders 3 to 7 are native and may be used) were ported file by file into `Fresh/Nv_*.lean`
(96 files, imports renamed only; all compile; no `sorry`, `native_decide`, `admit` or `unsafe` in code).  This file states them in `distInt` form: for `m` positive disparities, `m ≤ 6`,
some `σ > 0` has every `d σ` at distance at least `1/(m+1)` from an integer.  It proves `SixClear5` and `SevenClear6`, which were `-- STANDING: IMPORTED` in `FastPairConverse` and `FreeStepSeven`.
Grade [L].  The ported proofs are the owner's framework forms (orders three and four from `OrdersThreeFourN`, five, six, seven through the shared integer-to-real transfer `RealTransferN`).
-/

namespace Fresh.NativeOrders

open Fresh LRC.SpecN

theorem circDist_eq (x : ℝ) : circDist x = distInt x := by
  unfold circDist
  exact (Fresh.distInt_eq_fract x).symm

theorem clear_of_existence {n : ℕ} (hn : 0 < n) (h : ExistenceAtN n) (ds : Finset ℝ) (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ n - 1) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ d ∈ ds, (1 : ℝ) / n ≤ distInt (d * σ) := by
  obtain ⟨σ, hσ, hl⟩ := h ds hpos hcard
  refine ⟨σ, hσ, fun d hd => ?_⟩
  have := hl d hd
  rw [circDist_eq] at this
  simpa [one_div] using this

theorem clear_three {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ 2) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ d ∈ ds, (1 : ℝ) / 3 ≤ distInt (d * σ) :=
  clear_of_existence (n := 3) (by norm_num) existenceAtN_three ds hpos hcard

theorem clear_four {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ 3) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ d ∈ ds, (1 : ℝ) / 4 ≤ distInt (d * σ) :=
  clear_of_existence (n := 4) (by norm_num) existenceAtN_four ds hpos hcard

theorem clear_five {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ 4) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ d ∈ ds, (1 : ℝ) / 5 ≤ distInt (d * σ) :=
  clear_of_existence (n := 5) (by norm_num) LRC.OrderFiveN.existenceAtN_five ds hpos hcard

theorem clear_six {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ 5) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ d ∈ ds, (1 : ℝ) / 6 ≤ distInt (d * σ) :=
  clear_of_existence (n := 6) (by norm_num) LRC.OrderSixN.existenceAtN_six ds hpos hcard

theorem clear_seven {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ 6) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ d ∈ ds, (1 : ℝ) / 7 ≤ distInt (d * σ) :=
  clear_of_existence (n := 7) (by norm_num) LRC.OrderSevenN.existenceAtN_seven ds hpos hcard

theorem half_clear : (1 : ℝ) / 2 ≤ distInt (1 / 2) := by
  rw [Fresh.Localisation.le_distInt_iff]
  intro z
  rcases le_or_gt z 0 with hz | hz
  · have : (z : ℝ) ≤ 0 := by exact_mod_cast hz
    rw [abs_of_nonneg (by linarith)]; linarith
  · have : (1 : ℝ) ≤ z := by exact_mod_cast hz
    rw [abs_of_nonpos (by linarith)]; linarith

/-- One disparity: the instant `1/(2 d)` puts it at distance `1/2`. -/
theorem clear_two {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ 1) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ d ∈ ds, (1 : ℝ) / 2 ≤ distInt (d * σ) := by
  by_cases hne : ds.Nonempty
  · obtain ⟨d0, hd0⟩ := hne
    have hd0pos := hpos d0 hd0
    refine ⟨1 / (2 * d0), by positivity, fun d hd => ?_⟩
    have hdd : d = d0 := Finset.card_le_one.1 hcard d hd d0 hd0
    subst hdd
    rw [show d * (1 / (2 * d)) = 1 / 2 by field_simp]
    exact half_clear
  · exact ⟨1, one_pos, fun d hd => absurd ⟨d, hd⟩ hne⟩

theorem sixClear5_proved : Fresh.AdmissibleMoreLink.SixClear5 := fun ds hpos hcard => by
  obtain ⟨σ, hσ, h⟩ := clear_six hpos hcard
  exact ⟨σ, hσ, fun d hd => by simpa using h d hd⟩

theorem sevenClear6_proved : Fresh.FreeStep.SevenClear6 := fun ds hpos hcard => by
  obtain ⟨σ, hσ, h⟩ := clear_seven hpos hcard
  exact ⟨σ, hσ, fun d hd => by simpa using h d hd⟩

#print axioms clear_two
#print axioms clear_three
#print axioms clear_six
#print axioms clear_seven
#print axioms sixClear5_proved
#print axioms sevenClear6_proved

end Fresh.NativeOrders
