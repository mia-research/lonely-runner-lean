import Mathlib
import Fresh.Framework
import Fresh.DistIntFract
import Fresh.Nv_OrdersThreeFourN
import Fresh.Nv_RealFiveN
import Fresh.Nv_RealSixN
import Fresh.Nv_OrderSevenNativeN
import Fresh.FastPairConverse
import Fresh.FreeStepSeven

/-!
# Native lower orders, with order seven from the certificate-based native proof

Written 2026-10-29.  New file; the statements are those of `Fresh.NativeOrders`, but order seven here is
`LRC.OrderSevenNative.existenceAtN_seven` (the owner's grid/fold/digit-extension argument with kernel-checked certificates,
ported as `Nv_OrderSevenNativeN`), not `LRC.OrderSevenN.existenceAtN_seven` (the Barajas-Serra route).  The import closure of this module
contains no `Nv_OrderSevenN` module and no BHK module.  Grade [L].
-/

namespace Fresh.NativeOrdersFree

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

theorem clear_six {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ 5) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ d ∈ ds, (1 : ℝ) / 6 ≤ distInt (d * σ) :=
  clear_of_existence (n := 6) (by norm_num) LRC.OrderSixN.existenceAtN_six ds hpos hcard

theorem clear_seven {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ 6) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ d ∈ ds, (1 : ℝ) / 7 ≤ distInt (d * σ) :=
  clear_of_existence (n := 7) (by norm_num) LRC.OrderSevenNative.existenceAtN_seven ds hpos hcard

theorem sevenClear6_proved : Fresh.FreeStep.SevenClear6 := fun ds hpos hcard => by
  obtain ⟨σ, hσ, h⟩ := clear_seven hpos hcard
  exact ⟨σ, hσ, fun d hd => by simpa using h d hd⟩

/-- The two order-seven statements are the same proposition, so the native proof also gives the BS-route statement. -/
theorem existenceAtN_seven_native : ExistenceAtN 7 := LRC.OrderSevenNative.existenceAtN_seven

#print axioms clear_seven
#print axioms sevenClear6_proved

end Fresh.NativeOrdersFree
