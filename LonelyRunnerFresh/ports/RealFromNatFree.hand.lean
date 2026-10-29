import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Admissible
import Fresh.AdmissibleFlank
import Fresh.DistIntFract
import Fresh.NativeOrdersFree
import Fresh.FreeStepSeven
import Fresh.Nv_RealTransferN
import Fresh.Nv_OrderSevenNativeN

/-!
# Order eight on real speeds from the whole-number statement, order seven native

Written 2026-10-29.  New file; as `Fresh.RealFromNat`, with the order-seven input `LRC.OrderSevenNative.existenceAtN_seven`.
`NatLonely8` is the same proposition as `Fresh.RealFromNat.NatLonely8` (restated here so that this file does not import the BS route).
-- STANDING: OWED (NatLonely8 is not proved).  Grade [L] modulo `NatLonely8`.
-/

namespace Fresh.RealFromNatFree

open Fresh LRC.SpecN

-- STANDING: OWED
def NatLonely8 : Prop :=
  ∀ S : Finset ℕ, (∀ d ∈ S, 0 < d) → S.card ≤ 7 → ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (1 / 8 : ℝ) ≤ distInt ((d : ℝ) * t)

theorem existence8_of_nat (h : NatLonely8) : ExistenceAtN 8 := by
  have := LRC.RealTransferN.existenceAtN_of_nat (n := 5)
    (fun S hp hc => by
      obtain ⟨t, ht, hl⟩ := h S hp (by omega)
      refine ⟨t, ht, fun d hd => ?_⟩
      rw [Fresh.NativeOrdersFree.circDist_eq]
      have := hl d hd
      norm_num
      simpa using this)
    LRC.OrderSevenNative.existenceAtN_seven
  simpa using this

theorem real_clear_of_nat (h : NatLonely8) (ds : Finset ℝ) (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ 7) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ ds, (1 / 8 : ℝ) ≤ distInt (d * t) := by
  obtain ⟨t, ht, hl⟩ := existence8_of_nat h ds hpos (by simpa using hcard)
  refine ⟨t, ht, fun d hd => ?_⟩
  have := hl d hd
  rw [Fresh.NativeOrdersFree.circDist_eq] at this
  norm_num at this ⊢
  simpa using this

theorem isolation_of_natLonely8 (h : NatLonely8) {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) (k : Fin 8) : Isolation v k := by
  obtain ⟨t, ht, hl⟩ := real_clear_of_nat h (disparitySet v k) (fun d hd => Fresh.AdmissibleFlank.disp_pos hv.2.injective hd)
    (Fresh.FreeStep.disp_card_le_seven v k)
  refine ⟨t, ht, ?_⟩
  rw [Fresh.Localisation.isolatedAt_iff]
  exact hl

#print axioms existence8_of_nat
#print axioms isolation_of_natLonely8

end Fresh.RealFromNatFree
