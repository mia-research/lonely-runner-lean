import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Admissible
import Fresh.AdmissibleFlank
import Fresh.DistIntFract
import Fresh.NativeOrders
import Fresh.FreeStepSeven
import Fresh.Nv_RealTransferN
import Fresh.Nv_RealSevenN

/-!
# Order eight on real speeds from the whole-number statement, using the owner's native lower orders

Written 2026-10-25.  New file.  `LRC.RealTransferN.existenceAtN_of_nat` (ported, `Nv_RealTransferN`, the owner's framework form: one exact merge and the stepping margin) takes integer existence at order `n + 3` and real existence at order `n + 2`
to real existence at order `n + 3`.  At `n = 5` the preceding real order is seven, native (`Nv_RealSevenN.existenceAtN_seven`).  So the real statement at eight runners follows from
`NatLonely8`: every set of at most seven positive whole numbers has an instant at which each is `1/8`-clear.  **This is an integer/commensurable statement and is recorded as such** (owner 2026-10-09: integer results must say so; this theorem
does not change how arrangements are studied, it records that the real obligation is carried by `NatLonely8`).  `NatLonely8` is `-- STANDING: OWED`.
`isolation_of_natLonely8`: with it, every ordered arrangement is isolated for every subject.  Grade [L] modulo `NatLonely8`.
-/

namespace Fresh.RealFromNat

open Fresh LRC.SpecN

-- STANDING: OWED
def NatLonely8 : Prop :=
  ∀ S : Finset ℕ, (∀ d ∈ S, 0 < d) → S.card ≤ 7 → ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (1 / 8 : ℝ) ≤ distInt ((d : ℝ) * t)

theorem existence8_of_nat (h : NatLonely8) : ExistenceAtN 8 := by
  have := LRC.RealTransferN.existenceAtN_of_nat (n := 5)
    (fun S hp hc => by
      obtain ⟨t, ht, hl⟩ := h S hp (by omega)
      refine ⟨t, ht, fun d hd => ?_⟩
      rw [Fresh.NativeOrders.circDist_eq]
      have := hl d hd
      norm_num
      simpa using this)
    LRC.OrderSevenN.existenceAtN_seven
  simpa using this

theorem real_clear_of_nat (h : NatLonely8) (ds : Finset ℝ) (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ 7) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ ds, (1 / 8 : ℝ) ≤ distInt (d * t) := by
  obtain ⟨t, ht, hl⟩ := existence8_of_nat h ds hpos (by simpa using hcard)
  refine ⟨t, ht, fun d hd => ?_⟩
  have := hl d hd
  rw [Fresh.NativeOrders.circDist_eq] at this
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

end Fresh.RealFromNat
