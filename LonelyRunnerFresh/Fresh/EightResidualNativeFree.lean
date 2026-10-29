import Mathlib
import Fresh.Framework
import Fresh.DistIntFract
import Fresh.NativeOrdersFree
import Fresh.Nv_OrderEightCasesNFree
import Fresh.RealFromNatFree

/-!
# The order-eight residual, native in `Fresh/`

Written 2026-10-25.  New file.  `LRC.OrderEightN.EightResidual` (18 fields; ported in `Nv_OrderEightCasesN`, the owner's native case list: halving, the first reading, `1/q` rules, the descent, the free flank, the largest multiple,
rational openings, the fast pair, the block split, one free reading, ...) is now a structure in `Fresh/`, and so is `lonely_eight_nat_of_residual`: every whole-number set of at most seven positive numbers is lonely at `1/8` once every
`EightResidual` set is.  `ResidualLonely8` is that last statement (`-- STANDING: OWED`).  `natLonely8_of_residual` and `isolation_of_residual` assemble it with `RealFromNat`: **the real conjecture at eight runners, for every ordered
arrangement, follows from `ResidualLonely8`** (an integer statement, recorded as such).  `residualLonely8_of_natLonely8` is the converse.  Grade [L] modulo `ResidualLonely8`.
-/

namespace Fresh.EightResidualNative

open Fresh LRC.OrderEightN

-- STANDING: OWED
def ResidualLonely8 : Prop :=
  ∀ R : Finset ℕ, (∀ d ∈ R, 0 < d) → EightResidual R → ∃ t : ℝ, 0 < t ∧ ∀ d ∈ R, (1 / 8 : ℝ) ≤ distInt ((d : ℝ) * t)

theorem natLonely8_of_residual (h : ResidualLonely8) : Fresh.RealFromNatFree.NatLonely8 := by
  intro S hpos hcard
  have hres : ∀ R : Finset ℕ, (∀ d ∈ R, 0 < d) → EightResidual R →
      ∃ t : ℝ, 0 < t ∧ ∀ d ∈ R, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
    intro R hp hR
    obtain ⟨t, ht, hl⟩ := h R hp hR
    refine ⟨t, ht, fun d hd => ?_⟩
    rw [Fresh.NativeOrdersFree.circDist_eq]
    simpa using hl d hd
  obtain ⟨t, ht, hl⟩ := lonely_eight_nat_of_residual hres (∑ d ∈ S, d) S rfl hpos hcard
  refine ⟨t, ht, fun d hd => ?_⟩
  have := hl d hd
  rw [Fresh.NativeOrdersFree.circDist_eq] at this
  simpa using this

theorem residualLonely8_of_natLonely8 (h : Fresh.RealFromNatFree.NatLonely8) : ResidualLonely8 := by
  intro R hp hcard
  exact h R hp (by
    have := hcard.card_eq
    omega)

theorem isolation_of_residual (h : ResidualLonely8) {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) (k : Fin 8) :
    Isolation v k :=
  Fresh.RealFromNatFree.isolation_of_natLonely8 (natLonely8_of_residual h) hv k

#print axioms natLonely8_of_residual
#print axioms isolation_of_residual

end Fresh.EightResidualNative
