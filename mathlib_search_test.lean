import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.ModEq
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.CircleRotation
import Mathlib.Data.Real.EReal

/-! Mathlib 4.29.1 search for CRT and equidistribution machinery -/

open MeasureTheory Set AddCircle

namespace MathLibSearch

-- Test 1: Can we access ZMod.chineseRemainder?
example (p L : ℕ) [Fact (p.Coprime L)] :
    ∃ (φ : ZMod (p * L) ≃ ZMod p × ZMod L),
    φ.symm = ZMod.chineseRemainder (by decide : p.gcd L = 1) := by
  use ZMod.chineseRemainder (by decide : p.gcd L = 1)
  rfl

-- Test 2: Does Int.fract have measure-preserving properties?
#check Int.fract
#check Int.fract_nonneg
#check Int.fract_add_int

-- Test 3: Equidistribution in AddCircle?
-- (AddCircle is the circle [0, 1) with addition mod 1)
#check AddCircle
#check AddCircle.equidistributed_of_irrational

-- Test 4: Product measure
#check MeasureTheory.Measure.prod
#check MeasureTheory.volume

-- Test 5: Fubini's theorem
#check MeasureTheory.integral_prod_mul
#check MeasureTheory.lintegral_prod_mul

-- Test 6: Measure of empty set
#check MeasureTheory.measure_empty
#check Set.measure_empty

-- Test 7: Can we construct measure-preserving map?
#check MeasureTheory.MeasurePreserving
#check MeasureTheory.QuasiMeasurePreserving

-- Test 8: Measure restriction and scaling
#check MeasureTheory.measure_smul_le
#check Set.indicator

-- Test 9: Coprimality lemmas
#check Nat.Coprime
#check Nat.coprime_iff_gcd_eq_one
#check Nat.Coprime.mul_right

-- Test 10: lcm properties
#check Nat.lcm_dvd_iff_dvd_mul
#check Finset.lcm_le_iff_forall_dvd

end MathLibSearch
