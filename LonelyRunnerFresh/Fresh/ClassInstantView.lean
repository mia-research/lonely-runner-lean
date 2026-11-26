import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.HoldTwoScale

/-!
# A frozen set at a frozen reading's class-1 instant, in view terms (E747)

Written 2026-11-01.  New file; nothing existing is edited.  `lonely_two_scale` (`HoldTwoScale`) takes as a hypothesis
that the frozen set is clear at a class-1 instant `(8M+1)/(8d)` of a frozen reading `d`.  Here that test is read off
the AP/grid view through `d` (the grid of step `d`, E279): reading `f` has grid index `n = ⌊f/d + 1/2⌋` and deviation
`ε = f/d - n`, and at `(8M+1)/(8d)` it sits where `((n mod 8) + (8M+1)·ε)/8` sits (`class_instant_position`).  So:

* the residue is `n mod 8` on the grid through `d`, unchanged by `M` (since `8M + 1 ≡ 1`);
* the deviation is multiplied by `8M + 1`;
* `f` is clear there iff `(n mod 8) + (8M+1)·ε` is at least 1 from every multiple of 8 (`clear_at_class_instant_iff`).

This is `spine_reduce` (`LRC/Cascade/Iteration.lean`) at the instant `8M+1` eighths of scale `d`.  Grades: [L].
-/

namespace Fresh.OneMover

open Fresh

/-- Grid index of reading `f` on the grid of step `d`: the nearest integer to `f/d`, ties up. -/
noncomputable def gIdx (d f : ℝ) : ℤ := ⌊f / d + 1 / 2⌋

/-- Deviation of `f` from its grid point, in units of `d`. -/
noncomputable def gDev (d f : ℝ) : ℝ := f / d - gIdx d f

theorem gDev_mem (d f : ℝ) : -(1 / 2 : ℝ) ≤ gDev d f ∧ gDev d f < 1 / 2 := by
  unfold gDev gIdx
  constructor
  · have := Int.floor_le (f / d + 1 / 2); linarith
  · have := Int.lt_floor_add_one (f / d + 1 / 2); linarith

/-- **Position at the class-1 instant.**  At `(8M+1)/(8d)`, reading `f` sits at
`((n mod 8) + (8M+1)·ε)/8` plus an integer, with `(n, ε)` its view on the grid through `d`. -/
theorem class_instant_position (d f : ℝ) (hd : d ≠ 0) (M : ℤ) :
    ∃ z : ℤ, f * ((8 * (M : ℝ) + 1) / (8 * d)) =
      ((((gIdx d f) % 8 : ℤ) : ℝ) + (8 * (M : ℝ) + 1) * gDev d f) / 8 + z := by
  have hf : f = d * ((gIdx d f : ℝ) + gDev d f) := by unfold gDev; field_simp; ring
  set n := gIdx d f with hn
  set e := gDev d f with he
  refine ⟨M * n + n / 8, ?_⟩
  have hdiv : ((n % 8 : ℤ) : ℝ) + 8 * ((n / 8 : ℤ) : ℝ) = (n : ℝ) := by
    exact_mod_cast Int.emod_add_mul_ediv n 8
  have lhs : f * ((8 * (M : ℝ) + 1) / (8 * d)) = (8 * (M : ℝ) + 1) * ((n : ℝ) + e) / 8 := by
    rw [hf]; field_simp
  rw [lhs]; push_cast
  linear_combination (-(8 * (M : ℝ) + 1) / 8) * hdiv + (M : ℝ) * hdiv

/-- **Clear at the class-1 instant iff the view through `d` says so.** -/
theorem clear_at_class_instant_iff (d f : ℝ) (hd : d ≠ 0) (M : ℤ) :
    distInt (f * ((8 * (M : ℝ) + 1) / (8 * d))) =
      distInt (((((gIdx d f) % 8 : ℤ) : ℝ) + (8 * (M : ℝ) + 1) * gDev d f) / 8) := by
  obtain ⟨z, hz⟩ := class_instant_position d f hd M
  rw [hz, Cascade.distInt_add_int]

/-- **The frozen set at the class-1 instant**: clear iff every reading's residue on the grid through `d`, plus
`8M + 1` times its deviation, is clear in eighths.  This is the hypothesis `hF2` of `lonely_two_scale`. -/
theorem frozen_clear_at_class_instant_iff (F : Finset ℝ) (d : ℝ) (hd : d ≠ 0) (M : ℤ) :
    (∀ f ∈ F, (1 / 8 : ℝ) ≤ distInt (f * ((8 * (M : ℝ) + 1) / (8 * d)))) ↔
      ∀ f ∈ F, (1 / 8 : ℝ) ≤
        distInt (((((gIdx d f) % 8 : ℤ) : ℝ) + (8 * (M : ℝ) + 1) * gDev d f) / 8) := by
  refine forall_congr' fun f => imp_congr_right fun _ => ?_
  rw [clear_at_class_instant_iff d f hd M]

/-- The reading `d` itself sits at `1/8` at every class-1 instant of its own scale: on its leaving edge. -/
theorem self_at_class_instant (d : ℝ) (hd : d ≠ 0) (M : ℤ) :
    distInt (d * ((8 * (M : ℝ) + 1) / (8 * d))) = 1 / 8 := by
  have e : d * ((8 * (M : ℝ) + 1) / (8 * d)) = 1 / 8 + ((M : ℤ) : ℝ) := by field_simp; ring
  rw [e, Cascade.distInt_eighth_add_int]

/-- **The class-1 instants of `d` are a rotation by the deviation.**  At `(8M+1)/(8d)` reading `f` sits at
`f/(8d) + M·ε` plus an integer, `ε = gDev d f`: as `M` steps by 1, the position turns by `ε`. -/
theorem class_instant_rotation (d f : ℝ) (hd : d ≠ 0) (M : ℤ) :
    f * ((8 * (M : ℝ) + 1) / (8 * d)) = f / (8 * d) + (M : ℝ) * gDev d f + ((M * gIdx d f : ℤ) : ℝ) := by
  unfold gDev; push_cast; field_simp; ring

/-- The class-1 instants at which reading `f` is clear: the good `M` for `f` on the grid through `d`. -/
-- STANDING: DEFINITION
def GoodM (d f : ℝ) (M : ℤ) : Prop := (1 / 8 : ℝ) ≤ distInt (f / (8 * d) + (M : ℝ) * gDev d f)

/-- **Clear at the class-1 instant `M` iff `M` is good for `f`.** -/
theorem clear_at_class_instant_iff_goodM (d f : ℝ) (hd : d ≠ 0) (M : ℤ) :
    (1 / 8 : ℝ) ≤ distInt (f * ((8 * (M : ℝ) + 1) / (8 * d))) ↔ GoodM d f M := by
  unfold GoodM
  rw [class_instant_rotation d f hd M, Cascade.distInt_add_int]

/-- **The frozen set at the class-1 instant `M` of `d`**: clear iff `M` is good for every frozen reading. -/
theorem frozen_clear_iff_goodM (F : Finset ℝ) (d : ℝ) (hd : d ≠ 0) (M : ℤ) :
    (∀ f ∈ F, (1 / 8 : ℝ) ≤ distInt (f * ((8 * (M : ℝ) + 1) / (8 * d)))) ↔ ∀ f ∈ F, GoodM d f M := by
  refine forall_congr' fun f => imp_congr_right fun _ => ?_
  exact clear_at_class_instant_iff_goodM d f hd M

/-- A reading on the grid through `d` (`ε = 0`) is good for every `M` or for none: its position `f/(8d)` does not
turn. -/
theorem goodM_of_dev_zero (d f : ℝ) (h0 : gDev d f = 0) (M N : ℤ) : GoodM d f M ↔ GoodM d f N := by
  unfold GoodM; rw [h0]; simp

#print axioms class_instant_rotation
#print axioms clear_at_class_instant_iff_goodM
#print axioms frozen_clear_iff_goodM
#print axioms goodM_of_dev_zero
#print axioms gDev_mem
#print axioms class_instant_position
#print axioms clear_at_class_instant_iff
#print axioms frozen_clear_at_class_instant_iff
#print axioms self_at_class_instant

end Fresh.OneMover
