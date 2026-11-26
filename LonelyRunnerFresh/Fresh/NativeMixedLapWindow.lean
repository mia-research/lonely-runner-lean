import Fresh.NativePacketMoveUnion
import Fresh.Localisation

namespace Fresh.NativeMixedLapWindow

open Fresh Cascade Localisation
open scoped Classical

/-- One reading in a window containing a single capture interval.
Both endpoints of the capture interval give a fixed point. -/
theorem single_step {d U : ℝ} (j : ℤ)
    (hl : (j : ℝ) - 7 / 8 ≤ d * U) (hu : d * U ≤ (j : ℝ) + 7 / 8) :
    step ({d} : Finset ℝ) U =
      if (j : ℝ) - 1 / 8 < d * U ∧ d * U < (j : ℝ) + 1 / 8
      then ((j : ℝ) + 1 / 8) / d else U := by
  apply isMove_unique (isMove_step _ _)
  split
  · rename_i h
    have hc : |d * U - (j : ℝ)| < 1 / 8 := abs_lt.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
    have ho := nextOpening_eq hc
    refine Or.inr ⟨d, by simp, (Cascade.distInt_le _ j).trans_lt hc, ho.symm, ?_⟩
    intro r hr _
    simp only [Finset.mem_singleton] at hr
    simpa only [hr] using ho.le
  · rename_i h
    have hc : (1 / 8 : ℝ) ≤ Fresh.distInt (d * U) := by
      by_cases he : (j : ℝ) - 1 / 8 < d * U
      · exact clear_of_window j (le_of_not_gt (fun hx => h ⟨he, hx⟩)) hu
      · apply clear_of_window (j - 1) <;> push_cast <;> linarith [le_of_not_gt he]
    refine Or.inl ⟨?_, rfl⟩
    intro r hr
    simp only [Finset.mem_singleton] at hr
    exact not_inWay_iff.mpr (hr ▸ hc)

/-- Entry tests at the *current* opening give the combined move for
two readings on arbitrary symbolic laps. -/
theorem mixed_step {core : Finset ℝ} (hpos : ∀ r ∈ core, 0 < r)
    {a b U : ℝ} (ha : 0 < a) (hb : 0 < b) (j k : ℤ) (hc : LonelyAt core U)
    (hla : (j : ℝ) - 7 / 8 ≤ a * U) (hua : a * U ≤ (j : ℝ) + 7 / 8)
    (hlb : (k : ℝ) - 7 / 8 ≤ b * U) (hub : b * U ≤ (k : ℝ) + 7 / 8) :
    step (core ∪ (({a} : Finset ℝ) ∪ {b})) U =
      max (if (j : ℝ) - 1 / 8 < a * U ∧ a * U < (j : ℝ) + 1 / 8
        then ((j : ℝ) + 1 / 8) / a else U)
      (if (k : ℝ) - 1 / 8 < b * U ∧ b * U < (k : ℝ) + 1 / 8
        then ((k : ℝ) + 1 / 8) / b else U) := by
  have pa : ∀ d ∈ ({a} : Finset ℝ), 0 < d := by simpa using ha
  have pb : ∀ d ∈ ({b} : Finset ℝ), 0 < d := by simpa using hb
  have pu : ∀ d ∈ (({a} : Finset ℝ) ∪ {b}), 0 < d := by
    intro d hd
    exact (Finset.mem_union.mp hd).elim (pa d) (pb d)
  have hf : step core U = U :=
    isMove_unique (isMove_step _ _) ((isMove_self_iff hpos).2 hc)
  rw [NativePacketMoveUnion.step_union hpos pu, hf,
    max_eq_right (le_of_isMove pu (isMove_step _ _)),
    NativePacketMoveUnion.step_union pa pb, single_step j hla hua, single_step k hlb hub]

/-- A reading enters at another reading's named exit exactly when
the two starting-reading comparisons place it between the open edges. -/
theorem delayed_entry {a b : ℝ} (ha : 0 < a) (j k : ℤ) :
    ((k : ℝ) - 1 / 8 < b * (((j : ℝ) + 1 / 8) / a) ∧
      b * (((j : ℝ) + 1 / 8) / a) < (k : ℝ) + 1 / 8) ↔
    ((k : ℝ) - 1 / 8) * a < ((j : ℝ) + 1 / 8) * b ∧
      ((j : ℝ) + 1 / 8) * b < ((k : ℝ) + 1 / 8) * a := by
  rw [← mul_div_assoc, lt_div_iff₀ ha, div_lt_iff₀ ha, mul_comm b]

#print axioms single_step
#print axioms mixed_step
#print axioms delayed_entry

end Fresh.NativeMixedLapWindow
