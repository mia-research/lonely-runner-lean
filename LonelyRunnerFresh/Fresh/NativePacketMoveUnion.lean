import Fresh.Cascade

namespace Fresh.NativePacketMoveUnion

open Fresh Cascade
open scoped Classical

private theorem captured_bound {packet : Finset ℝ} (hm : IsMove packet T U)
    {d : ℝ} (hd : d ∈ packet) (hw : InWay d T) : nextOpening d T ≤ U := by
  rcases hm with ⟨h, _⟩ | ⟨_, _, _, _, h⟩
  · exact (h d hd hw).elim
  · exact h d hd hw

private theorem take_later {a b : Finset ℝ} (hb : ∀ d ∈ b, 0 < d) {T U V : ℝ}
    (hma : IsMove a T U) (hmb : IsMove b T V) (hle : V ≤ U) :
    IsMove (a ∪ b) T U := by
  rcases hma with ⟨hclear, rfl⟩ | ⟨d, hd, hwd, he, hmax⟩
  · have hv : V = _ := le_antisymm hle (le_of_isMove hb hmb)
    rw [hv] at hmb
    have hc := (isMove_self_iff hb).mp hmb
    refine Or.inl ⟨?_, rfl⟩
    intro d hd hw
    rcases Finset.mem_union.mp hd with hd | hd
    · exact hclear d hd hw
    · exact (not_inWay_iff.mpr (hc d hd)) hw
  · refine Or.inr ⟨d, Finset.mem_union_left b hd, hwd, he, ?_⟩
    intro r hr hw
    rcases Finset.mem_union.mp hr with hr | hr
    · exact hmax r hr hw
    · exact (captured_bound hmb hr hw).trans hle

/-- At the same origin, two packet moves combine by maximum. Each
packet can have its own lap, and equality retains the common exit. -/
theorem step_union {a b : Finset ℝ} (ha : ∀ d ∈ a, 0 < d)
    (hb : ∀ d ∈ b, 0 < d) (T : ℝ) :
    step (a ∪ b) T = max (step a T) (step b T) := by
  apply isMove_unique (isMove_step _ _)
  rcases le_total (step a T) (step b T) with h | h
  · rw [max_eq_right h, Finset.union_comm]
    exact take_later ha (isMove_step _ _) (isMove_step _ _) h
  · rw [max_eq_left h]
    exact take_later hb (isMove_step _ _) (isMove_step _ _) h

#print axioms step_union

end Fresh.NativePacketMoveUnion
