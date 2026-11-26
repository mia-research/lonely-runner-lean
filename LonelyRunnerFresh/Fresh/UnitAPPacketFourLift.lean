import Fresh.UnitAPPacketFourCells

/-! Whole unit-step laps and anchor return laps only add original integer
phase labels. The four closed opening-cell rules therefore lift unchanged. -/
namespace Fresh.UnitAPPacketFourLift
open Fresh Fresh.Localisation Fresh.UnitAPPacketFourCells

def Cell (a : Fin 4) (theta : ℝ) : Prop :=
  match a.val with
  | 0 => Cell0 theta
  | 1 => Cell1 theta
  | 2 => Cell2 theta
  | _ => Cell3 theta

theorem cell_iff (a : Fin 4) (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    Cell a theta ↔ ∀ i : Fin 4, (1/8 : ℝ) ≤ distInt (1/8+((i : ℝ)-(a : ℝ))*theta) := by
  fin_cases a
  · change Cell0 theta ↔ _
    norm_num only [Fin.val_mk, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
    exact ⟨cell0_clear theta,clear0_cell theta h0 h1⟩
  · change Cell1 theta ↔ _
    norm_num only [Fin.val_mk, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
    exact ⟨cell1_clear theta,clear1_cell theta h0 h1⟩
  · change Cell2 theta ↔ _
    norm_num only [Fin.val_mk, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
    exact ⟨cell2_clear theta,clear2_cell theta h0 h1⟩
  · change Cell3 theta ↔ _
    norm_num only [Fin.val_mk, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
    exact ⟨cell3_clear theta,clear3_cell theta h0 h1⟩

theorem integer_lift (i a : ℤ) (q h : ℤ) (tau : ℝ) :
    distInt ((q : ℝ)+1/8+((i : ℝ)-(a : ℝ))*tau)=
      distInt (1/8+((i : ℝ)-(a : ℝ))*(tau-(h : ℝ))) := by
  have he : (q : ℝ)+1/8+((i : ℝ)-(a : ℝ))*tau =
      (1/8+((i : ℝ)-(a : ℝ))*(tau-(h : ℝ)))+((q+(i-a)*h : ℤ) : ℝ) := by
    push_cast; ring
  rw [he,distInt_add_int]

theorem lifted_iff (a : Fin 4) (q h : ℤ) (tau : ℝ)
    (h0 : 0 ≤ tau-(h : ℝ)) (h1 : tau-(h : ℝ) ≤ 1) :
    Cell a (tau-(h : ℝ)) ↔
      ∀ i : Fin 4, (1/8 : ℝ) ≤ distInt ((q : ℝ)+1/8+((i : ℝ)-(a : ℝ))*tau) := by
  rw [cell_iff a _ h0 h1]
  have hi (i : Fin 4) := integer_lift ((i : ℕ) : ℤ) ((a : ℕ) : ℤ) q h tau
  simp only [Int.cast_natCast] at hi
  simp_rw [hi]

#print axioms cell_iff
#print axioms integer_lift
#print axioms lifted_iff
end Fresh.UnitAPPacketFourLift
