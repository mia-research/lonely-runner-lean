import Fresh.UnitAPPacketFourLift

/-! Exact boundary cells of three retained unit AP readings at a named
opening. No arbitrary-time selector or existence budget is introduced. -/
namespace Fresh.UnitAPPacketThreeCells
open Fresh Fresh.Localisation
set_option maxHeartbeats 4000000

def Cell0 (theta : ℝ) : Prop :=
  (0 ≤ theta ∧ theta ≤ (3/8 : ℝ)) ∨
  ((1/2 : ℝ) ≤ theta ∧ theta ≤ (3/4 : ℝ)) ∨
  (1 ≤ theta ∧ theta ≤ 1)

theorem cell0_clear (theta : ℝ) (hc : Cell0 theta) :
    ∀ i : Fin 3, (1/8 : ℝ) ≤ distInt (1/8+((i : ℝ)-0)*theta) := by
  rcases hc with h|h|h
  · intro i
    fin_cases i
    · apply clear_of_window (0 : ℤ) <;> norm_num <;> linarith [h.1,h.2]
    · apply clear_of_window (0 : ℤ) <;> norm_num <;> linarith [h.1,h.2]
    · apply clear_of_window (0 : ℤ) <;> norm_num <;> linarith [h.1,h.2]
  · intro i
    fin_cases i
    · apply clear_of_window (0 : ℤ) <;> norm_num <;> linarith [h.1,h.2]
    · apply clear_of_window (0 : ℤ) <;> norm_num <;> linarith [h.1,h.2]
    · apply clear_of_window (1 : ℤ) <;> norm_num <;> linarith [h.1,h.2]
  · intro i
    fin_cases i
    · apply clear_of_window (0 : ℤ) <;> norm_num <;> linarith [h.1,h.2]
    · apply clear_of_window (1 : ℤ) <;> norm_num <;> linarith [h.1,h.2]
    · apply clear_of_window (2 : ℤ) <;> norm_num <;> linarith [h.1,h.2]

theorem clear0_cell (theta : ℝ) (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1)
    (hc : ∀ i : Fin 3, (1/8 : ℝ) ≤ distInt (1/8+((i : ℝ)-0)*theta)) : Cell0 theta := by
  let n0 : ℤ := ⌊(1/8 : ℝ)+(1 : ℝ)*theta⌋
  have hc0 : (1/8 : ℝ) ≤ distInt (1/8+(1 : ℝ)*theta) := by
    have hh := hc (1 : Fin 3)
    norm_num at hh ⊢
    exact hh
  have hf0 := (clear_iff_fract _).mp hc0
  change (1/8 : ℝ) ≤ 1/8+(1 : ℝ)*theta-(n0 : ℝ) ∧
    1/8+(1 : ℝ)*theta-(n0 : ℝ) ≤ 7/8 at hf0
  have hn0loR : (-1 : ℝ) < n0 := by linarith [hf0.2]
  have hn0hiR : (n0 : ℝ) < 2 := by linarith [hf0.1]
  have hn0loZ : (-1 : ℤ) < n0 := by exact_mod_cast hn0loR
  have hn0hiZ : n0 < (2 : ℤ) := by exact_mod_cast hn0hiR
  have hn0lo : (0 : ℤ) ≤ n0 := by omega
  have hn0hi : n0 ≤ (1 : ℤ) := by omega
  let n1 : ℤ := ⌊(1/8 : ℝ)+(2 : ℝ)*theta⌋
  have hc1 : (1/8 : ℝ) ≤ distInt (1/8+(2 : ℝ)*theta) := by
    have hh := hc (2 : Fin 3)
    norm_num at hh ⊢
    exact hh
  have hf1 := (clear_iff_fract _).mp hc1
  change (1/8 : ℝ) ≤ 1/8+(2 : ℝ)*theta-(n1 : ℝ) ∧
    1/8+(2 : ℝ)*theta-(n1 : ℝ) ≤ 7/8 at hf1
  have hn1loR : (-1 : ℝ) < n1 := by linarith [hf1.2]
  have hn1hiR : (n1 : ℝ) < 3 := by linarith [hf1.1]
  have hn1loZ : (-1 : ℤ) < n1 := by exact_mod_cast hn1loR
  have hn1hiZ : n1 < (3 : ℤ) := by exact_mod_cast hn1hiR
  have hn1lo : (0 : ℤ) ≤ n1 := by omega
  have hn1hi : n1 ≤ (2 : ℤ) := by omega
  unfold Cell0
  interval_cases n0 <;> interval_cases n1 <;> norm_num at hf0 hf1
  all_goals first
    | exact Or.inl (⟨by linarith,by linarith⟩)
    | exact Or.inr (Or.inl (⟨by linarith,by linarith⟩))
    | exact Or.inr (Or.inr (⟨by linarith,by linarith⟩))
    | exfalso; linarith

def Cell1 (theta : ℝ) : Prop :=
  (0 ≤ theta ∧ theta ≤ 0) ∨
  ((1/4 : ℝ) ≤ theta ∧ theta ≤ (3/4 : ℝ)) ∨
  (1 ≤ theta ∧ theta ≤ 1)

theorem cell1_clear (theta : ℝ) (hc : Cell1 theta) :
    ∀ i : Fin 3, (1/8 : ℝ) ≤ distInt (1/8+((i : ℝ)-1)*theta) := by
  rcases hc with h|h|h
  · intro i
    fin_cases i
    · apply clear_of_window (0 : ℤ) <;> norm_num <;> linarith [h.1,h.2]
    · apply clear_of_window (0 : ℤ) <;> norm_num <;> linarith [h.1,h.2]
    · apply clear_of_window (0 : ℤ) <;> norm_num <;> linarith [h.1,h.2]
  · intro i
    fin_cases i
    · apply clear_of_window (-1 : ℤ) <;> norm_num <;> linarith [h.1,h.2]
    · apply clear_of_window (0 : ℤ) <;> norm_num <;> linarith [h.1,h.2]
    · apply clear_of_window (0 : ℤ) <;> norm_num <;> linarith [h.1,h.2]
  · intro i
    fin_cases i
    · apply clear_of_window (-1 : ℤ) <;> norm_num <;> linarith [h.1,h.2]
    · apply clear_of_window (0 : ℤ) <;> norm_num <;> linarith [h.1,h.2]
    · apply clear_of_window (1 : ℤ) <;> norm_num <;> linarith [h.1,h.2]

theorem clear1_cell (theta : ℝ) (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1)
    (hc : ∀ i : Fin 3, (1/8 : ℝ) ≤ distInt (1/8+((i : ℝ)-1)*theta)) : Cell1 theta := by
  let n0 : ℤ := ⌊(1/8 : ℝ)+(-1 : ℝ)*theta⌋
  have hc0 : (1/8 : ℝ) ≤ distInt (1/8+(-1 : ℝ)*theta) := by
    have hh := hc (0 : Fin 3)
    norm_num at hh ⊢
    exact hh
  have hf0 := (clear_iff_fract _).mp hc0
  change (1/8 : ℝ) ≤ 1/8+(-1 : ℝ)*theta-(n0 : ℝ) ∧
    1/8+(-1 : ℝ)*theta-(n0 : ℝ) ≤ 7/8 at hf0
  have hn0loR : (-2 : ℝ) < n0 := by linarith [hf0.2]
  have hn0hiR : (n0 : ℝ) < 1 := by linarith [hf0.1]
  have hn0loZ : (-2 : ℤ) < n0 := by exact_mod_cast hn0loR
  have hn0hiZ : n0 < (1 : ℤ) := by exact_mod_cast hn0hiR
  have hn0lo : (-1 : ℤ) ≤ n0 := by omega
  have hn0hi : n0 ≤ (0 : ℤ) := by omega
  let n1 : ℤ := ⌊(1/8 : ℝ)+(1 : ℝ)*theta⌋
  have hc1 : (1/8 : ℝ) ≤ distInt (1/8+(1 : ℝ)*theta) := by
    have hh := hc (2 : Fin 3)
    norm_num at hh ⊢
    exact hh
  have hf1 := (clear_iff_fract _).mp hc1
  change (1/8 : ℝ) ≤ 1/8+(1 : ℝ)*theta-(n1 : ℝ) ∧
    1/8+(1 : ℝ)*theta-(n1 : ℝ) ≤ 7/8 at hf1
  have hn1loR : (-1 : ℝ) < n1 := by linarith [hf1.2]
  have hn1hiR : (n1 : ℝ) < 2 := by linarith [hf1.1]
  have hn1loZ : (-1 : ℤ) < n1 := by exact_mod_cast hn1loR
  have hn1hiZ : n1 < (2 : ℤ) := by exact_mod_cast hn1hiR
  have hn1lo : (0 : ℤ) ≤ n1 := by omega
  have hn1hi : n1 ≤ (1 : ℤ) := by omega
  unfold Cell1
  interval_cases n0 <;> interval_cases n1 <;> norm_num at hf0 hf1
  all_goals first
    | exact Or.inl (⟨by linarith,by linarith⟩)
    | exact Or.inr (Or.inl (⟨by linarith,by linarith⟩))
    | exact Or.inr (Or.inr (⟨by linarith,by linarith⟩))
    | exfalso; linarith

def Cell2 (theta : ℝ) : Prop :=
  (0 ≤ theta ∧ theta ≤ 0) ∨
  ((1/4 : ℝ) ≤ theta ∧ theta ≤ (1/2 : ℝ)) ∨
  ((5/8 : ℝ) ≤ theta ∧ theta ≤ 1)

theorem cell2_clear (theta : ℝ) (hc : Cell2 theta) :
    ∀ i : Fin 3, (1/8 : ℝ) ≤ distInt (1/8+((i : ℝ)-2)*theta) := by
  rcases hc with h|h|h
  · intro i
    fin_cases i
    · apply clear_of_window (0 : ℤ) <;> norm_num <;> linarith [h.1,h.2]
    · apply clear_of_window (0 : ℤ) <;> norm_num <;> linarith [h.1,h.2]
    · apply clear_of_window (0 : ℤ) <;> norm_num <;> linarith [h.1,h.2]
  · intro i
    fin_cases i
    · apply clear_of_window (-1 : ℤ) <;> norm_num <;> linarith [h.1,h.2]
    · apply clear_of_window (-1 : ℤ) <;> norm_num <;> linarith [h.1,h.2]
    · apply clear_of_window (0 : ℤ) <;> norm_num <;> linarith [h.1,h.2]
  · intro i
    fin_cases i
    · apply clear_of_window (-2 : ℤ) <;> norm_num <;> linarith [h.1,h.2]
    · apply clear_of_window (-1 : ℤ) <;> norm_num <;> linarith [h.1,h.2]
    · apply clear_of_window (0 : ℤ) <;> norm_num <;> linarith [h.1,h.2]

theorem clear2_cell (theta : ℝ) (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1)
    (hc : ∀ i : Fin 3, (1/8 : ℝ) ≤ distInt (1/8+((i : ℝ)-2)*theta)) : Cell2 theta := by
  let n0 : ℤ := ⌊(1/8 : ℝ)+(-2 : ℝ)*theta⌋
  have hc0 : (1/8 : ℝ) ≤ distInt (1/8+(-2 : ℝ)*theta) := by
    have hh := hc (0 : Fin 3)
    norm_num at hh ⊢
    exact hh
  have hf0 := (clear_iff_fract _).mp hc0
  change (1/8 : ℝ) ≤ 1/8+(-2 : ℝ)*theta-(n0 : ℝ) ∧
    1/8+(-2 : ℝ)*theta-(n0 : ℝ) ≤ 7/8 at hf0
  have hn0loR : (-3 : ℝ) < n0 := by linarith [hf0.2]
  have hn0hiR : (n0 : ℝ) < 1 := by linarith [hf0.1]
  have hn0loZ : (-3 : ℤ) < n0 := by exact_mod_cast hn0loR
  have hn0hiZ : n0 < (1 : ℤ) := by exact_mod_cast hn0hiR
  have hn0lo : (-2 : ℤ) ≤ n0 := by omega
  have hn0hi : n0 ≤ (0 : ℤ) := by omega
  let n1 : ℤ := ⌊(1/8 : ℝ)+(-1 : ℝ)*theta⌋
  have hc1 : (1/8 : ℝ) ≤ distInt (1/8+(-1 : ℝ)*theta) := by
    have hh := hc (1 : Fin 3)
    norm_num at hh ⊢
    exact hh
  have hf1 := (clear_iff_fract _).mp hc1
  change (1/8 : ℝ) ≤ 1/8+(-1 : ℝ)*theta-(n1 : ℝ) ∧
    1/8+(-1 : ℝ)*theta-(n1 : ℝ) ≤ 7/8 at hf1
  have hn1loR : (-2 : ℝ) < n1 := by linarith [hf1.2]
  have hn1hiR : (n1 : ℝ) < 1 := by linarith [hf1.1]
  have hn1loZ : (-2 : ℤ) < n1 := by exact_mod_cast hn1loR
  have hn1hiZ : n1 < (1 : ℤ) := by exact_mod_cast hn1hiR
  have hn1lo : (-1 : ℤ) ≤ n1 := by omega
  have hn1hi : n1 ≤ (0 : ℤ) := by omega
  unfold Cell2
  interval_cases n0 <;> interval_cases n1 <;> norm_num at hf0 hf1
  all_goals first
    | exact Or.inl (⟨by linarith,by linarith⟩)
    | exact Or.inr (Or.inl (⟨by linarith,by linarith⟩))
    | exact Or.inr (Or.inr (⟨by linarith,by linarith⟩))
    | exfalso; linarith

#print axioms cell0_clear
#print axioms clear0_cell
#print axioms cell1_clear
#print axioms clear1_cell
#print axioms cell2_clear
#print axioms clear2_cell
def Cell (a : Fin 3) (theta : ℝ) : Prop :=
  match a.val with
  | 0 => Cell0 theta
  | 1 => Cell1 theta
  | _ => Cell2 theta

theorem cell_iff (a : Fin 3) (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    Cell a theta ↔ ∀ i : Fin 3, (1/8 : ℝ) ≤ distInt (1/8+((i : ℝ)-(a : ℝ))*theta) := by
  fin_cases a
  · change Cell0 theta ↔ _
    norm_num only [Fin.val_mk,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
    exact ⟨cell0_clear theta,clear0_cell theta h0 h1⟩
  · change Cell1 theta ↔ _
    norm_num only [Fin.val_mk,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
    exact ⟨cell1_clear theta,clear1_cell theta h0 h1⟩
  · change Cell2 theta ↔ _
    norm_num only [Fin.val_mk,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
    exact ⟨cell2_clear theta,clear2_cell theta h0 h1⟩

theorem lifted_iff (a : Fin 3) (q h : ℤ) (tau : ℝ)
    (h0 : 0 ≤ tau-(h : ℝ)) (h1 : tau-(h : ℝ) ≤ 1) :
    Cell a (tau-(h : ℝ)) ↔
      ∀ i : Fin 3, (1/8 : ℝ) ≤ distInt ((q : ℝ)+1/8+((i : ℝ)-(a : ℝ))*tau) := by
  rw [cell_iff a _ h0 h1]
  have hi (i : Fin 3) := Fresh.UnitAPPacketFourLift.integer_lift ((i : ℕ) : ℤ) ((a : ℕ) : ℤ) q h tau
  simp only [Int.cast_natCast] at hi
  simp_rw [hi]

#print axioms cell_iff
#print axioms lifted_iff
end Fresh.UnitAPPacketThreeCells
