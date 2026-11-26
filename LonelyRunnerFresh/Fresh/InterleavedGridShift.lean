import Fresh.Localisation

/-!
Rules: 1–4, 8–18. Exact AP-grid displacement of a signed translated packet
straddling the subject. At t=N+1/8 all integer readings1,...,7 remain clear.
The packet's common fractional offset selects N by a ceiling; the selected
whole-lap reading phase is retained explicitly.
[PROVISIONAL: counting tool] at the ceiling inequality, supporting placement
of the common packet phase within its exact clear band. No density argument.
-/
open Classical
namespace Fresh.InterleavedGridShift
open Fresh Fresh.Localisation

theorem integer_grid_clear (N : ℤ) (i : ℕ) (hi1 : 1 ≤ i) (hi7 : i ≤ 7) :
    (1/8 : ℝ) ≤ distInt ((i : ℝ)*((N : ℝ)+1/8)) := by
  have he : (i : ℝ)*((N : ℝ)+1/8) = (i : ℝ)/8+(((i : ℤ)*N : ℤ) : ℝ) := by push_cast; ring
  rw [he,distInt_add_int]
  apply clear_of_window 0 <;> push_cast
  · have : (1 : ℝ) ≤ i := by exact_mod_cast hi1
    linarith
  · have : (i : ℝ) ≤ 7 := by exact_mod_cast hi7
    linarith

/-- Positive fractional offset: push the packet's lower phase to1/8.
The integer lap is derived from B and η, never supplied as a witness. -/
theorem packet_positive {B η : ℝ} (m : ℤ) (L : ℕ)
    (hB : B=(m : ℝ)+η) (hB0 : B<0) (hη : 0<η)
    (hwidth : 8*η+(L : ℝ) ≤ 6) :
    ∃ N : ℤ, 0 < (N : ℝ)+1/8 ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ 7 → (1/8 : ℝ) ≤ distInt ((i : ℝ)*((N : ℝ)+1/8))) ∧
      ∀ j : ℕ, j ≤ L → (1/8 : ℝ) ≤ distInt ((B+(j : ℝ))*((N : ℝ)+1/8)) := by
  let z := (1-B)/(8*η)
  let N : ℤ := ⌈z⌉
  have hz : 0<z := by dsimp [z]; exact div_pos (by linarith) (by positivity)
  have hez : η*z=(1-B)/8 := by dsimp [z]; field_simp
  have h1 : z≤(N : ℝ) := Int.le_ceil z
  have h2 : (N : ℝ)<z+1 := Int.ceil_lt_add_one z
  have hn : 0<(N : ℝ) := hz.trans_le h1
  have hlo := mul_le_mul_of_nonneg_left h1 hη.le
  have hhi := mul_lt_mul_of_pos_left h2 hη
  refine ⟨N,by linarith,integer_grid_clear N,?_⟩
  intro j hj
  have hjR : (j : ℝ) ≤ L := by exact_mod_cast hj
  have he : (B+(j : ℝ))*((N : ℝ)+1/8) =
      (η*(N : ℝ)+(B+(j : ℝ))/8)+((((m+(j : ℤ))*N : ℤ)) : ℝ) := by
    rw [hB]
    push_cast
    ring
  rw [he,distInt_add_int]
  apply clear_of_window 0 <;> push_cast
  · have := Nat.cast_nonneg (α := ℝ) j
    nlinarith
  · nlinarith

/-- Negative fractional offset reverses the signed packet and applies the
same derived grid shift. Closed offset-width equality remains admissible. -/
theorem packet_negative {B η : ℝ} (m : ℤ) (L : ℕ)
    (hB : B=(m : ℝ)+η) (hBhi : 0<B+(L : ℝ)) (hη : η<0)
    (hwidth : 8*(-η)+(L : ℝ) ≤ 6) :
    ∃ N : ℤ, 0 < (N : ℝ)+1/8 ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ 7 → (1/8 : ℝ) ≤ distInt ((i : ℝ)*((N : ℝ)+1/8))) ∧
      ∀ j : ℕ, j ≤ L → (1/8 : ℝ) ≤ distInt ((B+(j : ℝ))*((N : ℝ)+1/8)) := by
  obtain ⟨N,hN,hints,hpacket⟩ := packet_positive (B := -B-(L : ℝ)) (η := -η)
    (-m-(L : ℤ)) L (by push_cast; rw [hB]; ring) (by linarith) (by linarith) hwidth
  refine ⟨N,hN,hints,?_⟩
  intro j hj
  have hcast : ((L-j : ℕ) : ℝ)=(L : ℝ)-(j : ℝ) := by rw [Nat.cast_sub hj]
  have hc := hpacket (L-j) (by omega)
  rw [hcast] at hc
  have he : (-B-(L : ℝ)+((L : ℝ)-(j : ℝ)))*((N : ℝ)+1/8) = -((B+(j : ℝ))*((N : ℝ)+1/8)) := by ring
  rw [he,distInt_neg] at hc
  exact hc

/-- Uniform signed-packet interface for splitTrain's remaining middle.
The nonzero fractional offset is explicit; zero would permit a physical
collision inside a straddling integer packet. -/
theorem signed_packet_grid (r : ℕ) (hr1 : 1 ≤ r) (hr5 : r ≤ 5)
    {B η : ℝ} (m : ℤ) (hB : B=(m : ℝ)+η)
    (hlo : B<0) (hhi : 0<B+((6-r : ℕ) : ℝ))
    (hη : η ≠ 0) (hηwidth : |η| ≤ (r : ℝ)/8) :
    ∃ t : ℝ, 0<t ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ r → (1/8 : ℝ) ≤ distInt ((i : ℝ)*t)) ∧
      ∀ j : ℕ, j ≤ 6-r → (1/8 : ℝ) ≤ distInt ((B+(j : ℝ))*t) := by
  have hL : ((6-r : ℕ) : ℝ)=6-(r : ℝ) := by rw [Nat.cast_sub (by omega : r ≤ 6)]; norm_num
  rcases lt_or_gt_of_ne hη with hneg | hpos
  · have hwidth : 8*(-η)+((6-r : ℕ) : ℝ) ≤ 6 := by
      rw [hL]
      rw [abs_of_neg hneg] at hηwidth
      linarith
    obtain ⟨N,hN,hints,hpacket⟩ := packet_negative m (6-r) hB hhi hneg hwidth
    exact ⟨(N : ℝ)+1/8,hN,fun i hi1 hir => hints i hi1 (by omega),hpacket⟩
  · have hwidth : 8*η+((6-r : ℕ) : ℝ) ≤ 6 := by
      rw [hL]
      rw [abs_of_pos hpos] at hηwidth
      linarith
    obtain ⟨N,hN,hints,hpacket⟩ := packet_positive m (6-r) hB hlo hpos hwidth
    exact ⟨(N : ℝ)+1/8,hN,fun i hi1 hir => hints i hi1 (by omega),hpacket⟩

#print axioms integer_grid_clear
#print axioms packet_positive
#print axioms packet_negative
#print axioms signed_packet_grid
end Fresh.InterleavedGridShift
