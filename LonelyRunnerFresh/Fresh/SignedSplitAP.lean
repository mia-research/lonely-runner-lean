import Fresh.SplitAPPositive
import Fresh.InterleavedGridShift

/-! Two signed AP reading blocks. The signed packet uses the same
physical subject; no stationary runner or signed physical speed is introduced.
[PROVISIONAL: counting tool] inherited exact grid-shift selection.
[PROVISIONAL: covering] finite middle strips in the supplied chart law.
-/
namespace Fresh.SplitAPBands
open Fresh Fresh.Localisation Fresh.InterleavedGridShift

 theorem split_train_grid (r : ℕ) (hr1 : 1 ≤ r) (hr5 : r ≤ 5)
    {B η : ℝ} (m : ℤ) (hB : B=(m : ℝ)+η)
    (hlo : B<0) (hhi : 0<B+((6-r : ℕ) : ℝ))
    (hη : η ≠ 0) (hηwidth : |η| ≤ (r : ℝ)/8) :
    ∃ t : ℝ, 0<t ∧ ∀ d ∈ splitTrain r B, (1/8 : ℝ) ≤ distInt (d*t) := by
  obtain ⟨t,ht,hint,hpacket⟩ := signed_packet_grid r hr1 hr5 m hB hlo hhi hη hηwidth
  refine ⟨t,ht,fun d hd => ?_⟩
  rcases Finset.mem_union.mp hd with hd | hd
  · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
    exact hint (j+1) (by omega) (by have := Finset.mem_range.mp hj; omega)
  · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
    exact hpacket j (by have := Finset.mem_range.mp hj; omega)

 theorem split_train_negative (r : ℕ) (hr1 : 1 ≤ r) (hr5 : r ≤ 5)
    (B : ℝ) (hB : B+((6-r : ℕ) : ℝ)<0) :
    ∃ t : ℝ, 0<t ∧ ∀ d ∈ splitTrain r B, (1/8 : ℝ) ≤ distInt (d*t) := by
  let L := 6-r
  have ha : 0 < -B-(L : ℝ) := by dsimp [L]; linarith
  obtain ⟨t,ht,hclear⟩ := split_train_positive r hr1 hr5 (-B-(L : ℝ)) ha
  refine ⟨t,ht,fun d hd => ?_⟩
  rcases Finset.mem_union.mp hd with hd | hd
  · exact hclear d (Finset.mem_union_left _ hd)
  · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
    have hjL : j ≤ L := by dsimp [L]; have := Finset.mem_range.mp hj; omega
    have hcast : ((L-j : ℕ) : ℝ)=(L : ℝ)-(j : ℝ) := by rw [Nat.cast_sub hjL]
    have hm : -B-(L : ℝ)+((L-j : ℕ) : ℝ) ∈ splitTrain r (-B-(L : ℝ)) := by
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨L-j,Finset.mem_range.mpr (by dsimp [L] at *; omega),rfl⟩
    have hc := hclear _ hm
    rw [hcast] at hc
    have he : (-B-(L : ℝ)+((L : ℝ)-(j : ℝ)))*t = -((B+(j : ℝ))*t) := by ring
    rw [he,distInt_neg] at hc
    exact hc

/-- The compact middle law is the only supplied hypothesis. Both unbounded
ends and both signed near-integer regimes are discharged by native AP laws. -/
theorem signed_split_noninteger_of_middle
    (H : ∀ (r : ℕ), 1 ≤ r → r ≤ 3 → ∀ (m : ℤ) (B : ℝ),
      -((6-r : ℕ) : ℤ) ≤ m → m < 0 →
      (m : ℝ)+(r : ℝ)/8 ≤ B → B ≤ (m : ℝ)+1-(r : ℝ)/8 →
      ∃ t : ℝ, 0<t ∧ ∀ d ∈ splitTrain r B, (1/8 : ℝ) ≤ distInt (d*t))
    (r : ℕ) (hr1 : 1 ≤ r) (hr5 : r ≤ 5) (B : ℝ)
    (hnot : ∀ m : ℤ, B ≠ (m : ℝ)) :
    ∃ t : ℝ, 0<t ∧ ∀ d ∈ splitTrain r B, (1/8 : ℝ) ≤ distInt (d*t) := by
  have hL : ((6-r : ℕ) : ℝ)=6-(r : ℝ) := by rw [Nat.cast_sub (by omega : r ≤ 6)]; norm_num
  have hrR : (0 : ℝ)<r := by exact_mod_cast (show 0<r by omega)
  by_cases hp : 0<B
  · exact split_train_positive r hr1 hr5 B hp
  by_cases hn : B+((6-r : ℕ) : ℝ)<0
  · exact split_train_negative r hr1 hr5 B hn
  have hlo : B<0 := lt_of_le_of_ne (le_of_not_gt hp) (by simpa using hnot 0)
  have hhi : 0<B+((6-r : ℕ) : ℝ) := by
    have hne := hnot (-((6-r : ℕ) : ℤ))
    push_cast at hne
    exact lt_of_le_of_ne (le_of_not_gt hn) (by intro he; apply hne; linarith)
  let m : ℤ := ⌊B⌋
  let η : ℝ := B-(m : ℝ)
  have hmle : (m : ℝ)≤B := Int.floor_le B
  have hmlt : B<(m : ℝ)+1 := Int.lt_floor_add_one B
  have hηpos : 0<η := sub_pos.mpr (lt_of_le_of_ne hmle (hnot m).symm)
  have hηlt : η<1 := by dsimp [η]; linarith
  have hB : B=(m : ℝ)+η := by dsimp [η]; ring
  by_cases hsmall : η≤(r : ℝ)/8
  · exact split_train_grid r hr1 hr5 m hB hlo hhi hηpos.ne' (by rwa [abs_of_pos hηpos])
  by_cases hlarge : 1-(r : ℝ)/8≤η
  · apply split_train_grid r hr1 hr5 (m+1) (η:=η-1) ?_ hlo hhi (by linarith) ?_
    · push_cast; rw [hB]; ring
    · rw [abs_of_neg (by linarith : η-1<0)]; linarith
  have hr3 : r≤3 := by
    by_contra hh
    have h4 : (4 : ℝ)≤r := by exact_mod_cast (show 4≤r by omega)
    linarith
  have hmlo : -((6-r : ℕ) : ℤ) ≤ m := by
    have hh : -(((6-r : ℕ) : ℤ) : ℝ) < (m : ℝ)+1 := by push_cast; linarith
    have hhI : -((6-r : ℕ) : ℤ) < m+1 := by exact_mod_cast hh
    omega
  have hmneg : m<0 := by exact_mod_cast (show (m : ℝ)<0 by linarith)
  apply H r hr1 hr3 m B hmlo hmneg
  · rw [hB]; linarith
  · rw [hB]; linarith

#print axioms split_train_grid
#print axioms split_train_negative
#print axioms signed_split_noninteger_of_middle
end Fresh.SplitAPBands
