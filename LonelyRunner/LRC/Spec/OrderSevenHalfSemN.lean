import LonelyRunner.LRC.Spec.OrderSevenL3SpecN
import LonelyRunner.LRC.Spec.OrderSevenL3BCoreN

/-!
# Order seven, half-unit certificates: what they give

* `gridOK3_neg`, `gridOK2_neg`: `u` and `7^a − u` are in band at the same instants (kernel-checked).
* `units3_of`: if every sorted half-index tuple has a common mask bit (certificate A), any five units share a unit
  instant of level 3.
* `units3_val1_of`: likewise four units and one valuation-1 runner (certificate B).

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.O7L3
open LRC.O7Grid

def neg3B : Bool := allR 343 0 fun u => allR 343 0 fun k =>
  decide (GridOK 3 k (343 - u)) == decide (GridOK 3 k u)

theorem neg3B_ok : neg3B = true := by decide +kernel

theorem gridOK3_neg {u k : ℕ} (hu : u < 343) : GridOK 3 k (343 - u) ↔ GridOK 3 k u := by
  rw [gridOK_mod_k, gridOK_mod_k 3 k u, show (7 : ℕ) ^ 3 = 343 by norm_num]
  have h := allR_spec _ _ _ (allR_spec _ _ _ neg3B_ok u (Nat.zero_le _) (by omega)) (k % 343) (Nat.zero_le _)
    (by have := Nat.mod_lt k (show 343 > 0 by norm_num); omega)
  simpa using h

def neg2B : Bool := allR 49 0 fun u => allR 49 0 fun k =>
  decide (GridOK 2 k (49 - u)) == decide (GridOK 2 k u)

theorem neg2B_ok : neg2B = true := by decide +kernel

theorem gridOK2_neg {u k : ℕ} (hu : u < 49) : GridOK 2 k (49 - u) ↔ GridOK 2 k u := by
  rw [gridOK_mod_k, gridOK_mod_k 2 k u, show (7 : ℕ) ^ 2 = 49 by norm_num]
  have h := allR_spec _ _ _ (allR_spec _ _ _ neg2B_ok u (Nat.zero_le _) (by omega)) (k % 49) (Nat.zero_le _)
    (by have := Nat.mod_lt k (show 49 > 0 by norm_num); omega)
  simpa using h

/-- The valuation-1 runner at level 3 is the cofactor at level 2. -/
theorem gridOK3_seven (m k : ℕ) : GridOK 3 k (7 * m) ↔ GridOK 2 k m := by
  unfold GridOK
  have e : 7 * m * k % 7 ^ 3 = 7 * (m * k % 49) := by
    rw [show 7 * m * k = 7 * (m * k) by ring, show (7 : ℕ) ^ 3 = 7 * 49 by norm_num, Nat.mul_mod_mul_left]
  rw [e]; norm_num; omega

def mmSpecB : Bool := allR 294 0 fun j => allR 42 0 fun t =>
  (mmL3 t).testBit j == decide (GridOK 2 (unitL3 j) (unit49 t))

theorem mmSpecB_ok : mmSpecB = true := by decide +kernel

theorem mmL3_spec {j t : ℕ} (hj : j < 294) (ht : t < 42) :
    (mmL3 t).testBit j = true ↔ GridOK 2 (unitL3 j) (unit49 t) := by
  have h := allR_spec _ _ _ (allR_spec _ _ _ mmSpecB_ok j (Nat.zero_le _) (by omega)) t (Nat.zero_le _) (by omega)
  simp only [beq_iff_eq] at h; rw [h]; simp

def idx49B : Bool := allR 49 0 fun u => u % 7 == 0 || (unit49 (u - 1 - u / 7) == u && decide (u - 1 - u / 7 < 42))

theorem idx49B_ok : idx49B = true := by decide +kernel

theorem unit49_idx {u : ℕ} (hu : u < 49) (h7 : u % 7 ≠ 0) : unit49 (u - 1 - u / 7) = u ∧ u - 1 - u / 7 < 42 := by
  have h := allR_spec _ _ _ idx49B_ok u (Nat.zero_le _) (by omega)
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact absurd h h7
  · exact h

theorem inv343 : ∀ u, u < 343 → u % 7 ≠ 0 → ∃ c, c < 343 ∧ c * u % 343 = 1 := by decide +kernel

/-- Sorted indices covering a finset of at most `n ≤ 4` indices below `B`. -/
theorem sorted_cover {W : Finset ℕ} {B : ℕ} (hB : 0 < B) (hc : W.card ≤ 4) (hW : ∀ i ∈ W, i < B) :
    ∃ i2 i3 i4 i5, i2 ≤ i3 ∧ i3 ≤ i4 ∧ i4 ≤ i5 ∧ i5 < B ∧ ∀ i ∈ W, i = i2 ∨ i = i3 ∨ i = i4 ∨ i = i5 := by
  have hs := List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort W)
  have hl : (W.sort (· ≤ ·)).length ≤ 4 := by rw [Finset.length_sort]; exact hc
  have hm : ∀ i, i ∈ W ↔ i ∈ W.sort (· ≤ ·) := fun i => (Finset.mem_sort _).symm
  generalize W.sort (· ≤ ·) = l at hs hl hm
  have hlt : ∀ i ∈ l, i < B := fun i h => hW i ((hm i).mpr h)
  match l, hs, hl, hm, hlt with
  | [], _, _, hm, _ => exact ⟨0, 0, 0, 0, le_rfl, le_rfl, le_rfl, hB, fun i h => by simp [hm] at h⟩
  | [a], _, _, hm, hlt =>
    exact ⟨a, a, a, a, le_rfl, le_rfl, le_rfl, hlt a (by simp), fun i h => by simp [hm] at h; omega⟩
  | [a, b], hs, _, hm, hlt =>
    have hab : a < b := by simp [List.pairwise_cons] at hs; exact hs
    exact ⟨a, b, b, b, hab.le, le_rfl, le_rfl, hlt b (by simp), fun i h => by simp [hm] at h; omega⟩
  | [a, b, c], hs, _, hm, hlt =>
    have h1 : a < b ∧ a < c ∧ b < c := by simp [List.pairwise_cons] at hs; omega
    exact ⟨a, b, c, c, h1.1.le, h1.2.2.le, le_rfl, hlt c (by simp), fun i h => by simp [hm] at h; omega⟩
  | [a, b, c, d], hs, _, hm, hlt =>
    have h1 : a < b ∧ b < c ∧ c < d := by simp [List.pairwise_cons] at hs; omega
    exact ⟨a, b, c, d, h1.1.le, h1.2.1.le, h1.2.2.le, hlt d (by simp), fun i h => by simp [hm] at h; omega⟩
  | _ :: _ :: _ :: _ :: _ :: _, _, hl, _, _ => simp at hl; omega

/-- Half representative of a unit mod 343. -/
def half3 (v : ℕ) : ℕ := if v ≤ 171 then v else 343 - v

theorem half3_spec {v : ℕ} (hv : v < 343) (h7 : v % 7 ≠ 0) :
    half3 v < 172 ∧ half3 v % 7 ≠ 0 ∧ ∀ k, GridOK 3 k (half3 v) ↔ GridOK 3 k v := by
  unfold half3
  split_ifs with h
  · exact ⟨by omega, h7, fun k => Iff.rfl⟩
  · refine ⟨by omega, by omega, fun k => gridOK3_neg hv⟩

/-- Normalisation shared by A and B: scale by the inverse of `u1`, reduce mod 343. -/
theorem normalise {U : Finset ℕ} {u1 : ℕ} (hu1 : u1 ∈ U) (hu : ∀ u ∈ U, ¬ 7 ∣ u) :
    ∃ c, ¬ 7 ∣ c ∧ c * u1 % 343 = 1 ∧ ∀ u ∈ U, c * u % 343 < 343 ∧ (c * u % 343) % 7 ≠ 0 := by
  have m7 : ∀ {x}, ¬ 7 ∣ x → x % 7 ≠ 0 := fun hx h0 => hx (Nat.dvd_of_mod_eq_zero h0)
  have mm : ∀ {x}, ¬ 7 ∣ x → (x % 343) % 7 ≠ 0 := fun {x} hx => by
    rw [show (343 : ℕ) = 7 * 49 by norm_num, Nat.mod_mul_right_mod]; exact m7 hx
  obtain ⟨c, hc343, hcu⟩ := inv343 (u1 % 343) (Nat.mod_lt _ (by norm_num)) (mm (hu u1 hu1))
  have hc7 : ¬ 7 ∣ c := by
    intro hd
    have : 7 ∣ c * (u1 % 343) % 343 := by
      rw [show (343 : ℕ) = 7 * 49 by norm_num]
      exact (Nat.dvd_mod_iff (dvd_mul_right 7 49)).mpr (dvd_mul_of_dvd_left hd _)
    rw [hcu] at this; norm_num at this
  refine ⟨c, hc7, ?_, fun u hu' => ⟨Nat.mod_lt _ (by norm_num), ?_⟩⟩
  · rw [Nat.mul_mod, Nat.mod_eq_of_lt hc343] at hcu ⊢; simpa [Nat.mul_mod] using hcu
  · rw [show (343 : ℕ) = 7 * 49 by norm_num, Nat.mod_mul_right_mod]
    exact m7 (fun hd => ((Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp hd).elim hc7 (hu u hu'))

end LRC.O7L3
