import LonelyRunner.LRC.Spec.OrderSevenLevel2N

/-!
# Order seven: the cell descent at level 3

* `gridOK_three_val2`: `49 d'` with `7 ∤ d'` is in band at every unit instant of level 3.
* `gridOK_three_val1`: `7 d'` at `k0 + 49 s` is in band iff `d'` is in band at `k0` at level 2 (independent of `s`).
* `blocked_le_two` (kernel-checked over all residues): a unit blocks at most two of the seven top digits `s`.
* `free_digit`: at most three units leave a free top digit `s`.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.O7Grid

theorem gridOK_three_val2 {d' k : ℕ} (hd : ¬ 7 ∣ d') (hk : ¬ 7 ∣ k) : GridOK 3 k (49 * d') := by
  unfold GridOK
  have h1 : d' * k % 7 ≠ 0 := by
    intro h; exact (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp (Nat.dvd_of_mod_eq_zero h) |>.elim hd hk
  have h2 : d' * k % 7 < 7 := Nat.mod_lt _ (by norm_num)
  have e : 49 * d' * k % 7 ^ 3 = 49 * (d' * k % 7) := by
    rw [show 49 * d' * k = 49 * (d' * k) by ring, show (7 : ℕ) ^ 3 = 49 * 7 by norm_num, Nat.mul_mod_mul_left]
  rw [e]; norm_num; omega

theorem gridOK_three_val1 (d' k0 s : ℕ) : GridOK 3 (k0 + 49 * s) (7 * d') ↔ GridOK 2 k0 d' := by
  unfold GridOK
  have e : 7 * d' * (k0 + 49 * s) % 7 ^ 3 = 7 * (d' * k0 % 49) := by
    rw [show 7 * d' * (k0 + 49 * s) = 7 * (d' * k0 + 49 * (d' * s)) by ring,
      show (7 : ℕ) ^ 3 = 7 * 49 by norm_num, Nat.mul_mod_mul_left, Nat.add_mul_mod_self_left]
  rw [e]; norm_num; omega

/-- For every unit residue `u < 343` and unit `k0 < 49`, at most two `s < 7` make `k0 + 49 s` block `u`. -/
def blockedB : Bool :=
  (List.range 343).all fun u => u % 7 == 0 ||
    (List.range 49).all fun k0 => k0 % 7 == 0 ||
      decide (((List.range 7).filter fun s => !decide (GridOK 3 (k0 + 49 * s) u)).length ≤ 2)

theorem blockedB_ok : blockedB = true := by decide +kernel

theorem blocked_le_two {u k0 : ℕ} (hu : ¬ 7 ∣ u) (hk : ¬ 7 ∣ k0) (hk49 : k0 < 49) :
    ((Finset.range 7).filter fun s => ¬ GridOK 3 (k0 + 49 * s) u).card ≤ 2 := by
  have hred : ∀ s, GridOK 3 (k0 + 49 * s) u ↔ GridOK 3 (k0 + 49 * s) (u % 343) := fun s => gridOK_mod _ _ _
  have h := blockedB_ok
  simp only [blockedB, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  have hu' : u % 343 % 7 ≠ 0 := by
    rw [show (343 : ℕ) = 7 * 49 by norm_num, Nat.mod_mul_right_mod]; exact fun h0 => hu (Nat.dvd_of_mod_eq_zero h0)
  have hk' : k0 % 7 ≠ 0 := fun h0 => hk (Nat.dvd_of_mod_eq_zero h0)
  rcases h (u % 343) (Nat.mod_lt _ (by norm_num)) with h | h
  · exact absurd h hu'
  rcases h k0 hk49 with h | h
  · exact absurd h hk'
  have : ((Finset.range 7).filter fun s => ¬ GridOK 3 (k0 + 49 * s) u) =
      ((List.range 7).filter fun s => !decide (GridOK 3 (k0 + 49 * s) (u % 343))).toFinset := by
    ext s; simp [hred]
  rw [this]
  exact le_trans (List.toFinset_card_le _) h

/-- **Free top digit.**  At most three units: some `s < 7` puts all of them in band at `k0 + 49 s`. -/
theorem free_digit {U : Finset ℕ} (hc : U.card ≤ 3) (hu : ∀ u ∈ U, ¬ 7 ∣ u) {k0 : ℕ} (hk : ¬ 7 ∣ k0)
    (hk49 : k0 < 49) :
    ∃ s, s < 7 ∧ ∀ u ∈ U, GridOK 3 (k0 + 49 * s) u := by
  by_contra hno
  push_neg at hno
  have hcov : Finset.range 7 ⊆ U.biUnion fun u => (Finset.range 7).filter fun s => ¬ GridOK 3 (k0 + 49 * s) u := by
    intro s hs
    obtain ⟨u, hu', hb⟩ := hno s (Finset.mem_range.mp hs)
    exact Finset.mem_biUnion.mpr ⟨u, hu', Finset.mem_filter.mpr ⟨hs, hb⟩⟩
  have h1 := Finset.card_le_card hcov
  have h2 := Finset.card_biUnion_le (s := U) (t := fun u => (Finset.range 7).filter fun s => ¬ GridOK 3 (k0 + 49 * s) u)
  have h3 : ∑ u ∈ U, ((Finset.range 7).filter fun s => ¬ GridOK 3 (k0 + 49 * s) u).card ≤ ∑ _u ∈ U, 2 :=
    Finset.sum_le_sum fun u hu' => blocked_le_two (hu u hu') hk hk49
  simp only [Finset.sum_const, smul_eq_mul, Finset.card_range] at h1 h3
  omega

end LRC.O7Grid
