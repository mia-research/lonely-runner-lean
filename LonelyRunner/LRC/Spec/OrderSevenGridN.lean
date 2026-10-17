import LonelyRunner.LRC.Spec.MirrorCentreN
import LonelyRunner.LRC.ConstructionN.LemmaPass

/-!
# Order seven on 7-adic residue grids

`lonely_of_grid`: if every speed `d` of `S` has `7^(a-1) ≤ d k mod 7^a ≤ 6·7^(a-1)`, every reading `d · k / 7^a` is at
circular distance at least `1/7` from the integers.  The grid instants `k / 7^a` are where order seven is lonely
(experiments/n7_native log E18–E20).

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.O7Grid

open LRC.MirrorCentre

/-- **Grid instant.** -/
theorem lonely_of_grid {S : Finset ℕ} {a k : ℕ} (ha : 1 ≤ a)
    (h : ∀ d ∈ S, 7 ^ (a - 1) ≤ (d * k) % 7 ^ a ∧ (d * k) % 7 ^ a ≤ 6 * 7 ^ (a - 1)) :
    ∀ d ∈ S, (1 : ℝ) / 7 ≤ circDist ((d : ℝ) * ((k : ℝ) / 7 ^ a)) := by
  intro d hd
  obtain ⟨h1, h2⟩ := h d hd
  obtain ⟨q, r, hq, hr⟩ : ∃ q r : ℕ, q = d * k / 7 ^ a ∧ r = d * k % 7 ^ a := ⟨_, _, rfl, rfl⟩
  rw [← hr] at h1 h2
  have hdk : (d : ℝ) * k = (7 : ℝ) ^ a * q + r := by
    have := Nat.div_add_mod (d * k) (7 ^ a)
    rw [← hq, ← hr] at this
    exact_mod_cast this.symm
  have hNpos : (0 : ℝ) < (7 : ℝ) ^ a := by positivity
  have hsplit : (d : ℝ) * ((k : ℝ) / 7 ^ a) = ((q : ℤ) : ℝ) + (r : ℝ) / 7 ^ a := by
    rw [mul_div_assoc', hdk]; push_cast; field_simp
  rw [hsplit, add_comm, ConstructionN.circDist_add_int]
  have h7 : (7 : ℝ) ^ a = 7 * 7 ^ (a - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hp : (0 : ℝ) < 7 ^ (a - 1) := by positivity
  have r1 : ((7 ^ (a - 1) : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast h1
  have r2 : (r : ℝ) ≤ ((6 * 7 ^ (a - 1) : ℕ) : ℝ) := by exact_mod_cast h2
  push_cast at r1 r2
  apply circDist_ge_of_window (m := 0) _ _ (by norm_num)
  · push_cast; rw [le_div_iff₀ hNpos, h7]; nlinarith
  · push_cast; rw [div_le_iff₀ hNpos, h7]; nlinarith

/-! ### Grid conditions on residues -/

/-- Speed `d` is in band at the grid instant `k / 7^a`. -/
def GridOK (a k d : ℕ) : Prop := 7 ^ (a - 1) ≤ d * k % 7 ^ a ∧ d * k % 7 ^ a ≤ 6 * 7 ^ (a - 1)

instance (a k d : ℕ) : Decidable (GridOK a k d) := by unfold GridOK; infer_instance

/-- Only `d mod 7^a` matters. -/
theorem gridOK_mod (a k d : ℕ) : GridOK a k d ↔ GridOK a k (d % 7 ^ a) := by
  unfold GridOK; rw [Nat.mod_mul_mod]

/-- Only `k mod 7^a` matters. -/
theorem gridOK_mod_k (a k d : ℕ) : GridOK a k d ↔ GridOK a (k % 7 ^ a) d := by
  unfold GridOK; rw [Nat.mul_mod_mod]

/-- Common scaling: `c` moves from the instant to the speed. -/
theorem gridOK_scale (a c k d : ℕ) : GridOK a (c * k) d ↔ GridOK a k (c * d) := by
  unfold GridOK; rw [show d * (c * k) = c * d * k by ring]

/-- Level 1: a speed not divisible by 7 is in band at `k/7` for `k = 1..6`. -/
theorem gridOK_one {d k : ℕ} (hd : ¬ 7 ∣ d) (hk : ¬ 7 ∣ k) : GridOK 1 k d := by
  unfold GridOK
  have h1 : d * k % 7 ≠ 0 := by
    intro h; exact (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp (Nat.dvd_of_mod_eq_zero h) |>.elim hd hk
  have h2 : d * k % 7 < 7 := Nat.mod_lt _ (by norm_num)
  simp only [Nat.sub_self, pow_zero, pow_one]; omega

/-- A speed `7 d'` with `7 ∤ d'` is in band at every unit instant of level 2. -/
theorem gridOK_two_val1 {d' k : ℕ} (hd : ¬ 7 ∣ d') (hk : ¬ 7 ∣ k) : GridOK 2 k (7 * d') := by
  unfold GridOK
  have h1 : d' * k % 7 ≠ 0 := by
    intro h; exact (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp (Nat.dvd_of_mod_eq_zero h) |>.elim hd hk
  have h2 : d' * k % 7 < 7 := Nat.mod_lt _ (by norm_num)
  have e : 7 * d' * k % 7 ^ 2 = 7 * (d' * k % 7) := by
    rw [show 7 * d' * k = 7 * (d' * k) by ring, show (7 : ℕ) ^ 2 = 7 * 7 by norm_num, Nat.mul_mod_mul_left]
  rw [e]; norm_num; omega

/-- **Lonely from grid conditions.** -/
theorem lonely_of_gridOK {S : Finset ℕ} {a k : ℕ} (ha : 1 ≤ a) (h : ∀ d ∈ S, GridOK a k d) :
    ∃ t : ℝ, ∀ d ∈ S, (1 : ℝ) / 7 ≤ circDist ((d : ℝ) * t) :=
  ⟨(k : ℝ) / 7 ^ a, lonely_of_grid ha h⟩

/-- **Order seven at level 1**: if no speed is divisible by 7, `t = 1/7` is lonely. -/
theorem lonely_level_one {S : Finset ℕ} (h : ∀ d ∈ S, ¬ 7 ∣ d) :
    ∃ t : ℝ, ∀ d ∈ S, (1 : ℝ) / 7 ≤ circDist ((d : ℝ) * t) :=
  lonely_of_gridOK (a := 1) (k := 1) le_rfl (fun d hd => gridOK_one (h d hd) (by norm_num))

end LRC.O7Grid
