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

end LRC.O7Grid
