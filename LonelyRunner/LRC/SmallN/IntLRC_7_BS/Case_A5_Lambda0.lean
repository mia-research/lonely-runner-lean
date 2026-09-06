import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Lemmas
import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Section5

/-!
# n = 7 (Barajas–Serra) — §6 Λ₀ assembly for `|A| = 5`

This file provides the Λ₀ (level-0 multiplier) bridge that lifts the `ZMod 7`
shift-avoidance produced by `lemma5` (`intervalAvoids`) to the integer
`q`-avoidance conclusion used by `five_avoid`.

- `lambda0_lift` — single `k : ZMod 7` shift ⇒ unit multiplier `1 + k·7^m`.
-/

open Finset

namespace IntLRC7BS

/-- **Λ₀ lift.** A single `ZMod 7` shift `k` whose post-shift arc indices
`q(dᵢ) + k·r(dᵢ)` all avoid `{0,6}` is realized by the integer unit multiplier
`1 + k·7^m` (via `qz_shift0`, BS eq 3 at level 0). -/
theorem lambda0_lift (m : ℕ) (hm : 0 < m) {ι : Type*} (d : ι → ℤ)
    (k : ZMod 7)
    (havoid : ∀ i, qz m (d i) + k * (d i : ZMod 7) ∉ ({0, 6} : Finset (ZMod 7))) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
  set k_int : ℤ := (k.val : ℤ) with hk_def
  refine ⟨1 + k_int * 7 ^ m, by simpa using lam_unit m hm k_int 1 (le_refl 1) (by omega),
    fun i => ?_⟩
  rw [qz_shift0]
  have hk_cast : ((k_int : ℤ) : ZMod 7) = k :=
    show ((k.val : ℕ) : ZMod 7) = k from ZMod.natCast_rightInverse k
  rw [hk_cast]
  have h := havoid i
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
  exact ⟨h.1, h.2⟩

end IntLRC7BS
