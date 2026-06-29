import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Lemmas
import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Section5

/-!
# n = 7 (Barajas–Serra) — §6 Λ₀ assembly for `|A| = 5`

This file provides the Λ₀ (level-0 multiplier) bridge that lifts the `ZMod 7`
shift-avoidance produced by `lemma5` (`intervalAvoids`) to the integer
`q`-avoidance conclusion used by `five_avoid`.

- `lambda0_lift` — single `k : ZMod 7` shift ⇒ unit multiplier `1 + k·7^m`.
- `five_lambda0` — full §6 assembly: five elements in residue classes `{1,2,4}`,
  each class fitting a short interval with total length `≤ 5`, admit a unit
  multiplier sending every arc index outside `{0,6}`. (BS §6, Lemma 5 route.)
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

/-- **§6 Λ₀ assembly (Lemma 5 route).** Five integers, each with residue in
`{1,2,4}` (tagged by `cls`), whose arc indices `q(dᵢ)` per residue class fit a
length-`ℓ₁`/`ℓ₂`/`ℓ₄` interval with `ℓ₁+ℓ₂+ℓ₄ ≤ 5` (and `A₁` most popular, the
`(3,1,1)` triple carrying its `ẽ ∉ {2,4}` carve-out), admit a unit multiplier
sending every `q(lam·dᵢ)` outside `{0,6}`. This is BS §6's terminal step: once
the case analysis compresses the three classes into short intervals, `lemma5`
yields the shift `k` and `lambda0_lift` lifts it to ℤ. -/
theorem five_lambda0 (m : ℕ) (hm : 0 < m) (d : Fin 5 → ℤ)
    (a₁ a₂ a₄ : ZMod 7) (ℓ₁ ℓ₂ ℓ₄ : ℕ)
    (h₁ : ℓ₁ ≤ 5) (hsum : ℓ₁ + ℓ₂ + ℓ₄ ≤ 5) (h21 : ℓ₂ ≤ ℓ₁) (h41 : ℓ₄ ≤ ℓ₁)
    (hexc : ℓ₁ = 3 ∧ ℓ₂ = 1 ∧ ℓ₄ = 1 → (2 * a₂ - a₄) ∉ ({2, 4} : Finset (ZMod 7)))
    (cls : Fin 5 → ZMod 7)
    (hcls : ∀ i, cls i = 1 ∨ cls i = 2 ∨ cls i = 4)
    (hres : ∀ i, (d i : ZMod 7) = cls i)
    (hfit : ∀ i, (cls i = 1 → ∃ j : Fin ℓ₁, qz m (d i) = a₁ + (j.val : ZMod 7)) ∧
                 (cls i = 2 → ∃ j : Fin ℓ₂, qz m (d i) = a₂ + (j.val : ZMod 7)) ∧
                 (cls i = 4 → ∃ j : Fin ℓ₄, qz m (d i) = a₄ + (j.val : ZMod 7))) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i,
      qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
  obtain ⟨k, hk1, hk2, hk4⟩ := lemma5 a₁ a₂ a₄ ℓ₁ ℓ₂ ℓ₄ h₁ hsum h21 h41 hexc
  refine lambda0_lift m hm d k (fun i => ?_)
  rw [hres i]
  rcases hcls i with hc | hc | hc <;> rw [hc]
  · obtain ⟨j, hj⟩ := (hfit i).1 hc
    have := hk1 j; rw [hj]; simpa [intervalAvoids, mul_one] using this
  · obtain ⟨j, hj⟩ := (hfit i).2.1 hc
    have := hk2 j; rw [hj]; simpa [intervalAvoids, mul_comm] using this
  · obtain ⟨j, hj⟩ := (hfit i).2.2 hc
    have := hk4 j; rw [hj]; simpa [intervalAvoids, mul_comm] using this

end IntLRC7BS
