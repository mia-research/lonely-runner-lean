import LonelyRunner.LRC.SmallN.IntLRC_7_BS.PrimeFiltering

/-! # Does the n=7 pigeonhole core extend off a prime modulus?

The owner's ruling: the §6A firewall bars automatic carry-over, not looking. And the n=7 proof is
on disk, so this is mechanical rather than speculative.

`IntLRC7BS.single_level_avoid` is the combinatorial core of BS Lemma 2. Its statement takes
`r i ≠ 0` and its proof closes with `mul_inv_cancel₀` — which is where `ZMod 7` being a **field**
is load-bearing. At `ZMod 8`, `2 ≠ 0` but `2` is not invertible, so the proof has no last step and
the statement is false as written (witness in `single_level_avoid_false_at_8` below).

What survives is the honest hypothesis: **the slopes must be units, not merely nonzero.** Over a
field those coincide, which is why BS never had to say it. `single_level_avoid_general` below is
the same pigeonhole over `ZMod N` for arbitrary `N`, and `recovers_n7` shows the existing n=7
lemma is exactly its `N = 7` instance — so this is a generalisation, not a different result.

**Scope, stated plainly.** This extends the *core pigeonhole* only. It does NOT extend Lemma 2:
BS's level structure `Λ_j,p = {1 + p^(m−j)k}` and the digit `r_p(x)` are specific to prime powers,
and at `p = 2` the digit is always `1`, so a 2-adic filtration allows `∑|F| ≤ 1` per level and is
near-vacuous. Nothing here licenses importing the n=7 argument. See `BS_TRANSFER_v1.md` §4, whose
firewall question is unresolved and governs anything built on top. -/

open Finset

namespace SingleLevelGeneral

/-- **The pigeonhole core, off a prime modulus.** For unit slopes `r i` and forbidden sets `F i`
in `ZMod N` of total size `≤ N − 1`, some multiplier coefficient `k` avoids every `F i`.

Identical to `IntLRC7BS.single_level_avoid` except that `r i ≠ 0` is replaced by `IsUnit (r i)`,
which is what the affine map `k ↦ c i + k · r i` actually needs to be a bijection. -/
theorem single_level_avoid_general {ι : Type*} {N : ℕ} [NeZero N] (s : Finset ι)
    (c r : ι → ZMod N) (F : ι → Finset (ZMod N))
    (hr : ∀ i ∈ s, IsUnit (r i))
    (hsum : ∑ i ∈ s, (F i).card ≤ N - 1) :
    ∃ k : ZMod N, ∀ i ∈ s, c i + k * r i ∉ F i := by
  classical
  set B : ι → Finset (ZMod N) := fun i => (F i).image (fun y => (y - c i) * Ring.inverse (r i))
    with hB
  have hBcard : ∀ i ∈ s, (B i).card ≤ (F i).card := fun i _ => card_image_le
  have hunion : (s.biUnion B).card ≤ N - 1 :=
    le_trans card_biUnion_le (le_trans (sum_le_sum hBcard) hsum)
  have hcardN : (univ : Finset (ZMod N)).card = N := by rw [card_univ, ZMod.card]
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hne : ∃ k : ZMod N, k ∉ s.biUnion B := by
    by_contra h
    push_neg at h
    have hle := card_le_card (fun k (_ : k ∈ (univ : Finset (ZMod N))) => h k)
    rw [hcardN] at hle
    omega
  obtain ⟨k, hknot⟩ := hne
  refine ⟨k, fun i hi hmem => ?_⟩
  have hkB : k ∉ B i := fun h => hknot (mem_biUnion.mpr ⟨i, hi, h⟩)
  apply hkB
  rw [hB, mem_image]
  refine ⟨c i + k * r i, hmem, ?_⟩
  show (c i + k * r i - c i) * Ring.inverse (r i) = k
  rw [add_sub_cancel_left, mul_assoc, Ring.mul_inverse_cancel _ (hr i hi), mul_one]

/-- The existing n=7 lemma is the `N = 7` instance: over a field, nonzero *is* unit. -/
theorem recovers_n7 {ι : Type*} (s : Finset ι)
    (c r : ι → ZMod 7) (F : ι → Finset (ZMod 7))
    (hr : ∀ i ∈ s, r i ≠ 0)
    (hsum : ∑ i ∈ s, (F i).card ≤ 6) :
    ∃ k : ZMod 7, ∀ i ∈ s, c i + k * r i ∉ F i :=
  single_level_avoid_general s c r F (fun i hi => (hr i hi).isUnit) (by simpa using hsum)

/-- **The nonzero hypothesis really is insufficient off a field.**  Taking `N = 8`, one index,
slope `r = 2` (nonzero, not a unit) and `F = {0, 2, 4, 6}` of size `4 ≤ 8 − 1`, every `k` lands
in `F`. So `single_level_avoid`'s statement is false at `ZMod 8`, not merely unproved. -/
theorem single_level_avoid_false_at_8 :
    ¬ (∀ (s : Finset (Fin 1)) (c r : Fin 1 → ZMod 8) (F : Fin 1 → Finset (ZMod 8)),
        (∀ i ∈ s, r i ≠ 0) → (∑ i ∈ s, (F i).card ≤ 7) →
        ∃ k : ZMod 8, ∀ i ∈ s, c i + k * r i ∉ F i) := by
  intro h
  obtain ⟨k, hk⟩ := h univ (fun _ => 0) (fun _ => 2) (fun _ => {0, 2, 4, 6})
    (by decide) (by decide)
  exact absurd (hk 0 (mem_univ 0)) (by revert k; decide)

end SingleLevelGeneral
