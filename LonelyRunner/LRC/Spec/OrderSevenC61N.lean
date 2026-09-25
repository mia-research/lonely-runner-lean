import LonelyRunner.LRC.Spec.OrderSevenL1012N

/-!
# n = 7 (Barajas–Serra) — §6.1: dropping the distinctness hypothesis

A natural statement here sends five **distinct** `ZMod 7` residues outside
`{0,6}` by an affine unit map, using injectivity only to know that the complement
of the image has exactly two elements, so `affine_place_pair` can send those two
to `0` and `6`.

But two is all that is ever needed, and the image of *any* `Fin 5 → ZMod 7` has
at most five elements, hence a complement of at least two. So the injectivity
hypothesis is unnecessary: `affine_place_gen` below drops it.

`case_61_top_gen` below is the corresponding placement step, and it closes the
`ν(E) = {m}` half of §6.1 **without** any case split on whether the level-`m`
coefficients are distinct: the branch where they collapse is not a separate
argument, it is the same argument with more room.

An exhaustive check confirms the boundary is exactly where this reasoning puts
it: every subset of `ZMod 7` of size `≤ 5` fits a length-5 window under some unit
dilation, and no subset of size `6` or `7` does.
-/

namespace LRC.OrderSevenN
namespace Case61

open Finset

/-- **Affine placement, no distinctness needed.** Any five `ZMod 7` residues —
not necessarily distinct — admit an affine unit map `x ↦ A + u·x` sending all of
them outside `{0,6}`.

The image has at most 5 elements, so its complement has at least 2; picking any
two of them and mapping them to `0` and `6` by `affine_place_pair` works, since
`x ↦ A + u·x` is a bijection and therefore carries the image away from `{0,6}`. -/
theorem affine_place_gen (c : Fin 5 → ZMod 7) :
    ∃ u A : ZMod 7, u ≠ 0 ∧ ∀ i, A + u * c i ≠ 0 ∧ A + u * c i ≠ 6 := by
  classical
  set S : Finset (ZMod 7) := Finset.image c Finset.univ with hS
  have hScard : S.card ≤ 5 := by
    calc S.card ≤ (Finset.univ : Finset (Fin 5)).card := Finset.card_image_le
    _ = 5 := by simp
  have hcard7 : Fintype.card (ZMod 7) = 7 := by decide
  have hcompl : 2 ≤ Sᶜ.card := by
    have h := Finset.card_compl S
    rw [hcard7] at h
    omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < Sᶜ.card)
  obtain ⟨u, A, hu, hp0, hq6⟩ := affine_place_pair p q hpq
  have hpc : p ∉ S := Finset.mem_compl.mp hp
  have hqc : q ∉ S := Finset.mem_compl.mp hq
  refine ⟨u, A, hu, fun i => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have hcip : c i = p := mul_left_cancel₀ hu (add_left_cancel (a := A) (by rw [h, hp0]))
    exact hpc (hcip ▸ Finset.mem_image_of_mem c (Finset.mem_univ i))
  · have hciq : c i = q := mul_left_cancel₀ hu (add_left_cancel (a := A) (by rw [h, hq6]))
    exact hqc (hciq ▸ Finset.mem_image_of_mem c (Finset.mem_univ i))

/-- **§6.1 `ν(E) = {m}` placement.** The level-`m` coefficients need not be
distinct — `affine_place_gen` needs no injectivity — so `case_61` requires no
case split here. -/
theorem case_61_top_gen (m : ℕ) (hm : 0 < m) (d : Fin 5 → ℤ)
    (hres1 : ∀ i, (d i : ZMod 7) = 1)
    (htop : ∀ i, (7 : ℤ) ^ m ∣ (d i - d 0)) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i, qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
  set c : Fin 5 → ZMod 7 := fun i => (((d i - d 0) / 7 ^ m : ℤ) : ZMod 7) with hc_def
  obtain ⟨u, A, hu, havoid⟩ := affine_place_gen c
  set u_int : ℤ := (u.val : ℤ) with hu_def
  have hu_cast : ((u_int : ℤ) : ZMod 7) = u := by
    rw [hu_def]; push_cast; exact ZMod.natCast_rightInverse u
  have hu_ndvd : ¬ (7 : ℤ) ∣ u_int := by
    intro h; apply hu
    rw [← hu_cast]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd u_int 7).mpr (by exact_mod_cast h)
  set qb : ZMod 7 := qz m (u_int * d 0) with hqb
  set k : ZMod 7 := (A - qb) * u⁻¹ with hk_def
  have hku : k * u = A - qb := by rw [hk_def, mul_assoc, inv_mul_cancel₀ hu, mul_one]
  set k_int : ℤ := (k.val : ℤ) with hk_int_def
  have hk_cast : ((k_int : ℤ) : ZMod 7) = k := by
    rw [hk_int_def]; push_cast; exact ZMod.natCast_rightInverse k
  set lam : ℤ := (1 + k_int * 7 ^ m) * u_int with hlam_def
  have hlam_ndvd : ¬ (7 : ℤ) ∣ lam := by
    rw [hlam_def]
    have hp : Prime (7 : ℤ) := seven_totient_full_int
    have h1m : ¬ (7 : ℤ) ∣ (1 + k_int * 7 ^ m) := by
      intro h
      have hd7m : (7 : ℤ) ∣ k_int * 7 ^ m :=
        Dvd.dvd.mul_left (dvd_pow_self 7 (by omega : m ≠ 0)) k_int
      have h1 : (7 : ℤ) ∣ 1 := by have := dvd_sub h hd7m; simpa using this
      exact absurd h1 (by norm_num)
    intro h
    rcases hp.dvd_mul.mp h with h1 | h2
    · exact h1m h1
    · exact hu_ndvd h2
  refine ⟨lam, hlam_ndvd, fun i => ?_⟩
  have key : qz m (lam * d i) = A + u * c i := by
    have hrw : lam * d i = (1 + k_int * 7 ^ m) * (u_int * d i) := by rw [hlam_def]; ring
    rw [hrw, qz_shift0, hk_cast]
    have hres_i : ((u_int * d i : ℤ) : ZMod 7) = u := by
      push_cast; rw [hu_cast, hres1 i]; ring
    rw [hres_i]
    have haff : qz m (u_int * d i) = qb + u * c i := by
      rw [hqb, qz_top_affine m u_int (d i) (d 0) (htop i), hu_cast, hc_def]
    rw [haff]
    have : qb + u * c i + k * u = A + u * c i := by rw [hku]; ring
    linear_combination this
  rw [key]; exact havoid i

end Case61
end LRC.OrderSevenN
