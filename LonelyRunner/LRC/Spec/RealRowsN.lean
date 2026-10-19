import LonelyRunner.LRC.Spec.ManyDirectionsN
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! Shared integer rows, parallelism, and real-speed basis representation. -/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.OrderFiveN

open MomentIterationN LRC.SpecN ConstructionN LRC.Stepping

variable {m : ℕ}

/-! ## Parallel rows -/

theorem parallel_refl (r : Fin m → ℤ) : Parallel r r := fun _ _ => mul_comm _ _

theorem parallel_symm {r s : Fin m → ℤ} (h : Parallel r s) : Parallel s r := fun i k => by
  have := h k i; linarith [mul_comm (r k) (s i), mul_comm (r i) (s k)]

/-- Parallelism passes through a non-zero row. -/
theorem parallel_trans {r s t : Fin m → ℤ} (hs : s ≠ 0) (h1 : Parallel r s) (h2 : Parallel s t) :
    Parallel r t := by
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hs
  intro q r'
  have hA := h1 q p
  have hC := h1 r' p
  have hB := h2 p r'
  have hD := h2 p q
  have key : (s p * s p) * (r q * t r' - r r' * t q) = 0 := by
    linear_combination (r q * s p) * hB + (s r' * t p) * hA - (r r' * s p) * hD - (s q * t p) * hC
  have hpp : s p * s p ≠ 0 := mul_ne_zero hp hp
  have := (mul_eq_zero.mp key).resolve_left hpp
  linarith

theorem dotZ_sub_smul (y r s : Fin m → ℤ) (ε : ℤ) :
    dotZ y (fun q => r q - ε * s q) = dotZ y r - ε * dotZ y s := by
  simp only [dotZ, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- A direction perpendicular to `d` and off the hyperplanes of every row not parallel to `d`:
`y = (d·d) z − (z·d) d`. -/
theorem exists_perp_avoid {k : ℕ} (d : Fin m → ℤ) (hd : d ≠ 0) (a : Fin k → Fin m → ℤ)
    (ha : ∀ i, ¬ Parallel (a i) d) :
    ∃ y : Fin m → ℤ, dotZ y d = 0 ∧ ∀ i, dotZ y (a i) ≠ 0 := by
  classical
  set D2 : ℤ := dotZ d d with hD2
  have hD2ne : D2 ≠ 0 := by
    intro h0
    apply hd
    have hsum : ∑ q, d q * d q = 0 := h0
    have hnn : ∀ q ∈ Finset.univ, 0 ≤ d q * d q := fun q _ => mul_self_nonneg _
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum
    funext q
    exact mul_self_eq_zero.mp (this q (Finset.mem_univ q))
  -- the normals of the rows, seen from inside `d`'s hyperplane
  set h : Fin k → Fin m → ℤ := fun i q => D2 * a i q - dotZ d (a i) * d q with hh
  have hhne : ∀ i, h i ≠ 0 := by
    intro i h0
    apply ha i
    intro q r
    have hq := congrFun h0 q
    have hr := congrFun h0 r
    simp only [hh, Pi.zero_apply] at hq hr
    have : D2 * (a i q * d r - a i r * d q) = 0 := by
      linear_combination (d r) * hq - (d q) * hr
    have := (mul_eq_zero.mp this).resolve_left hD2ne
    linarith
  obtain ⟨z, hz⟩ := exists_avoid (Finset.univ.image h) (by
    intro s hs; obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs; exact hhne i)
  have hdot : ∀ r : Fin m → ℤ, dotZ (fun q => D2 * z q - dotZ z d * d q) r =
      D2 * dotZ z r - dotZ z d * dotZ d r := by
    intro r
    simp only [dotZ, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  refine ⟨fun q => D2 * z q - dotZ z d * d q, ?_, fun i => ?_⟩
  · rw [hdot]; ring
  · rw [hdot]
    have e : D2 * dotZ z (a i) - dotZ z d * dotZ d (a i) = dotZ z (h i) := by
      simp only [hh]
      generalize dotZ d (a i) = A
      have : dotZ z (fun q => D2 * a i q - A * d q) = D2 * dotZ z (a i) - A * dotZ z d := by
        simp only [dotZ, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [this]; ring
    rw [e]
    exact hz _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))

/-! ## Rows over a basis of the speeds -/

/-- A rational times a multiple of its denominator is a whole number. -/
theorem exists_int_eq_mul_of_den_dvd (q : ℚ) {D : ℕ} (h : q.den ∣ D) :
    ∃ z : ℤ, (z : ℚ) = q * D := by
  obtain ⟨c, hc⟩ := h
  refine ⟨q.num * c, ?_⟩
  rw [hc]; push_cast
  rw [← mul_assoc, Rat.mul_den_eq_num]

/-- No whole-number relation means no rational relation. -/
theorem noRelation_of_int {d : ℕ} {β : Fin d → ℝ}
    (hZ : ∀ (c0 : ℤ) (c : Fin d → ℤ), (c0 : ℝ) + ∑ j, (c j : ℝ) * β j = 0 → c0 = 0 ∧ c = 0) :
    NoRelation β := by
  intro c0 c h
  set D : ℕ := c0.den * ∏ j, (c j).den with hD
  have hDpos : 0 < D := Nat.mul_pos c0.den_pos (Finset.prod_pos fun j _ => (c j).den_pos)
  have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
  obtain ⟨z0, hz0⟩ := exists_int_eq_mul_of_den_dvd c0 (Dvd.intro _ rfl : c0.den ∣ D)
  have hdvd : ∀ j, (c j).den ∣ D := fun j =>
    Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)) _
  choose z hz using fun j => exists_int_eq_mul_of_den_dvd (c j) (hdvd j)
  have cast : ∀ (w : ℤ) (q : ℚ), (w : ℚ) = q * D → (w : ℝ) = (q : ℝ) * D := by
    intro w q hw
    have := congrArg (fun x : ℚ => (x : ℝ)) hw
    push_cast at this
    exact this
  have hrel : (z0 : ℝ) + ∑ j, (z j : ℝ) * β j = 0 := by
    rw [cast z0 c0 hz0]
    rw [Finset.sum_congr rfl fun j _ => by rw [cast (z j) (c j) (hz j)]]
    have : (c0 : ℝ) * D + ∑ j, (c j : ℝ) * D * β j = D * ((c0 : ℝ) + ∑ j, (c j : ℝ) * β j) := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, h, mul_zero]
  obtain ⟨h0, hc⟩ := hZ z0 z hrel
  constructor
  · have : c0 * D = 0 := by rw [← hz0, h0]; simp
    exact (mul_eq_zero.mp this).resolve_right hD0
  · funext j
    have hj := congrFun hc j
    have : c j * D = 0 := by rw [← hz j]; simp [hj]
    exact (mul_eq_zero.mp this).resolve_right hD0

/-- **Rows.**  Finitely many non-zero reals are one real factor times the speeds of whole-number
rows over directions `1, β` with no rational relation.  The directions come from a basis of the
free group the reals span. -/
theorem exists_rows (X : Finset ℝ) (hX : ∀ x ∈ X, x ≠ 0) (hne : X.Nonempty) :
    ∃ d : ℕ, ∃ β : Fin d → ℝ, NoRelation β ∧ ∃ l : ℝ, l ≠ 0 ∧
      ∃ a : ℝ → Fin (d + 1) → ℤ, ∀ x ∈ X, x = l * speed β (a x) := by
  classical
  set M := Submodule.span ℤ (X : Set ℝ) with hM
  set b := Module.Free.chooseBasis ℤ M with hb
  obtain ⟨x0, hx0⟩ := hne
  have hcard : 0 < Fintype.card (Module.Free.ChooseBasisIndex ℤ M) := by
    rw [Fintype.card_pos_iff]
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    have := b.sum_repr ⟨x0, Submodule.subset_span hx0⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty] at this
    exact hX x0 hx0 (congrArg Subtype.val this).symm
  set d := Fintype.card (Module.Free.ChooseBasisIndex ℤ M) - 1 with hd
  let e : Module.Free.ChooseBasisIndex ℤ M ≃ Fin (d + 1) := Fintype.equivFinOfCardEq (by omega)
  set B : Fin (d + 1) → ℝ := fun k => ((b (e.symm k) : M) : ℝ) with hBdef
  have hB0 : B 0 ≠ 0 := by
    intro h; apply b.ne_zero (e.symm 0); exact Subtype.ext h
  set a : ℝ → Fin (d + 1) → ℤ := fun x k =>
    if hx : x ∈ M then b.repr ⟨x, hx⟩ (e.symm k) else 0 with ha
  have hsum : ∀ x ∈ X, x = ∑ k, (a x k : ℝ) * B k := by
    intro x hx
    have hxM : x ∈ M := Submodule.subset_span hx
    have hcoe := congrArg Subtype.val (b.sum_repr ⟨x, hxM⟩)
    rw [Submodule.coe_sum] at hcoe
    simp only [Submodule.coe_smul, zsmul_eq_mul] at hcoe
    rw [← e.symm.sum_comp] at hcoe
    refine hcoe.symm.trans (Finset.sum_congr rfl fun k _ => ?_)
    simp [ha, hxM, hBdef]
  set β : Fin d → ℝ := fun j => B j.succ / B 0 with hβdef
  refine ⟨d, β, ?_, B 0, hB0, a, fun x hx => ?_⟩
  · apply noRelation_of_int
    intro c0 c h
    set g : Fin (d + 1) → ℤ := Fin.cons c0 c with hg
    have hrel : ∑ k, (g k : ℝ) * B k = 0 := by
      rw [Fin.sum_univ_succ]
      simp only [hg, Fin.cons_zero, Fin.cons_succ]
      have : (c0 : ℝ) * B 0 + ∑ j, (c j : ℝ) * B j.succ =
          B 0 * ((c0 : ℝ) + ∑ j, (c j : ℝ) * β j) := by
        rw [mul_add, Finset.mul_sum]
        congr 1
        · ring
        · exact Finset.sum_congr rfl fun j _ => by rw [hβdef]; field_simp
      rw [this, h, mul_zero]
    have hli := b.linearIndependent.comp e.symm e.symm.injective
    rw [Fintype.linearIndependent_iff] at hli
    have hg0 := hli g (by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Function.comp_apply, Submodule.coe_smul, zsmul_eq_mul, Submodule.coe_zero]
      exact hrel)
    refine ⟨by simpa [hg] using hg0 0, funext fun j => by simpa [hg] using hg0 j.succ⟩
  · conv_lhs => rw [hsum x hx]
    rw [speed, Fin.sum_univ_succ, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [hβdef]; field_simp

/-! ## Speeds of zero and parallel rows -/

theorem speed_zero {d : ℕ} (β : Fin d → ℝ) : speed β 0 = 0 := by simp [speed]

/-- Parallel rows have proportional speeds. -/
theorem speed_mul_of_parallel {d : ℕ} (β : Fin d → ℝ) {r s : Fin (d + 1) → ℤ} (h : Parallel r s)
    (p : Fin (d + 1)) : speed β r * s p = r p * speed β s := by
  simp only [speed, add_mul, mul_add, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · exact_mod_cast h 0 p
  · refine Finset.sum_congr rfl fun j _ => ?_
    have := h j.succ p
    have hc : (r j.succ : ℝ) * s p = r p * s j.succ := by exact_mod_cast this
    linear_combination (β j) * hc

end LRC.OrderFiveN
