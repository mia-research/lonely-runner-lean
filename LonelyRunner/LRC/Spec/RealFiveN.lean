import LonelyRunner.LRC.Spec.ManyDirectionsN
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# The conjecture at five runners, for every arrangement of real speeds

2026-09-24.  Every set of at most four positive real disparities is lonely at `1/5`
(`existenceAtN_five`), so the Lonely Runner Conjecture holds at five runners for all real speeds
(`lonelyRunnerAtN_five`).  Everything is exhibited inside the framework.

* **Rows.**  The whole-number span of the disparities is a free group with a finite basis
  `B₀, …, B_d`; each disparity is `B₀ · (r₀ + Σ rⱼ₊₁ βⱼ)` with whole-number row `r` and
  `βⱼ = Bⱼ₊₁ / B₀`, and `1, β` carry no rational relation (`exists_rows`).
* **One class.**  If every two rows are parallel, all the disparities are whole multiples of one
  unit, and order five for whole numbers (`lonely_five_nat`) settles them, scaled.
* **More than one class.**  Otherwise the exact merge (`exists_merge_model_gen`, which allows
  parallel rows) gives a whole-number model with at most three distinct runners; order four gives
  the margin `1/20`; stepping (`lonely_of_model_many`) carries the model instant to a real time.
  No density, no measure.

Everything here is proved; no `sorry`, no `native_decide`.
-/

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

theorem fin4_fifth {i j k l1 l2 : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (h1i : l1 ≠ i) (h1j : l1 ≠ j) (h1k : l1 ≠ k) (h2i : l2 ≠ i) (h2j : l2 ≠ j) (h2k : l2 ≠ k) :
    l1 = l2 := by
  revert i j k l1 l2; decide

/-- **The exact merge, general.**  Four non-zero rows, not all parallel, have a whole-number
direction whose readings are all non-zero, with two of them equal up to sign. -/
theorem exists_merge_model_gen (a : Fin 4 → Fin m → ℤ) (hnz : ∀ i, a i ≠ 0)
    (hnp : ∃ i j, ¬ Parallel (a i) (a j)) :
    ∃ y : Fin m → ℤ, (∀ i, dotZ y (a i) ≠ 0) ∧
      ∃ i j, i ≠ j ∧ (dotZ y (a i)).natAbs = (dotZ y (a j)).natAbs := by
  classical
  by_cases hall : ∀ i j, i ≠ j → ¬ Parallel (a i) (a j)
  · obtain ⟨y, hy, hm⟩ := exists_merge_model_many a hall
    rcases hm with h | h
    · exact ⟨y, hy, 0, 1, by decide, h⟩
    · exact ⟨y, hy, 0, 2, by decide, h⟩
  push Not at hall
  obtain ⟨i, k, hik, hpar⟩ := hall
  -- a row not parallel to `a i`
  obtain ⟨j, hj⟩ : ∃ j, ¬ Parallel (a i) (a j) := by
    by_contra H
    push Not at H
    obtain ⟨i', j', hn⟩ := hnp
    exact hn (parallel_trans (hnz i) (parallel_symm (H i')) (H j'))
  have hij : i ≠ j := fun h => hj (h ▸ parallel_refl _)
  have hjk : j ≠ k := fun h => hj (h ▸ hpar)
  -- the two merge directions `a i ∓ a j`
  set dε : ℤ → Fin m → ℤ := fun ε q => a i q - ε * a j q with hdε
  have hε1 : ∀ ε : ℤ, ε * ε = 1 → dε ε ≠ 0 := by
    intro ε hε h0
    apply hj
    intro q r
    have hq := congrFun h0 q
    have hr := congrFun h0 r
    simp only [hdε, Pi.zero_apply] at hq hr
    linear_combination (a j r) * hq - (a j q) * hr
  have hi_not : ∀ ε : ℤ, ε * ε = 1 → ¬ Parallel (a i) (dε ε) := by
    intro ε hε P
    apply hj
    intro q r
    have := P q r
    simp only [hdε] at this
    linear_combination (-ε) * this - (a i q * a j r - a i r * a j q) * hε
  have hj_not : ∀ ε : ℤ, ¬ Parallel (a j) (dε ε) := by
    intro ε P
    apply hj
    intro q r
    have := P q r
    simp only [hdε] at this
    linear_combination (-1 : ℤ) * this
  have hk_not : ∀ ε : ℤ, ε * ε = 1 → ¬ Parallel (a k) (dε ε) := fun ε hε P =>
    hi_not ε hε (parallel_trans (hnz k) hpar P)
  have hboth : ∀ l, ¬ (Parallel (a l) (dε 1) ∧ Parallel (a l) (dε (-1))) := by
    rintro l ⟨P1, P2⟩
    have P := parallel_trans (hnz l) (parallel_symm P1) P2
    apply hj
    intro q r
    have := P q r
    simp only [hdε] at this
    have h2 : 2 * (a i q * a j r - a i r * a j q) = 0 := by linear_combination this
    linarith
  -- pick the sign whose direction no row is parallel to
  obtain ⟨ε, hε, hfree⟩ : ∃ ε : ℤ, ε * ε = 1 ∧ ∀ l, ¬ Parallel (a l) (dε ε) := by
    by_cases h1 : ∀ l, ¬ Parallel (a l) (dε 1)
    · exact ⟨1, by norm_num, h1⟩
    by_cases h2 : ∀ l, ¬ Parallel (a l) (dε (-1))
    · exact ⟨-1, by norm_num, h2⟩
    exfalso
    push Not at h1 h2
    obtain ⟨l1, P1⟩ := h1
    obtain ⟨l2, P2⟩ := h2
    have n1i : l1 ≠ i := fun h => hi_not 1 (by norm_num) (h ▸ P1)
    have n1j : l1 ≠ j := fun h => hj_not 1 (h ▸ P1)
    have n1k : l1 ≠ k := fun h => hk_not 1 (by norm_num) (h ▸ P1)
    have n2i : l2 ≠ i := fun h => hi_not (-1) (by norm_num) (h ▸ P2)
    have n2j : l2 ≠ j := fun h => hj_not (-1) (h ▸ P2)
    have n2k : l2 ≠ k := fun h => hk_not (-1) (by norm_num) (h ▸ P2)
    have heq := fin4_fifth hij hik hjk n1i n1j n1k n2i n2j n2k
    exact hboth l1 ⟨P1, heq ▸ P2⟩
  obtain ⟨y, hy0, hy⟩ := exists_perp_avoid (dε ε) (hε1 ε hε) a hfree
  refine ⟨y, hy, i, j, hij, ?_⟩
  have hsub := dotZ_sub_smul y (a i) (a j) ε
  have hzero : dotZ y (a i) = ε * dotZ y (a j) := by
    have : dotZ y (fun q => a i q - ε * a j q) = 0 := hy0
    linarith
  rw [hzero, Int.natAbs_mul]
  have : ε.natAbs = 1 := by
    have := congrArg Int.natAbs hε
    rw [Int.natAbs_mul] at this
    simpa using Nat.eq_one_of_mul_eq_one_right this
  rw [this, one_mul]

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

/-! ## Order five, every real arrangement -/

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

/-- **Order five, real speeds.**  Every set of at most four positive real disparities is lonely at
`1/5`. -/
theorem existenceAtN_five : ExistenceAtN 5 := by
  intro ds hpos hcard
  classical
  by_cases h3 : ds.card ≤ 3
  · obtain ⟨t, ht, hl⟩ := existenceAtN_four ds hpos (by simpa using h3)
    refine ⟨t, ht, fun d hd => le_trans ?_ (hl d hd)⟩
    norm_num
  have h4 : ds.card = 4 := by
    have : ds.card ≤ 4 := by simpa using hcard
    omega
  obtain ⟨d, β, hβ, l, hl0, a, hrep⟩ :=
    exists_rows ds (fun x hx => (hpos x hx).ne') (Finset.card_pos.mp (by omega))
  set e4 := ds.equivFinOfCardEq h4 with he4
  set xs : Fin 4 → ℝ := fun i => ((e4.symm i : ds) : ℝ) with hxs
  have hxs_mem : ∀ i, xs i ∈ ds := fun i => (e4.symm i).2
  have hxs_pos : ∀ i, 0 < xs i := fun i => hpos _ (hxs_mem i)
  set A : Fin 4 → Fin (d + 1) → ℤ := fun i => a (xs i) with hAdef
  have hxA : ∀ i, xs i = l * speed β (A i) := fun i => hrep _ (hxs_mem i)
  have hAnz : ∀ i, A i ≠ 0 := by
    intro i h
    have := hxA i
    rw [h, speed_zero, mul_zero] at this
    exact (hxs_pos i).ne' this
  have hcover : ∀ x ∈ ds, ∃ i, xs i = x := fun x hx => ⟨e4 ⟨x, hx⟩, by simp [hxs]⟩
  suffices H : ∃ t : ℝ, 0 < t ∧ ∀ i, (5 : ℝ)⁻¹ ≤ circDist (xs i * t) by
    obtain ⟨t, ht, hlt⟩ := H
    refine ⟨t, ht, fun x hx => ?_⟩
    obtain ⟨i, rfl⟩ := hcover x hx
    simpa using hlt i
  by_cases hallpar : ∀ i j, Parallel (A i) (A j)
  · -- one commensurability class: whole multiples of one unit
    obtain ⟨p, hp⟩ := Function.ne_iff.mp (hAnz 0)
    have hp' : (A 0 p : ℝ) ≠ 0 := by exact_mod_cast hp
    set u0 : ℝ := l * speed β (A 0) / (A 0 p : ℝ) with hu0
    have hxu : ∀ i, xs i = u0 * (A i p : ℝ) := by
      intro i
      have hsp := speed_mul_of_parallel β (hallpar i 0) p
      rw [hxA i, hu0]
      field_simp
      linear_combination hsp
    set mm : Fin 4 → ℕ := fun i => (A i p).natAbs with hmm
    have hxm : ∀ i, xs i = |u0| * mm i := by
      intro i
      have hpi := hxs_pos i
      rw [hxu i] at hpi ⊢
      rw [← abs_of_pos hpi, abs_mul, hmm]
      simp only [Nat.cast_natAbs, Int.cast_abs]
    have hmpos : ∀ i, 0 < mm i := by
      intro i
      rcases Nat.eq_zero_or_pos (mm i) with h | h
      · have := hxm i; rw [h] at this; simp at this; exact absurd this (hxs_pos i).ne'
      · exact h
    have hu : 0 < |u0| := by
      have := hxm 0
      have h0 := hxs_pos 0
      rw [this] at h0
      have : (0 : ℝ) < mm 0 := by exact_mod_cast hmpos 0
      exact pos_of_mul_pos_left h0 this.le
    obtain ⟨t, ht, hlt⟩ := lonely_five_nat (Finset.univ.image mm)
      (fun x hx => by obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx; exact hmpos i)
      (le_trans Finset.card_image_le (by simp))
    refine ⟨t / |u0|, by positivity, fun i => ?_⟩
    rw [hxm i, show |u0| * (mm i : ℝ) * (t / |u0|) = (mm i : ℝ) * t by field_simp]
    exact hlt _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  · -- more than one class: the exact merge, order four, stepping
    push Not at hallpar
    obtain ⟨i0, j0', hnp⟩ := hallpar
    obtain ⟨y, hy, i1, j1, hij, hm⟩ := exists_merge_model_gen A hAnz ⟨i0, j0', hnp⟩
    have hd : 0 < d := by
      by_contra hd0
      apply hnp
      intro q r
      have hqr : q = r := by
        apply Fin.ext
        have := q.isLt; have := r.isLt; omega
      rw [hqr]
    set j0 : Fin d := ⟨0, hd⟩
    set w : Fin 4 → ℝ := fun i => |((dotZ y (A i) : ℤ) : ℝ)| with hw
    set W : Finset ℝ := Finset.univ.image w with hW
    have hWpos : ∀ x ∈ W, 0 < x := by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact abs_pos.mpr (by exact_mod_cast hy i)
    have hWcard : W.card ≤ 3 := by
      have hle : W.card ≤ 4 := le_trans Finset.card_image_le (by simp)
      by_contra hgt
      have h4' : W.card = (Finset.univ : Finset (Fin 4)).card := by simp; omega
      have hinj := Finset.card_image_iff.mp h4'
      apply hij
      apply hinj (Finset.mem_coe.mpr (Finset.mem_univ i1)) (Finset.mem_coe.mpr (Finset.mem_univ j1))
      simp only [hw]
      rw [← Int.cast_abs, ← Int.cast_abs, Int.abs_eq_natAbs, Int.abs_eq_natAbs, hm]
    obtain ⟨τ, -, hlτ⟩ := existenceAtN_four W hWpos (by simpa using hWcard)
    have hτ : ∀ r ∈ Finset.univ.image A, ((5 : ℕ) - 1 : ℝ)⁻¹ ≤ circDist ((dotZ y r : ℝ) * τ) := by
      intro r hr
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hr
      have := hlτ (w i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
      simp only [hw] at this
      rw [circDist_abs_mul] at this
      have h54 : ((5 : ℕ) - 1 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
      rw [h54]; exact this
    obtain ⟨t, ht, hlt⟩ := lonely_of_model_many (n := 5) (by norm_num) hβ j0
      ⟨A 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩ y hτ
    refine ⟨t / |l|, div_pos ht (abs_pos.mpr hl0), fun i => ?_⟩
    have := hlt (A i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    rw [hxA i]
    rcases abs_choice l with h | h
    · rw [h, show l * speed β (A i) * (t / l) = speed β (A i) * t by field_simp]
      simpa using this
    · rw [h, show l * speed β (A i) * (t / -l) = -(speed β (A i) * t) by field_simp,
        circDist.symm_neg]
      simpa using this

/-- **The Lonely Runner Conjecture at five runners**, for every injective arrangement of real
speeds, proved inside the framework. -/
theorem lonelyRunnerAtN_five : LonelyRunnerAtN 5 :=
  lonelyRunnerAtN_of_existence existenceAtN_five

end LRC.OrderFiveN
