import LonelyRunner.LRC.Spec.FastRunnerN
import LonelyRunner.LRC.Spec.DescentMultiN
import LonelyRunner.LRC.Spec.ShiftedTotientN

/-!
# Order five, whole-number disparities: everything but one sub-case, inside the framework

2026-09-24.  A subject at order five has at most four disparities.  Split them by divisibility
by `5`, and let `M` count the multiples.

* `M = 0`: the instant `1/5` is lonely — R6 at `q = 5` (`lonely_five_of_no_multiple`).
* `M ≥ 2` (and not every disparity a multiple): at most two non-multiples, each of cost
  `max 2 (gcd e 5) = 2`, total `≤ 4 < 5`, so the descent passes the set to the cofactors of its
  multiples, at most three of them, which the framework settles at `1/5`
  (`lonely_five_of_descent`).
* `M = 1`, the multiple the largest disparity: R4, the divisible flank, with at most three
  non-flank disparities against the four units of `ℤ/5` (`lonely_five_of_largest_multiple`).

What is left (`lonely_five_or_residual`) is exactly one multiple of `5` that is **not** the
largest disparity.  That is the sub-case the fastest runner's flank carries; it is treated
separately.

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.OrderFiveN

open MomentIterationN LRC.SpecN LRC.Descent LRC.Resonance LRC.FlankFinite

/-- A disparity not divisible by `5` has `gcd` one with `5`, read off its residue. -/
theorem gcd_five_of_not_dvd {e : ℕ} (h : ¬ 5 ∣ e) : Nat.gcd e 5 = 1 := by
  have h5 : e % 5 ≠ 0 := fun h0 => h (Nat.dvd_of_mod_eq_zero h0)
  have hlt : e % 5 < 5 := Nat.mod_lt _ (by norm_num)
  rw [Nat.gcd_comm, Nat.gcd_rec]
  interval_cases hm : e % 5 <;> first | omega | decide

/-- At most three positive disparities are lonely at `1/5`. -/
theorem lonely_five_of_card_le_three {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d) (hc : S.card ≤ 3) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (5 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  obtain ⟨t, ht, hl⟩ := exists_lonely_of_card_le_three (n := 5)
    (ds := S.image (fun d : ℕ => (d : ℝ))) (by norm_num)
    (by
      intro x hx
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      exact_mod_cast hpos d hd)
    (le_trans Finset.card_image_le hc)
  refine ⟨t, ht, fun d hd => ?_⟩
  have := hl (d : ℝ) (Finset.mem_image_of_mem _ hd)
  simpa using this

/-- **No multiple of five**: the instant `1/5` is lonely (R6 at `q = 5`). -/
theorem lonely_five_of_no_multiple {S : Finset ℕ} (h : ∀ d ∈ S, ¬ 5 ∣ d) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (5 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  refine ⟨1 / 5, by norm_num, fun d hd => ?_⟩
  have hnd : ¬ ((5 : ℕ) : ℤ) ∣ (d : ℤ) := by exact_mod_cast h d hd
  have := ConstructionN.circDist_int_div (n := 5) (by norm_num) hnd
  have heq : ((d : ℤ) : ℝ) / ((5 : ℕ) : ℝ) = (d : ℝ) * (1 / 5) := by push_cast; ring
  rw [heq] at this
  simpa using this

/-- **At most two non-multiples and at most three multiples**: the descent. -/
theorem lonely_five_of_descent {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d)
    (hE : (S.filter (fun d => ¬ 5 ∣ d)).card ≤ 2) (hM : (S.filter (fun d => 5 ∣ d)).card ≤ 3) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (5 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  set E := S.filter (fun d => ¬ 5 ∣ d) with hEdef
  set C : Finset ℕ := (S.filter (fun d => 5 ∣ d)).image (fun d => d / 5) with hCdef
  have hcost : ∑ e ∈ E, max 2 (Nat.gcd e 5) < 5 := by
    have h2 : ∀ e ∈ E, max 2 (Nat.gcd e 5) = 2 := fun e he => by
      rw [gcd_five_of_not_dvd (Finset.mem_filter.mp he).2]; rfl
    rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul]
    omega
  have hCpos : ∀ m ∈ C, 0 < m := by
    intro m hm
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hdS, h5⟩ := Finset.mem_filter.mp hd
    exact Nat.div_pos (Nat.le_of_dvd (hpos d hdS) h5) (by norm_num)
  obtain ⟨τ, hτ, hC⟩ := lonely_five_of_card_le_three hCpos (le_trans Finset.card_image_le hM)
  obtain ⟨t, ht, hEt, hMt⟩ := (lonely_multi_descent_iff (n := 5) (by norm_num) E C.toList hcost).mpr
    ⟨τ, hτ, fun m hm => by simpa using hC m (Finset.mem_toList.mp hm)⟩
  refine ⟨t, ht, fun d hd => ?_⟩
  by_cases h5 : 5 ∣ d
  · obtain ⟨m, rfl⟩ := h5
    have hmC : m ∈ C.toList := Finset.mem_toList.mpr (Finset.mem_image.mpr
      ⟨5 * m, Finset.mem_filter.mpr ⟨hd, dvd_mul_right 5 m⟩, by omega⟩)
    simpa using hMt m hmC
  · simpa using hEt d (Finset.mem_filter.mpr ⟨hd, h5⟩)

/-- **One multiple of five, and it is the largest disparity**: R4, the divisible flank. -/
theorem lonely_five_of_largest_multiple {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d)
    (hcard : S.card ≤ 4) {e : ℕ} (heS : e ∈ S) (he5 : 5 ∣ e)
    (hothers : ∀ d ∈ S, d ≠ e → ¬ 5 ∣ d) (hlarg : ∀ d ∈ S, d ≤ e) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (5 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  set L := (S.erase e).toList with hL
  have hmemL : ∀ d ∈ L, d ∈ S ∧ d ≠ e := fun d hd => by
    have := Finset.mem_toList.mp hd
    exact ⟨Finset.mem_of_mem_erase this, Finset.ne_of_mem_erase this⟩
  have hlen : L.length ≤ 3 := by
    rw [hL, Finset.length_toList, Finset.card_erase_of_mem heS]; omega
  have htot : Nat.totient 5 = 4 := by decide
  have hfw : flankWorks 5 (e :: L) e = true :=
    flankWorks_of_dvd_totient (n := 5) L e (hpos e heS) he5
      (fun d hd => hothers d (hmemL d hd).1 (hmemL d hd).2)
      (fun d hd => lt_of_le_of_ne (hlarg d (hmemL d hd).1) (hmemL d hd).2)
      (by rw [htot]; exact lt_of_le_of_lt (List.length_filter_le _ _) (by omega))
  obtain ⟨j, hj⟩ := lonely_of_flankWorks (n := 5) (e :: L) e (hpos e heS) hfw
  refine ⟨Flanks.flankOpening 5 (e : ℝ) j,
    Flanks.flankOpening_pos (n := 5) (by exact_mod_cast hpos e heS) j, fun d hd => ?_⟩
  have hdL : d ∈ e :: L := by
    by_cases h : d = e
    · rw [h]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨h, hd⟩))
  simpa using hj d hdL

/-- **Order five, whole numbers.**  A set of at most four positive disparities, not all divisible
by `5`, is lonely at `1/5`, unless it has exactly one multiple of `5` and that multiple is not
the largest disparity. -/
theorem lonely_five_or_residual {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d) (hcard : S.card ≤ 4)
    (hprim : ∃ d ∈ S, ¬ 5 ∣ d) :
    (∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (5 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t)) ∨
      ((S.filter (fun d => 5 ∣ d)).card = 1 ∧ ∃ e ∈ S, 5 ∣ e ∧ ∃ d ∈ S, e < d) := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (fun d => 5 ∣ d)
  have hE1 : 1 ≤ (S.filter (fun d => ¬ 5 ∣ d)).card := by
    obtain ⟨d, hd, h5⟩ := hprim
    exact Finset.card_pos.mpr ⟨d, Finset.mem_filter.mpr ⟨hd, h5⟩⟩
  rcases Nat.lt_or_ge (S.filter (fun d => 5 ∣ d)).card 1 with h0 | h1
  · left
    apply lonely_five_of_no_multiple
    intro d hd h5
    have : (S.filter (fun d => 5 ∣ d)).card = 0 := by omega
    rw [Finset.card_eq_zero] at this
    have hmem : d ∈ S.filter (fun d => 5 ∣ d) := Finset.mem_filter.mpr ⟨hd, h5⟩
    rw [this] at hmem
    exact absurd hmem (Finset.notMem_empty d)
  · rcases Nat.lt_or_ge (S.filter (fun d => 5 ∣ d)).card 2 with hone | h2
    · have hc1 : (S.filter (fun d => 5 ∣ d)).card = 1 := by omega
      obtain ⟨e, he⟩ := Finset.card_eq_one.mp hc1
      have heS : e ∈ S := (Finset.mem_filter.mp (he ▸ Finset.mem_singleton_self e)).1
      have he5 : 5 ∣ e := (Finset.mem_filter.mp (he ▸ Finset.mem_singleton_self e)).2
      have hothers : ∀ d ∈ S, d ≠ e → ¬ 5 ∣ d := by
        intro d hd hne h5
        have hmem : d ∈ S.filter (fun d => 5 ∣ d) := Finset.mem_filter.mpr ⟨hd, h5⟩
        rw [he, Finset.mem_singleton] at hmem
        exact hne hmem
      by_cases hbig : ∃ d ∈ S, e < d
      · exact Or.inr ⟨hc1, e, heS, he5, hbig⟩
      · push Not at hbig
        exact Or.inl (lonely_five_of_largest_multiple hpos hcard heS he5 hothers hbig)
    · left
      exact lonely_five_of_descent hpos (by omega) (by omega)

end LRC.OrderFiveN
