import LonelyRunner.LRC.Spec.RealSevenN
import LonelyRunner.LRC.Spec.PathRouteN

/-!
# One free reading at order eight

2026-09-27.  Running record: `RUNNING_LOG_order8_v1.md` E116.

A move of the path route (`PathWindowN`) changes one runner's speed while six readings stay fixed.  If the six fixed
readings have a common period `P` (every `(v j − v k)·P` a whole number) and the moving reading is **off that lattice**
(`(v i − v k)·P` not a whole number), the subject is lonely, by native order seven alone:

* order seven clears the six fixed readings at `1/7` at some `t₇` (`OrderSevenN.existenceAtN_seven`);
* at `t₇ + m·P` the six are exactly where they were, while the moving runner steps by `α = (v i − v k)·P` each period;
* `α` is not whole, so some `m` puts the moving runner at least `1/8` from the subject (`exists_clear_step`):
  if `‖α‖ = a ≥ 1/4`, one step; otherwise `m = ⌈1/(4a)⌉` steps carry it to between `1/4` and `1/2`.

So along a move every arrangement off the lattice is lonely, and only the lattice points, where every reading is a whole
multiple of `1/P`, remain.  No density, no measure: the step count is written down.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.OneFree

open Arrangement

/-- The nearest whole number realises the circle distance. -/
theorem exists_near_int (x : ℝ) : ∃ z : ℤ, |x - z| = circDist x := by
  unfold circDist
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  by_cases h : Int.fract x ≤ 1 - Int.fract x
  · refine ⟨⌊x⌋, ?_⟩
    rw [min_eq_left h, ← Int.self_sub_floor, abs_of_nonneg (by rw [Int.self_sub_floor]; exact h0)]
  · refine ⟨⌊x⌋ + 1, ?_⟩
    rw [min_eq_right (le_of_not_ge h)]
    have e : x - ((⌊x⌋ + 1 : ℤ) : ℝ) = Int.fract x - 1 := by
      rw [← Int.self_sub_floor]; push_cast; ring
    rw [e, abs_of_neg (by linarith)]; ring

/-- Within half a lap of a whole number, the circle distance is the plain distance. -/
theorem circDist_eq_abs {x : ℝ} (h : |x| ≤ 1 / 2) : circDist x = |x| := by
  have key : ∀ y : ℝ, 0 ≤ y → y ≤ 1 / 2 → circDist y = y := by
    intro y hy0 hy1
    unfold circDist
    have hf : Int.fract y = y := Int.fract_eq_self.mpr ⟨hy0, by linarith⟩
    rw [hf, min_eq_left (by linarith)]
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx] at h ⊢; exact key x hx h
  · rw [abs_of_neg hx] at h ⊢
    rw [← LRC.PinchOpen.circDist_neg_po x]; exact key (-x) (by linarith) h

/-- The circle distance of a sum is at least that of one term less that of the other. -/
theorem circDist_sub_le (x y : ℝ) : circDist y - circDist x ≤ circDist (x + y) := by
  obtain ⟨z, hz⟩ := exists_near_int x
  have e : x + y = (y + (x - z)) + (z : ℝ) := by ring
  rw [e, LRC.PinchOpen.circDist_add_int_po]
  have hlip := circDist_lipschitz.dist_le_mul (y + (x - z)) y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, add_sub_cancel_left] at hlip
  have := (abs_sub_le_iff.mp hlip).2
  linarith

/-- **A step that is not whole carries the runner a quarter lap away, in finitely many steps.** -/
theorem exists_far_multiple {α : ℝ} (hα : ∀ z : ℤ, α ≠ z) : ∃ m : ℕ, (1 : ℝ) / 4 ≤ circDist (m * α) := by
  obtain ⟨z, hz⟩ := exists_near_int α
  set a := circDist α with ha
  have ha0 : 0 < a := by
    rcases (circDist.nonneg α).lt_or_eq with h | h
    · exact h
    · exfalso; apply hα z
      have : |α - z| = 0 := by rw [hz]; exact h.symm
      linarith [abs_eq_zero.mp this]
  have hahalf : a ≤ 1 / 2 := circDist.le_half α
  -- `m α = m z + m r`, `|r| = a`
  set r := α - z with hr
  have hm : ∀ m : ℕ, circDist (m * α) = circDist (m * r) := by
    intro m
    have e : (m : ℝ) * α = m * r + ((m * z : ℤ) : ℝ) := by rw [hr]; push_cast; ring
    rw [e, LRC.PinchOpen.circDist_add_int_po]
  rcases le_or_gt ((1 : ℝ) / 4) a with h4 | h4
  · refine ⟨1, ?_⟩
    rw [hm, Nat.cast_one, one_mul, circDist_eq_abs (by rw [hz]; exact hahalf), hz]; exact h4
  · set m : ℕ := ⌈1 / (4 * a)⌉₊ with hmdef
    have hc1 : 1 / (4 * a) ≤ (m : ℝ) := Nat.le_ceil _
    have hc2 : (m : ℝ) < 1 / (4 * a) + 1 := Nat.ceil_lt_add_one (by positivity)
    have hma1 : (1 : ℝ) / 4 ≤ m * a := by
      have := mul_le_mul_of_nonneg_right hc1 ha0.le
      have e : 1 / (4 * a) * a = 1 / 4 := by field_simp
      linarith
    have hma2 : (m : ℝ) * a < 1 / 2 := by
      have := mul_lt_mul_of_pos_right hc2 ha0
      have e : (1 / (4 * a) + 1) * a = 1 / 4 + a := by field_simp
      rw [e] at this; linarith
    have habs : |(m : ℝ) * r| = m * a := by
      rw [abs_mul, Nat.abs_cast, hz]
    refine ⟨m, ?_⟩
    rw [hm, circDist_eq_abs (by rw [habs]; linarith), habs]; exact hma1

/-- **Some step count puts the moving runner clear**, from any start `θ`, when the step `α` is not whole. -/
theorem exists_clear_step (θ : ℝ) {α : ℝ} (hα : ∀ z : ℤ, α ≠ z) :
    ∃ m : ℕ, (8 : ℝ)⁻¹ ≤ circDist (θ + m * α) := by
  rcases le_or_gt (8 : ℝ)⁻¹ (circDist θ) with h | h
  · exact ⟨0, by simpa using h⟩
  · obtain ⟨m, hm⟩ := exists_far_multiple hα
    refine ⟨m, ?_⟩
    have := circDist_sub_le θ (m * α)
    linarith

/-- **One free reading at order eight.**  Six readings with a common period `P`, a seventh off their lattice: the
subject is lonely (at `t₇ + m·P`, where order seven clears the six at `t₇`). -/
theorem lonely_of_one_free_eight {v : Fin 8 → ℝ} {k i : Fin 8} (hki : k ≠ i)
    (hpos : ∀ j : Fin 8, j ≠ k → 0 < v j - v k) {P : ℝ} (hP : 0 < P)
    (hper : ∀ j : Fin 8, j ≠ i → ∃ z : ℤ, (v j - v k) * P = z)
    (hfree : ∀ z : ℤ, (v i - v k) * P ≠ z) : LRC.Spec.LonelyForSubject v k := by
  classical
  set S : Finset (Fin 8) := (Finset.univ.erase k).erase i with hS
  set ds : Finset ℝ := S.image (fun j => v j - v k) with hds
  have hSmem : ∀ j, j ∈ S ↔ j ≠ i ∧ j ≠ k := by
    intro j; simp [hS]
  have hcardS : S.card = 6 := by
    rw [hS, Finset.card_erase_of_mem (by simp [Ne.symm hki]), Finset.card_erase_of_mem (Finset.mem_univ k)]
    simp
  have hcard : ds.card ≤ 7 - 1 := by
    have := Finset.card_image_le (s := S) (f := fun j => v j - v k)
    rw [hcardS] at this; simpa using this
  have hdpos : ∀ d ∈ ds, 0 < d := by
    intro d hd
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
    exact hpos j ((hSmem j).mp hj).2
  obtain ⟨t7, ht7, hl7⟩ := LRC.OrderSevenN.existenceAtN_seven ds hdpos hcard
  obtain ⟨m, hm⟩ := exists_clear_step ((v i - v k) * t7) hfree
  refine ⟨t7 + m * P, by positivity, fun j hjk => ?_⟩
  rw [sep_eq]
  by_cases hji : j = i
  · subst hji
    have e : (v j - v k) * (t7 + m * P) = (v j - v k) * t7 + m * ((v j - v k) * P) := by ring
    rw [e]; exact hm
  · obtain ⟨z, hz⟩ := hper j hji
    have e : (v j - v k) * (t7 + m * P) = (v j - v k) * t7 + ((m * z : ℤ) : ℝ) := by
      push_cast; rw [← hz]; ring
    rw [e, LRC.PinchOpen.circDist_add_int_po]
    have hmem : v j - v k ∈ ds := Finset.mem_image.mpr ⟨j, (hSmem j).mpr ⟨hji, hjk⟩, rfl⟩
    have h7 := hl7 _ hmem
    have : ((7 : ℕ) : ℝ)⁻¹ ≥ (8 : ℝ)⁻¹ := by norm_num
    linarith

end LRC.OneFree
