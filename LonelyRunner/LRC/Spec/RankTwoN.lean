import LonelyRunner.LRC.Spec.TwoGroupsN

/-!
# Real speeds on two independent directions: the exact merge

2026-09-24.  Let the disparities be `aᵢ + cᵢ·α` with `α` irrational and whole-number rows
`(aᵢ, cᵢ)`.  Pairwise non-parallel rows are exactly pairwise incommensurable speeds, so this
carries the class structure `1 + 1 + 1 + 1` whenever the speeds span two directions.

* **The model.**  A whole-number direction `y` reads each row as `wᵢ = aᵢ y₁ + cᵢ y₂`.  Choose
  `y` so that two readings coincide up to sign — the merge rule, made exact
  (`exists_merge_model`).  The model then has at most three distinct runners, all non-zero.
* **The order below.**  Three runners are lonely at `1/4` (order four, inside the framework), at
  an instant `τ`.  Against `1/5` that is a margin of `1/20` on every runner.
* **To a real time.**  Take `t = τ y₁ + K` for a whole number `K`: the `aᵢ t` part is read exactly.
  The `cᵢ α t` part needs `α t` within `η` of `τ y₂`; one Dirichlet step `k₀α − j` of size at
  most `η`, then stepping, puts it there (`lonely_of_model`).  The margin absorbs `cᵢ η`.

`lonely_of_model` holds at every order `n`: a model instant at the threshold of the order below
becomes a real lonely instant at `1/n`.  At order five the model comes from `exists_merge_model`
(`lonely_five_rank_two`).  No density, no measure: one pigeonhole and a walk.

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.OrderFiveN

open MomentIterationN LRC.SpecN ConstructionN

/-- The cross product of two whole-number rows; zero exactly when they are parallel. -/
def cross (r s : ℤ × ℤ) : ℤ := r.1 * s.2 - r.2 * s.1

/-- The model's reading of a row along the whole-number direction `y`. -/
def reading (y r : ℤ × ℤ) : ℤ := r.1 * y.1 + r.2 * y.2

/-! ## From a model instant to a real time, at every order -/

/-- **The model carries to the reals.**  If along the whole-number direction `y` every row's
reading is clear at `1/(n − 1)` at `τ`, the real speeds `a + c·α` (`α` irrational) are lonely at
`1/n` at some `t > 0`. -/
theorem lonely_of_model {n : ℕ} (hn : 2 ≤ n) {α : ℝ} (hα : Irrational α) {R : Finset (ℤ × ℤ)}
    (hR : R.Nonempty) (y : ℤ × ℤ) {τ : ℝ}
    (hτ : ∀ r ∈ R, ((n : ℝ) - 1)⁻¹ ≤ circDist ((reading y r : ℝ) * τ)) :
    ∃ t : ℝ, 0 < t ∧ ∀ r ∈ R, (n : ℝ)⁻¹ ≤ circDist (((r.1 : ℝ) + r.2 * α) * t) := by
  classical
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  -- the margin, and the tolerance it buys against the largest `c`
  set σ : ℝ := ((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹ with hσ
  have hσ0 : 0 < σ := by
    rw [hσ, sub_pos]; exact inv_strictAnti₀ hn1 (by linarith)
  set C : ℝ := ((R.sup (fun r => r.2.natAbs) : ℕ) : ℝ) + 1 with hC
  have hC0 : 0 < C := by positivity
  have hcC : ∀ r ∈ R, |(r.2 : ℝ)| ≤ C := by
    intro r hr
    have h1 : r.2.natAbs ≤ R.sup (fun r => r.2.natAbs) := Finset.le_sup (f := fun r => r.2.natAbs) hr
    have h2 : |(r.2 : ℝ)| = ((r.2.natAbs : ℕ) : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [h2, hC]
    have : ((r.2.natAbs : ℕ) : ℝ) ≤ ((R.sup (fun r => r.2.natAbs) : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  set η : ℝ := σ / C with hη
  have hη0 : 0 < η := by positivity
  -- one Dirichlet step of `α`, of size at most `η`
  set N : ℕ := ⌈1 / η⌉₊ + 1 with hN
  obtain ⟨j, k0, hk0, -, hdir⟩ := Real.exists_int_int_abs_mul_sub_le α (show 0 < N by omega)
  have hNη : 1 / ((N : ℝ) + 1) ≤ η := by
    have h1 : 1 / η ≤ (⌈1 / η⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (N : ℝ) + 1 = (⌈1 / η⌉₊ : ℝ) + 2 := by rw [hN]; push_cast; ring
    rw [h2, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hη0] at h1
    nlinarith
  set s : ℝ := (k0 : ℝ) * α - j with hs
  have hs0 : s ≠ 0 := ((hα.intCast_mul hk0.ne').sub_intCast j).ne_zero
  have hsη : |s| ≤ η := le_trans hdir hNη
  -- stepping puts `α t` within `η` of `τ y₂`
  set c : ℝ := α * τ * y.1 - τ * y.2 with hc
  obtain ⟨i, K, hiK⟩ := exists_step_near_int c s η hs0 hsη
  set e : ℝ := c + i * s - K with he
  set t0 : ℝ := τ * y.1 + i * k0 with ht0
  have key : ∀ r ∈ R, circDist (((r.1 : ℝ) + r.2 * α) * t0) =
      circDist ((reading y r : ℝ) * τ + r.2 * e) := by
    intro r _
    have heq : ((r.1 : ℝ) + r.2 * α) * t0 = ((reading y r : ℝ) * τ + r.2 * e) +
        ((r.1 * ((i : ℤ) * k0) + r.2 * (K + (i : ℤ) * j) : ℤ) : ℝ) := by
      rw [ht0, he, hc, hs, reading]; push_cast; ring
    rw [heq, circDist_add_int]
  have hclear : ∀ r ∈ R, (n : ℝ)⁻¹ ≤ circDist (((r.1 : ℝ) + r.2 * α) * t0) := by
    intro r hr
    rw [key r hr]
    have hlip := circDist_lipschitz.dist_le_mul ((reading y r : ℝ) * τ + r.2 * e)
      ((reading y r : ℝ) * τ)
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
    have hbound : |(reading y r : ℝ) * τ + r.2 * e - (reading y r : ℝ) * τ| ≤ σ := by
      rw [show (reading y r : ℝ) * τ + r.2 * e - (reading y r : ℝ) * τ = r.2 * e by ring, abs_mul]
      calc |(r.2 : ℝ)| * |e| ≤ C * η :=
            mul_le_mul (hcC r hr) hiK (abs_nonneg _) hC0.le
        _ = σ := by rw [hη]; field_simp
    have h1 := hτ r hr
    have := abs_sub_le_iff.mp hlip
    linarith [this.2]
  -- the instant is not zero, and the sign of time does not matter
  obtain ⟨r0, hr0⟩ := hR
  have ht0ne : t0 ≠ 0 := by
    intro h0
    have := hclear r0 hr0
    rw [h0, mul_zero, show circDist 0 = 0 by simp [circDist]] at this
    have : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
    linarith
  refine ⟨|t0|, abs_pos.mpr ht0ne, fun r hr => ?_⟩
  rcases abs_choice t0 with h | h
  · rw [h]; exact hclear r hr
  · rw [h, mul_neg, circDist.symm_neg]; exact hclear r hr

/-! ## The exact merge at order five -/

/-- Four `2 × 2` minors of four rows in the plane obey the Grassmann–Plücker relation. -/
theorem cross_plucker (r1 r2 r3 r4 : ℤ × ℤ) :
    cross r1 r2 * cross r3 r4 - cross r1 r3 * cross r2 r4 + cross r1 r4 * cross r2 r3 = 0 := by
  simp only [cross]; ring

/-- If none of the four merge directions `r₁ ∓ r₂`, `r₁ ∓ r₃` is free, the minors are forced to
`3·[r₁,r₄]·[r₂,r₃] = 0`. -/
theorem merge_obstruction {A B Cc D E G : ℤ} (hP : A * G - B * E + Cc * D = 0)
    (hC : Cc ≠ 0) (hD : D ≠ 0)
    (h1 : B = D ∨ E = Cc) (h2 : B = -D ∨ E = -Cc) (h3 : A = -D ∨ G = Cc) (h4 : A = D ∨ G = -Cc) :
    False := by
  have h3CD : (3 * Cc) * D ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hC) hD
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    rcases h4 with h4 | h4 <;>
    first
      | exact hD (by linarith)
      | exact hC (by linarith)
      | exact h3CD (by linear_combination hP - G * h3 + D * h4 + E * h1 + D * h2)
      | exact h3CD (by linear_combination hP - G * h4 - D * h3 + E * h1 + D * h2)
      | exact h3CD (by linear_combination hP - G * h3 + D * h4 + E * h2 - D * h1)
      | exact h3CD (by linear_combination hP - G * h4 - D * h3 + E * h2 - D * h1)

/-- The direction perpendicular to `d`: its reading of a row `r` is `−[r, d]`. -/
theorem reading_perp (d r : ℤ × ℤ) : reading (-d.2, d.1) r = -cross r d := by
  simp only [reading, cross]; ring

/-- **The exact merge.**  Four pairwise non-parallel rows have a whole-number direction whose
readings are all non-zero and in which row one coincides, up to sign, with row two or row three. -/
theorem exists_merge_model {r1 r2 r3 r4 : ℤ × ℤ}
    (h12 : cross r1 r2 ≠ 0) (h13 : cross r1 r3 ≠ 0) (h14 : cross r1 r4 ≠ 0)
    (h23 : cross r2 r3 ≠ 0) (h24 : cross r2 r4 ≠ 0) (h34 : cross r3 r4 ≠ 0) :
    ∃ y : ℤ × ℤ, reading y r1 ≠ 0 ∧ reading y r2 ≠ 0 ∧ reading y r3 ≠ 0 ∧ reading y r4 ≠ 0 ∧
      ((reading y r1).natAbs = (reading y r2).natAbs ∨
        (reading y r1).natAbs = (reading y r3).natAbs) := by
  have self : ∀ u : ℤ × ℤ, cross u u = 0 := fun u => by simp only [cross]; ring
  have anti : ∀ u v : ℤ × ℤ, cross v u = -cross u v := fun u v => by simp only [cross]; ring
  have lin : ∀ (u v w : ℤ × ℤ) (ε : ℤ), cross w (v.1 - ε * u.1, v.2 - ε * u.2) =
      cross w v - ε * cross w u := fun u v w ε => by simp only [cross]; ring
  -- a direction `d = r₁ − ε r_k` is free when no row is parallel to it
  have try_dir : ∀ (k : ℤ × ℤ) (ε : ℤ), (ε = 1 ∨ ε = -1) →
      cross r1 (r1.1 - ε * k.1, r1.2 - ε * k.2) ≠ 0 → cross r2 (r1.1 - ε * k.1, r1.2 - ε * k.2) ≠ 0 →
      cross r3 (r1.1 - ε * k.1, r1.2 - ε * k.2) ≠ 0 → cross r4 (r1.1 - ε * k.1, r1.2 - ε * k.2) ≠ 0 →
      (cross k (r1.1 - ε * k.1, r1.2 - ε * k.2)).natAbs = (cross r1 (r1.1 - ε * k.1, r1.2 - ε * k.2)).natAbs →
      (k = r2 ∨ k = r3) →
      ∃ y : ℤ × ℤ, reading y r1 ≠ 0 ∧ reading y r2 ≠ 0 ∧ reading y r3 ≠ 0 ∧ reading y r4 ≠ 0 ∧
        ((reading y r1).natAbs = (reading y r2).natAbs ∨
          (reading y r1).natAbs = (reading y r3).natAbs) := by
    intro k ε _ n1 n2 n3 n4 hab hk
    set d : ℤ × ℤ := (r1.1 - ε * k.1, r1.2 - ε * k.2) with hd
    refine ⟨(-d.2, d.1), ?_, ?_, ?_, ?_, ?_⟩
    · rw [reading_perp]; exact neg_ne_zero.mpr n1
    · rw [reading_perp]; exact neg_ne_zero.mpr n2
    · rw [reading_perp]; exact neg_ne_zero.mpr n3
    · rw [reading_perp]; exact neg_ne_zero.mpr n4
    · rw [reading_perp, reading_perp, reading_perp, Int.natAbs_neg, Int.natAbs_neg, Int.natAbs_neg]
      rcases hk with rfl | rfl
      · exact Or.inl hab.symm
      · exact Or.inr hab.symm
  -- the minors, named
  set A := cross r1 r2
  set B := cross r1 r3
  set Cc := cross r1 r4
  set D := cross r2 r3
  set E := cross r2 r4
  set G := cross r3 r4
  have e11 : ∀ ε k, cross r1 (r1.1 - ε * k.1, r1.2 - ε * k.2) = -ε * cross r1 k := fun ε k => by
    rw [lin k r1 r1 ε, self]; ring
  have ekk : ∀ ε k, cross k (r1.1 - ε * k.1, r1.2 - ε * k.2) = -cross r1 k := fun ε k => by
    rw [lin k r1 k ε, self, anti]; ring
  have natε : ∀ (ε x : ℤ), (ε = 1 ∨ ε = -1) → (-ε * x).natAbs = x.natAbs := by
    rintro ε x (rfl | rfl) <;> simp
  -- the four candidates
  by_cases c1 : cross r3 (r1.1 - 1 * r2.1, r1.2 - 1 * r2.2) ≠ 0 ∧
      cross r4 (r1.1 - 1 * r2.1, r1.2 - 1 * r2.2) ≠ 0
  · refine try_dir r2 1 (Or.inl rfl) (by rw [e11]; simpa using h12) (by rw [ekk]; simpa using h12)
      c1.1 c1.2 (by rw [ekk, e11, natε _ _ (Or.inl rfl), Int.natAbs_neg]) (Or.inl rfl)
  by_cases c2 : cross r3 (r1.1 - (-1) * r2.1, r1.2 - (-1) * r2.2) ≠ 0 ∧
      cross r4 (r1.1 - (-1) * r2.1, r1.2 - (-1) * r2.2) ≠ 0
  · refine try_dir r2 (-1) (Or.inr rfl) (by rw [e11]; simpa using h12) (by rw [ekk]; simpa using h12)
      c2.1 c2.2 (by rw [ekk, e11, natε _ _ (Or.inr rfl), Int.natAbs_neg]) (Or.inl rfl)
  by_cases c3 : cross r2 (r1.1 - 1 * r3.1, r1.2 - 1 * r3.2) ≠ 0 ∧
      cross r4 (r1.1 - 1 * r3.1, r1.2 - 1 * r3.2) ≠ 0
  · refine try_dir r3 1 (Or.inl rfl) (by rw [e11]; simpa using h13) c3.1 (by rw [ekk]; simpa using h13)
      c3.2 (by rw [ekk, e11, natε _ _ (Or.inl rfl), Int.natAbs_neg]) (Or.inr rfl)
  by_cases c4 : cross r2 (r1.1 - (-1) * r3.1, r1.2 - (-1) * r3.2) ≠ 0 ∧
      cross r4 (r1.1 - (-1) * r3.1, r1.2 - (-1) * r3.2) ≠ 0
  · refine try_dir r3 (-1) (Or.inr rfl) (by rw [e11]; simpa using h13) c4.1 (by rw [ekk]; simpa using h13)
      c4.2 (by rw [ekk, e11, natε _ _ (Or.inr rfl), Int.natAbs_neg]) (Or.inr rfl)
  -- none is free: the minors are forced to vanish
  exfalso
  rw [not_and_or, not_not, not_not] at c1 c2 c3 c4
  rw [lin, lin] at c1 c2
  rw [lin, lin] at c3 c4
  refine merge_obstruction (A := A) (B := B) (Cc := Cc) (D := D) (E := E) (G := G)
    (cross_plucker r1 r2 r3 r4) h14 h23 ?_ ?_ ?_ ?_
  · rcases c1 with h | h
    · left; rw [anti r1 r3, anti r2 r3] at h; linarith
    · right; rw [anti r1 r4, anti r2 r4] at h; linarith
  · rcases c2 with h | h
    · left; rw [anti r1 r3, anti r2 r3] at h; linarith
    · right; rw [anti r1 r4, anti r2 r4] at h; linarith
  · rcases c3 with h | h
    · left; rw [anti r1 r2] at h; linarith
    · right; rw [anti r1 r4, anti r3 r4] at h; linarith
  · rcases c4 with h | h
    · left; rw [anti r1 r2] at h; linarith
    · right; rw [anti r1 r4, anti r3 r4] at h; linarith

/-! ## Order five on two directions -/

/-- **Order five, real speeds on two independent directions.**  Four speeds `aᵢ + cᵢ·α`, `α`
irrational, with pairwise non-parallel whole-number rows (pairwise incommensurable speeds), are
lonely at `1/5`. -/
theorem lonely_five_rank_two {α : ℝ} (hα : Irrational α) {r1 r2 r3 r4 : ℤ × ℤ}
    (h12 : cross r1 r2 ≠ 0) (h13 : cross r1 r3 ≠ 0) (h14 : cross r1 r4 ≠ 0)
    (h23 : cross r2 r3 ≠ 0) (h24 : cross r2 r4 ≠ 0) (h34 : cross r3 r4 ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ ∀ r ∈ ({r1, r2, r3, r4} : Finset (ℤ × ℤ)),
      (5 : ℝ)⁻¹ ≤ circDist (((r.1 : ℝ) + r.2 * α) * t) := by
  classical
  obtain ⟨y, n1, n2, n3, n4, hm⟩ := exists_merge_model h12 h13 h14 h23 h24 h34
  set w : ℤ × ℤ → ℝ := fun r => |((reading y r : ℤ) : ℝ)| with hw
  set W : Finset ℝ := {w r1, w r2, w r3, w r4} with hW
  have hWpos : ∀ d ∈ W, 0 < d := by
    intro d hd
    simp only [hW, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      exact abs_pos.mpr (by exact_mod_cast (by assumption))
  have hwnat : ∀ r, w r = (((reading y r).natAbs : ℕ) : ℝ) := fun r => by
    rw [hw]; simp only; rw [Nat.cast_natAbs, Int.cast_abs]
  have hWcard : W.card ≤ 3 := by
    rcases hm with h | h
    · have : w r1 = w r2 := by rw [hwnat, hwnat, h]
      rw [hW, this, Finset.insert_eq_of_mem (Finset.mem_insert_self _ _)]
      exact le_trans (Finset.card_insert_le _ _)
        (by have := Finset.card_insert_le (w r3) ({w r4} : Finset ℝ); simp at this ⊢; omega)
    · have : w r1 = w r3 := by rw [hwnat, hwnat, h]
      rw [hW, this, Finset.insert_eq_of_mem (by simp)]
      exact le_trans (Finset.card_insert_le _ _)
        (by have := Finset.card_insert_le (w r3) ({w r4} : Finset ℝ); simp at this ⊢; omega)
  obtain ⟨τ, -, hl⟩ := existenceAtN_four W hWpos (by simpa using hWcard)
  have hτ : ∀ r ∈ ({r1, r2, r3, r4} : Finset (ℤ × ℤ)),
      ((5 : ℕ) - 1 : ℝ)⁻¹ ≤ circDist ((reading y r : ℝ) * τ) := by
    intro r hr
    have hwr : w r ∈ W := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      simp only [hW, Finset.mem_insert, Finset.mem_singleton]
      rcases hr with rfl | rfl | rfl | rfl <;> simp
    have := hl (w r) hwr
    rw [hw] at this; simp only at this
    rw [circDist_abs_mul] at this
    have h54 : ((5 : ℕ) - 1 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
    rw [h54]; exact this
  obtain ⟨t, ht, hlt⟩ := lonely_of_model (n := 5) (by norm_num) hα ⟨r1, by simp⟩ y hτ
  exact ⟨t, ht, fun r hr => by simpa using hlt r hr⟩

end LRC.OrderFiveN
