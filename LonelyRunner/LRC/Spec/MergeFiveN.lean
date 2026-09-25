import LonelyRunner.LRC.Spec.RealFiveN

/-!
# The exact merge for five rows

2026-09-24.  Five non-zero whole-number rows, not all parallel, have a whole-number direction `y`
whose readings `y·aᵢ` are all non-zero, with two of them equal up to sign
(`exists_merge_model_five`).  This is `exists_merge_model_gen` one row up.

**Why a merge exists.**  Take two non-parallel rows `u`, `v`.  The merge directions are
`u − v` and `u + v`; one of them is free unless rows `p ∥ u − v` and `q ∥ u + v` block both.  Read
every row in the coordinates of `u`, `v` (two minors, `pA` and `pB`): `u = (Δ, 0)`, `v = (0, Δ)`,
`p = (α, −α)`, `q = (γ, γ)`.  The pairs `(u, p)` and `(v, p)` need blockers too.  `v` and `q`
cannot block both directions of `(u, p)`, and `u` and `q` cannot block both of `(v, p)`, so the
fifth row blocks one of each.  The two directions it would have to follow are not parallel.

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.OrderSixN

open LRC.OrderFiveN

variable {m : ℕ}

/-- First coordinate against the pair `u`, `v` (read at coordinates `q`, `r`). -/
def pA (q r : Fin m) (v w : Fin m → ℤ) : ℤ := w q * v r - w r * v q

/-- Second coordinate against the pair `u`, `v`. -/
def pB (q r : Fin m) (u w : Fin m → ℤ) : ℤ := u q * w r - u r * w q

theorem pA_sub (q r : Fin m) (v x y : Fin m → ℤ) (ε : ℤ) :
    pA q r v (fun k => x k - ε * y k) = pA q r v x - ε * pA q r v y := by
  simp only [pA]; ring

theorem pB_sub (q r : Fin m) (u x y : Fin m → ℤ) (ε : ℤ) :
    pB q r u (fun k => x k - ε * y k) = pB q r u x - ε * pB q r u y := by
  simp only [pB]; ring

/-- Parallel rows read parallel in the coordinates. -/
theorem cross_of_parallel (q r : Fin m) (u v : Fin m → ℤ) {w z : Fin m → ℤ} (h : Parallel w z) :
    pA q r v w * pB q r u z - pB q r u w * pA q r v z = 0 := by
  have hwz := h q r
  have : pA q r v w * pB q r u z - pB q r u w * pA q r v z
      = (u q * v r - u r * v q) * (w q * z r - w r * z q) := by simp only [pA, pB]; ring
  rw [this, hwz, sub_self, mul_zero]

/-- A non-zero row parallel to a direction with non-zero coordinates has non-zero coordinates. -/
theorem coords_ne_zero (q r : Fin m) {u v w z : Fin m → ℤ} (hΔ : u q * v r - u r * v q ≠ 0)
    (hw : w ≠ 0) (h : Parallel w z) (hz : pA q r v z ≠ 0 ∨ pB q r u z ≠ 0) :
    pA q r v w ≠ 0 ∨ pB q r u w ≠ 0 := by
  by_contra H
  push_neg at H
  obtain ⟨hA, hB⟩ := H
  have hwq : w q = 0 := by
    have e : (u q * v r - u r * v q) * w q = u q * pA q r v w + v q * pB q r u w := by
      simp only [pA, pB]; ring
    rw [hA, hB] at e
    exact (mul_eq_zero.mp (by linarith)).resolve_left hΔ
  have hwr : w r = 0 := by
    have e : (u q * v r - u r * v q) * w r = u r * pA q r v w + v r * pB q r u w := by
      simp only [pA, pB]; ring
    rw [hA, hB] at e
    exact (mul_eq_zero.mp (by linarith)).resolve_left hΔ
  apply hw
  funext k
  have hzq : z q ≠ 0 ∨ z r ≠ 0 := by
    by_contra H2
    push_neg at H2
    rcases hz with hz | hz <;> apply hz <;> simp [pA, pB, H2.1, H2.2]
  rcases hzq with hzq | hzr
  · have := h k q
    rw [hwq, zero_mul] at this
    exact (mul_eq_zero.mp this).resolve_right hzq
  · have := h k r
    rw [hwr, zero_mul] at this
    exact (mul_eq_zero.mp this).resolve_right hzr

/-- A free merge direction gives the merge. -/
theorem merge_of_free {k : ℕ} (a : Fin k → Fin m → ℤ) {i j : Fin k} (hij : i ≠ j) {ε : ℤ}
    (hε : ε * ε = 1) (hd : (fun q => a i q - ε * a j q) ≠ 0)
    (hfree : ∀ l, ¬ Parallel (a l) (fun q => a i q - ε * a j q)) :
    ∃ y : Fin m → ℤ, (∀ l, dotZ y (a l) ≠ 0) ∧
      ∃ i j, i ≠ j ∧ (dotZ y (a i)).natAbs = (dotZ y (a j)).natAbs := by
  obtain ⟨y, hy0, hy⟩ := exists_perp_avoid _ hd a hfree
  refine ⟨y, hy, i, j, hij, ?_⟩
  have hzero : dotZ y (a i) = ε * dotZ y (a j) := by
    have := dotZ_sub_smul y (a i) (a j) ε
    linarith
  rw [hzero, Int.natAbs_mul]
  have : ε.natAbs = 1 := by
    have := congrArg Int.natAbs hε
    rw [Int.natAbs_mul] at this
    simpa using Nat.eq_one_of_mul_eq_one_right this
  rw [this, one_mul]

theorem fin5_fifth (i j l1 l2 : Fin 5) (h1 : i ≠ j) (h2 : i ≠ l1) (h3 : i ≠ l2) (h4 : j ≠ l1)
    (h5 : j ≠ l2) (h6 : l1 ≠ l2) :
    ∃ o : Fin 5, ∀ b : Fin 5, b = i ∨ b = j ∨ b = l1 ∨ b = l2 ∨ b = o := by
  revert i j l1 l2; decide

/-! ## The blocking cases, in the coordinates of `u`, `v`

A blocker's coordinates `(c, d)` are one of `u = (Δ, 0)`, `v = (0, Δ)`, `p = (α, −α)`,
`q = (γ, γ)` or the fifth row `(X, Y)`. -/

section Blocking

variable {Δ α γ X Y c d : ℤ}

/-- Shorthand for "the blocker is one of the five rows". -/
def OneOf (Δ α γ X Y c d : ℤ) : Prop :=
  (c = Δ ∧ d = 0) ∨ (c = 0 ∧ d = Δ) ∨ (c = α ∧ d = -α) ∨ (c = γ ∧ d = γ) ∨ (c = X ∧ d = Y)

theorem ne_of_mul {x y : ℤ} (hx : x ≠ 0) (h : x * y = 0) : y = 0 := (mul_eq_zero.mp h).resolve_left hx

/-- Blocking `u − p`, coordinates `(Δ − α, α)`. -/
theorem blk1 (hΔ : Δ ≠ 0) (hα : α ≠ 0) (hγ : γ ≠ 0) (hc : OneOf Δ α γ X Y c d)
    (hn : c ≠ 0 ∨ d ≠ 0) (h : c * α - d * (Δ - α) = 0) :
    Δ = α ∨ Δ = 2 * α ∨ (X * α - Y * (Δ - α) = 0 ∧ (X ≠ 0 ∨ Y ≠ 0)) := by
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at h hn
  · exact absurd (ne_of_mul hΔ (by linear_combination h)) hα
  · left; linarith [ne_of_mul hΔ (by linear_combination -h : Δ * (Δ - α) = 0)]
  · exact absurd (ne_of_mul hα (by linear_combination h : α * Δ = 0)) hΔ
  · right; left; linarith [ne_of_mul hγ (by linear_combination h : γ * (2 * α - Δ) = 0)]
  · right; right; exact ⟨h, hn⟩

/-- Blocking `u + p`, coordinates `(Δ + α, −α)`. -/
theorem blk2 (hΔ : Δ ≠ 0) (hα : α ≠ 0) (hγ : γ ≠ 0) (hc : OneOf Δ α γ X Y c d)
    (hn : c ≠ 0 ∨ d ≠ 0) (h : c * -α - d * (Δ + α) = 0) :
    Δ = -α ∨ Δ = -2 * α ∨ (X * -α - Y * (Δ + α) = 0 ∧ (X ≠ 0 ∨ Y ≠ 0)) := by
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at h hn
  · exact absurd (ne_of_mul hΔ (by linear_combination -h)) hα
  · left; linarith [ne_of_mul hΔ (by linear_combination -h : Δ * (Δ + α) = 0)]
  · exact absurd (ne_of_mul hα (by linear_combination h : α * Δ = 0)) hΔ
  · right; left; linarith [ne_of_mul hγ (by linear_combination -h : γ * (Δ + 2 * α) = 0)]
  · right; right; exact ⟨h, hn⟩

/-- Blocking `v − p`, coordinates `(−α, Δ + α)`. -/
theorem blk3 (hΔ : Δ ≠ 0) (hα : α ≠ 0) (hγ : γ ≠ 0) (hc : OneOf Δ α γ X Y c d)
    (hn : c ≠ 0 ∨ d ≠ 0) (h : c * (Δ + α) - d * -α = 0) :
    Δ = -α ∨ Δ = -2 * α ∨ (X * (Δ + α) - Y * -α = 0 ∧ (X ≠ 0 ∨ Y ≠ 0)) := by
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at h hn
  · left; linarith [ne_of_mul hΔ (by linear_combination h : Δ * (Δ + α) = 0)]
  · exact absurd (ne_of_mul hΔ (by linear_combination h)) hα
  · exact absurd (ne_of_mul hα (by linear_combination h : α * Δ = 0)) hΔ
  · right; left; linarith [ne_of_mul hγ (by linear_combination h : γ * (Δ + 2 * α) = 0)]
  · right; right; exact ⟨h, hn⟩

/-- Blocking `v + p`, coordinates `(α, Δ − α)`. -/
theorem blk4 (hΔ : Δ ≠ 0) (hα : α ≠ 0) (hγ : γ ≠ 0) (hc : OneOf Δ α γ X Y c d)
    (hn : c ≠ 0 ∨ d ≠ 0) (h : c * (Δ - α) - d * α = 0) :
    Δ = α ∨ Δ = 2 * α ∨ (X * (Δ - α) - Y * α = 0 ∧ (X ≠ 0 ∨ Y ≠ 0)) := by
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at h hn
  · left; linarith [ne_of_mul hΔ (by linear_combination h : Δ * (Δ - α) = 0)]
  · exact absurd (ne_of_mul hΔ (by linear_combination -h)) hα
  · exact absurd (ne_of_mul hα (by linear_combination h : α * Δ = 0)) hΔ
  · right; left; linarith [ne_of_mul hγ (by linear_combination h : γ * (Δ - 2 * α) = 0)]
  · right; right; exact ⟨h, hn⟩

/-- The fifth row cannot follow both `u − p` and `u + p`. -/
theorem fifth12 (hα : α ≠ 0) (hΔ : Δ ≠ 0) (hXY : X ≠ 0 ∨ Y ≠ 0)
    (h1 : X * α - Y * (Δ - α) = 0) (h2 : X * -α - Y * (Δ + α) = 0) : False := by
  have hY : Y = 0 := by
    have e : 2 * (Δ * Y) = 0 := by linear_combination -(h1 + h2)
    exact ne_of_mul hΔ (by linarith)
  subst hY
  have hX : X = 0 := by
    have := ne_of_mul hα (by linear_combination h1 : α * X = 0); exact this
  rcases hXY with h | h <;> simp_all

/-- The fifth row cannot follow both `v − p` and `v + p`. -/
theorem fifth34 (hα : α ≠ 0) (hΔ : Δ ≠ 0) (hXY : X ≠ 0 ∨ Y ≠ 0)
    (h3 : X * (Δ + α) - Y * -α = 0) (h4 : X * (Δ - α) - Y * α = 0) : False := by
  have hX : X = 0 := by
    have e : 2 * (Δ * X) = 0 := by linear_combination h3 + h4
    exact ne_of_mul hΔ (by linarith)
  subst hX
  have hY : Y = 0 := by
    have := ne_of_mul hα (by linear_combination -h4 : α * Y = 0); exact this
  rcases hXY with h | h <;> simp_all

/-- The fifth row cannot follow both `u − p` and `v + p` unless `Δ = 2α`. -/
theorem fifth14 (hα : α ≠ 0) (hΔ : Δ ≠ 0) (hΔα : Δ - 2 * α ≠ 0) (hXY : X ≠ 0 ∨ Y ≠ 0)
    (h1 : X * α - Y * (Δ - α) = 0) (h4 : X * (Δ - α) - Y * α = 0) : False := by
  have hY : Y = 0 := by
    have e : Δ * ((Δ - 2 * α) * Y) = 0 := by linear_combination -(Δ - α) * h1 + α * h4
    exact ne_of_mul hΔα (ne_of_mul hΔ e)
  subst hY
  have hX : X = 0 := ne_of_mul hα (by linear_combination h1)
  rcases hXY with h | h <;> simp_all

/-- The fifth row cannot follow both `u + p` and `v − p` unless `Δ = −2α`. -/
theorem fifth23 (hα : α ≠ 0) (hΔ : Δ ≠ 0) (hΔα : Δ + 2 * α ≠ 0) (hXY : X ≠ 0 ∨ Y ≠ 0)
    (h2 : X * -α - Y * (Δ + α) = 0) (h3 : X * (Δ + α) - Y * -α = 0) : False := by
  have hY : Y = 0 := by
    have e : Δ * ((Δ + 2 * α) * Y) = 0 := by linear_combination -(Δ + α) * h2 - α * h3
    exact ne_of_mul hΔα (ne_of_mul hΔ e)
  subst hY
  have hX : X = 0 := ne_of_mul hα (by linear_combination -h2)
  rcases hXY with h | h <;> simp_all

end Blocking

-- 81 blocking combinations are closed one by one
set_option maxHeartbeats 4000000 in
/-- **The exact merge, five rows.**  Five non-zero rows, not all parallel, have a whole-number
direction whose readings are all non-zero, with two of them equal up to sign. -/
theorem exists_merge_model_five (a : Fin 5 → Fin m → ℤ) (hnz : ∀ i, a i ≠ 0)
    (hnp : ∃ i j, ¬ Parallel (a i) (a j)) :
    ∃ y : Fin m → ℤ, (∀ i, dotZ y (a i) ≠ 0) ∧
      ∃ i j, i ≠ j ∧ (dotZ y (a i)).natAbs = (dotZ y (a j)).natAbs := by
  classical
  by_contra hno
  -- every merge direction is blocked
  have blk : ∀ x y : Fin 5, x ≠ y → ∀ ε : ℤ, ε * ε = 1 →
      (fun q => a x q - ε * a y q) ≠ 0 → ∃ l, Parallel (a l) (fun q => a x q - ε * a y q) := by
    intro x y hxy ε hε hd
    by_contra H
    push_neg at H
    exact hno (merge_of_free a hxy hε hd H)
  obtain ⟨i, j, hij⟩ := hnp
  have hij' : i ≠ j := fun h => hij (h ▸ parallel_refl _)
  -- coordinates against `u = a i`, `v = a j`
  obtain ⟨q, r, hqr⟩ : ∃ q r, a i q * a j r ≠ a i r * a j q := by
    by_contra H; push_neg at H; exact hij H
  set Δ : ℤ := a i q * a j r - a i r * a j q with hΔdef
  have hΔ : Δ ≠ 0 := sub_ne_zero.mpr hqr
  set A : (Fin m → ℤ) → ℤ := pA q r (a j) with hA
  set B : (Fin m → ℤ) → ℤ := pB q r (a i) with hB
  have Au : A (a i) = Δ := by simp only [hA, pA, hΔdef]
  have Bu : B (a i) = 0 := by simp only [hB, pB]; ring
  have Av : A (a j) = 0 := by simp only [hA, pA]; ring
  have Bv : B (a j) = Δ := by simp only [hB, pB, hΔdef]
  have cross : ∀ {w z}, Parallel w z → A w * B z - B w * A z = 0 :=
    fun h => cross_of_parallel q r (a i) (a j) h
  have Asub : ∀ x y (ε : ℤ), A (fun k => x k - ε * y k) = A x - ε * A y := fun x y ε => pA_sub q r (a j) x y ε
  have Bsub : ∀ x y (ε : ℤ), B (fun k => x k - ε * y k) = B x - ε * B y := fun x y ε => pB_sub q r (a i) x y ε
  have nz : ∀ {w z}, w ≠ 0 → Parallel w z → (A z ≠ 0 ∨ B z ≠ 0) → (A w ≠ 0 ∨ B w ≠ 0) :=
    fun hw h hz => coords_ne_zero q r hΔ hw h hz
  -- a direction with non-zero coordinates is non-zero
  have dne : ∀ {z : Fin m → ℤ}, (A z ≠ 0 ∨ B z ≠ 0) → z ≠ 0 := by
    intro z hz h0
    rw [h0] at hz
    rcases hz with hz | hz <;> apply hz <;> simp [hA, hB, pA, pB]
  -- the blockers of `(u, v)`
  obtain ⟨l1, P1⟩ := blk i j hij' 1 (by norm_num) (dne (by rw [Asub, Au, Av]; left; simpa using hΔ))
  obtain ⟨l2, P2⟩ := blk i j hij' (-1) (by norm_num) (dne (by rw [Asub, Au, Av]; left; simpa using hΔ))
  set α := A (a l1) with hα
  set γ := A (a l2) with hγ
  have Bl1 : B (a l1) = -α := by
    have := cross P1
    rw [Asub, Bsub, Au, Av, Bu, Bv] at this
    have : Δ * (B (a l1) + α) = 0 := by rw [hα]; linarith
    linarith [(mul_eq_zero.mp this).resolve_left hΔ]
  have Bl2 : B (a l2) = γ := by
    have := cross P2
    rw [Asub, Bsub, Au, Av, Bu, Bv] at this
    have : Δ * (B (a l2) - γ) = 0 := by rw [hγ]; linarith
    linarith [(mul_eq_zero.mp this).resolve_left hΔ]
  have hα0 : α ≠ 0 := by
    have := nz (hnz l1) P1 (by rw [Asub, Au, Av]; left; simpa using hΔ)
    rw [Bl1] at this
    rcases this with h | h
    · exact h
    · exact fun h0 => h (by rw [h0]; ring)
  have hγ0 : γ ≠ 0 := by
    have := nz (hnz l2) P2 (by rw [Asub, Au, Av]; left; simpa using hΔ)
    rw [Bl2] at this
    rcases this with h | h <;> exact h
  -- the four rows are distinct
  have d1i : l1 ≠ i := by
    intro h; apply hα0
    have : B (a l1) = B (a i) := by rw [h]
    rw [Bl1, Bu] at this; linarith
  have d1j : l1 ≠ j := by
    intro h; apply hα0
    have : A (a l1) = A (a j) := by rw [h]
    rw [Av] at this; exact this
  have d2i : l2 ≠ i := by
    intro h; apply hγ0
    have : B (a l2) = B (a i) := by rw [h]
    rw [Bl2, Bu] at this; exact this
  have d2j : l2 ≠ j := by
    intro h; apply hγ0
    have : A (a l2) = A (a j) := by rw [h]
    rw [Av] at this; exact this
  have d12 : l1 ≠ l2 := by
    intro h; apply hα0
    have hb : B (a l1) = B (a l2) := by rw [h]
    have ha : A (a l1) = A (a l2) := by rw [h]
    rw [Bl1, Bl2] at hb; rw [← hα, ← hγ] at ha; linarith
  obtain ⟨o, ho⟩ := fin5_fifth i j l1 l2 hij' (Ne.symm d1i) (Ne.symm d2i) (Ne.symm d1j) (Ne.symm d2j) d12
  -- a blocker of a direction with coordinates `(X, Y)`
  have blocker : ∀ x y : Fin 5, x ≠ y → ∀ ε : ℤ, ε * ε = 1 →
      (A (fun k => a x k - ε * a y k) ≠ 0 ∨ B (fun k => a x k - ε * a y k) ≠ 0) →
      ∃ b, (b = i ∨ b = j ∨ b = l1 ∨ b = l2 ∨ b = o) ∧
        A (a b) * B (fun k => a x k - ε * a y k) - B (a b) * A (fun k => a x k - ε * a y k) = 0 := by
    intro x y hxy ε hε hd
    obtain ⟨b, hb⟩ := blk x y hxy ε hε (dne hd)
    exact ⟨b, ho b, cross hb⟩
  have coordsOf : ∀ b, OneOf Δ α γ (A (a o)) (B (a o)) (A (a b)) (B (a b)) := by
    intro b
    rcases ho b with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨Au, Bu⟩
    · exact Or.inr (Or.inl ⟨Av, Bv⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hα.symm, Bl1⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hγ.symm, Bl2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
  have blocker : ∀ x y : Fin 5, x ≠ y → ∀ ε : ℤ, ε * ε = 1 →
      (A (fun k => a x k - ε * a y k) ≠ 0 ∨ B (fun k => a x k - ε * a y k) ≠ 0) →
      ∃ b, A (a b) * B (fun k => a x k - ε * a y k) - B (a b) * A (fun k => a x k - ε * a y k) = 0 ∧
        (A (a b) ≠ 0 ∨ B (a b) ≠ 0) := by
    intro x y hxy ε hε hd
    obtain ⟨b, hb⟩ := blk x y hxy ε hε (dne hd)
    exact ⟨b, cross hb, nz (hnz b) hb hd⟩
  have hαne : ∀ z : ℤ, z = -α → z ≠ 0 := fun z hz h => hα0 (by linarith)
  obtain ⟨b1, c1, n1⟩ := blocker i l1 (Ne.symm d1i) 1 (by norm_num)
    (by right; rw [Bsub, Bu, Bl1]; intro h; apply hα0; linarith)
  obtain ⟨b2, c2, n2⟩ := blocker i l1 (Ne.symm d1i) (-1) (by norm_num)
    (by right; rw [Bsub, Bu, Bl1]; intro h; apply hα0; linarith)
  obtain ⟨b3, c3, n3⟩ := blocker j l1 (Ne.symm d1j) 1 (by norm_num)
    (by left; rw [Asub, Av, ← hα]; intro h; apply hα0; linarith)
  obtain ⟨b4, c4, n4⟩ := blocker j l1 (Ne.symm d1j) (-1) (by norm_num)
    (by left; rw [Asub, Av, ← hα]; intro h; apply hα0; linarith)
  rw [Asub, Bsub, Au, Bu, ← hα, Bl1] at c1 c2
  rw [Asub, Bsub, Av, Bv, ← hα, Bl1] at c3 c4
  have e1 := blk1 hΔ hα0 hγ0 (coordsOf b1) n1 (by linear_combination c1)
  have e2 := blk2 hΔ hα0 hγ0 (coordsOf b2) n2 (by linear_combination c2)
  have e3 := blk3 hΔ hα0 hγ0 (coordsOf b3) n3 (by linear_combination c3)
  have e4 := blk4 hΔ hα0 hγ0 (coordsOf b4) n4 (by linear_combination c4)
  rcases e1 with e1 | e1 | ⟨o1, m1⟩ <;> rcases e2 with e2 | e2 | ⟨o2, m2⟩ <;>
    rcases e3 with e3 | e3 | ⟨o3, m3⟩ <;> rcases e4 with e4 | e4 | ⟨o4, m4⟩
  all_goals first
    | exact hα0 (by linarith)
    | exact fifth12 hα0 hΔ ‹_› o1 o2
    | exact fifth34 hα0 hΔ ‹_› o3 o4
    | exact fifth14 hα0 hΔ (by intro h; apply hα0; linarith) ‹_› o1 o4
    | exact fifth23 hα0 hΔ (by intro h; apply hα0; linarith) ‹_› o2 o3

end LRC.OrderSixN
