import LonelyRunner.LRC.Spec.RealRowsN

/-! The exact merge for any finite number of nonzero integer rows. -/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.OrderSixN
open LRC.OrderFiveN
variable {m : ℕ}

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

end LRC.OrderSixN

namespace LRC.OrderSevenN

open LRC.OrderFiveN LRC.OrderSixN

variable {m : ℕ}

/-! ## the plane picture on two coordinates -/

/-- **A row inside a smaller cone is inside the larger.**  On `ℤ²`, with `D = det(A, B) ≠ 0` and
`C` strictly inside the cone of `A` and `B` (`det(A,C)·det(C,B) > 0`), let `C' = σ·C` with `σ = ±1`
chosen so that `det(A, C')` has the sign of `D`.  Every `w` strictly inside the cone of `A` and `C'`
is strictly inside the cone of `A` and `B`. -/
theorem inside_shrink {a1 a2 b1 b2 c1 c2 w1 w2 σ : ℤ} (hσ : σ * σ = 1)
    (hC : 0 < (a1 * c2 - a2 * c1) * (c1 * b2 - c2 * b1))
    (hsign : 0 < σ * (a1 * c2 - a2 * c1) * (a1 * b2 - a2 * b1))
    (hw : 0 < (a1 * w2 - a2 * w1) * (w1 * (σ * c2) - w2 * (σ * c1))) :
    0 < (a1 * w2 - a2 * w1) * (w1 * b2 - w2 * b1) := by
  set D := a1 * b2 - a2 * b1 with hD
  set α := w1 * b2 - w2 * b1 with hα
  set β := a1 * w2 - a2 * w1 with hβ
  set μ := a1 * (σ * c2) - a2 * (σ * c1) with hμ
  set lam := (σ * c1) * b2 - (σ * c2) * b1 with hlam
  -- the Plücker relation `D·det(w, C') = α·μ − β·λ`
  have hpl : D * (w1 * (σ * c2) - w2 * (σ * c1)) = α * μ - β * lam := by
    simp only [hD, hα, hβ, hμ, hlam]; ring
  have hμD : 0 < μ * D := by
    have : μ = σ * (a1 * c2 - a2 * c1) := by simp only [hμ]; ring
    rw [this]; exact hsign
  have hlm : 0 < lam * μ := by
    have : lam * μ = (σ * σ) * ((a1 * c2 - a2 * c1) * (c1 * b2 - c2 * b1)) := by
      simp only [hlam, hμ]; ring
    rw [this, hσ, one_mul]; exact hC
  have hlD : 0 < lam * D := by
    have h3 : 0 < (lam * μ) * (μ * D) := mul_pos hlm hμD
    have h4 : (lam * μ) * (μ * D) = (lam * D) * (μ * μ) := by ring
    rw [h4] at h3
    exact pos_of_mul_pos_left h3 (mul_self_nonneg μ)
  have hDne : D ≠ 0 := by rintro h0; rw [h0, mul_zero] at hμD; exact lt_irrefl 0 hμD
  -- `β·det(w, C') > 0`, scaled by `D²`
  have h5 : 0 < β * (α * μ - β * lam) * D := by
    have h6 : 0 < (β * (w1 * (σ * c2) - w2 * (σ * c1))) * (D * D) :=
      mul_pos hw (mul_self_pos.mpr hDne)
    have h7 : (β * (w1 * (σ * c2) - w2 * (σ * c1))) * (D * D) = β * (D * (w1 * (σ * c2) - w2 * (σ * c1))) * D := by
      ring
    rw [h7, hpl] at h6; exact h6
  have h8 : β * lam * D * β ≥ 0 := by
    have : β * lam * D * β = (β * β) * (lam * D) := by ring
    rw [this]; exact mul_nonneg (mul_self_nonneg β) hlD.le
  have h9 : 0 < (β * α) * (μ * D) := by nlinarith
  have := pos_of_mul_pos_left h9 hμD.le
  simpa [hα, hβ, mul_comm] using this

/-- **A blocker lies inside the cone.**  If `x` is parallel to `z = A + B` on two coordinates,
`x ≠ 0` there and `det(A, B) ≠ 0`, then `x` is strictly inside the cone of `A` and `B`. -/
theorem inside_of_parallel {a1 a2 b1 b2 x1 x2 : ℤ} (hD : a1 * b2 - a2 * b1 ≠ 0)
    (hpar : x1 * (a2 + b2) = x2 * (a1 + b1)) (hx : x1 ≠ 0 ∨ x2 ≠ 0) :
    0 < (a1 * x2 - a2 * x1) * (x1 * b2 - x2 * b1) := by
  set D := a1 * b2 - a2 * b1 with hDdef
  -- `det(A, x)·zₛ = D·xₛ` and `det(x, B)·zₛ = D·xₛ` for `z = A + B`, `s ∈ {1, 2}`
  have e1 : (a1 * x2 - a2 * x1) * (a1 + b1) = D * x1 := by
    have : (a1 * x2 - a2 * x1) * (a1 + b1) - D * x1 = a1 * (x2 * (a1 + b1) - x1 * (a2 + b2)) := by
      simp only [hDdef]; ring
    rw [hpar] at this; linarith
  have e2 : (a1 * x2 - a2 * x1) * (a2 + b2) = D * x2 := by
    have : (a1 * x2 - a2 * x1) * (a2 + b2) - D * x2 = a2 * (x2 * (a1 + b1) - x1 * (a2 + b2)) := by
      simp only [hDdef]; ring
    rw [hpar] at this; linarith
  have f1 : (x1 * b2 - x2 * b1) * (a1 + b1) = D * x1 := by
    have : (x1 * b2 - x2 * b1) * (a1 + b1) - D * x1 = b1 * (x1 * (a2 + b2) - x2 * (a1 + b1)) := by
      simp only [hDdef]; ring
    rw [hpar] at this; linarith
  have f2 : (x1 * b2 - x2 * b1) * (a2 + b2) = D * x2 := by
    have : (x1 * b2 - x2 * b1) * (a2 + b2) - D * x2 = b2 * (x1 * (a2 + b2) - x2 * (a1 + b1)) := by
      simp only [hDdef]; ring
    rw [hpar] at this; linarith
  rcases hx with hx | hx
  · have h : ((a1 * x2 - a2 * x1) * (x1 * b2 - x2 * b1)) * ((a1 + b1) * (a1 + b1)) = (D * x1) * (D * x1) := by
      calc ((a1 * x2 - a2 * x1) * (x1 * b2 - x2 * b1)) * ((a1 + b1) * (a1 + b1))
          = ((a1 * x2 - a2 * x1) * (a1 + b1)) * ((x1 * b2 - x2 * b1) * (a1 + b1)) := by ring
        _ = (D * x1) * (D * x1) := by rw [e1, f1]
    have hpos : 0 < (D * x1) * (D * x1) := mul_self_pos.mpr (mul_ne_zero hD hx)
    rw [← h] at hpos
    exact pos_of_mul_pos_left hpos (mul_self_nonneg _)
  · have h : ((a1 * x2 - a2 * x1) * (x1 * b2 - x2 * b1)) * ((a2 + b2) * (a2 + b2)) = (D * x2) * (D * x2) := by
      calc ((a1 * x2 - a2 * x1) * (x1 * b2 - x2 * b1)) * ((a2 + b2) * (a2 + b2))
          = ((a1 * x2 - a2 * x1) * (a2 + b2)) * ((x1 * b2 - x2 * b1) * (a2 + b2)) := by ring
        _ = (D * x2) * (D * x2) := by rw [e2, f2]
    have hpos : 0 < (D * x2) * (D * x2) := mul_self_pos.mpr (mul_ne_zero hD hx)
    rw [← h] at hpos
    exact pos_of_mul_pos_left hpos (mul_self_nonneg _)

/-! ## the merge -/

/-- Rows `i`, `j` on the coordinates `q`, `r`: the `2 × 2` determinant. -/
def det2 (q r : Fin m) (x y : Fin m → ℤ) : ℤ := x q * y r - x r * y q

/-- Row `l` is strictly inside the cone of `aᵢ` and `ε·aⱼ` on the coordinates `q`, `r`. -/
def InsideCone {k : ℕ} (q r : Fin m) (a : Fin k → Fin m → ℤ) (i j : Fin k) (ε : ℤ) (l : Fin k) :
    Prop :=
  0 < det2 q r (a i) (a l) * ((a l q) * (ε * a j r) - (a l r) * (ε * a j q))

/-- **The exact merge, any number of rows.**  Non-zero rows, not all parallel, have a whole-number
direction whose readings are all non-zero, with two of them equal up to sign. -/
theorem exists_merge_model_all {k : ℕ} (a : Fin k → Fin m → ℤ) (hnz : ∀ i, a i ≠ 0)
    (hnp : ∃ i j, ¬ Parallel (a i) (a j)) :
    ∃ y : Fin m → ℤ, (∀ i, dotZ y (a i) ≠ 0) ∧
      ∃ i j, i ≠ j ∧ (dotZ y (a i)).natAbs = (dotZ y (a j)).natAbs := by
  classical
  obtain ⟨i0, j0, hij0⟩ := hnp
  obtain ⟨q, r, hqr⟩ : ∃ q r, a i0 q * a j0 r ≠ a i0 r * a j0 q := by
    by_contra H; push Not at H; exact hij0 H
  -- pairs and signs with a non-degenerate cone, and how many rows lie strictly inside
  set T : Finset (Fin k × Fin k × ℤ) :=
    (Finset.univ ×ˢ Finset.univ ×ˢ ({1, -1} : Finset ℤ)).filter
      (fun p => det2 q r (a p.1) (a p.2.1) ≠ 0) with hT
  have hTne : T.Nonempty := ⟨(i0, j0, 1), by
    simp only [hT, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    exact ⟨by simp, by simp only [det2]; exact sub_ne_zero.mpr hqr⟩⟩
  set cnt : Fin k × Fin k × ℤ → ℕ := fun p =>
    (Finset.univ.filter (fun l => InsideCone q r a p.1 p.2.1 p.2.2 l)).card with hcnt
  obtain ⟨⟨i, j, ε⟩, hpT, hmin⟩ := T.exists_min_image cnt hTne
  simp only [hT, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton] at hpT
  obtain ⟨hε, hDij⟩ := hpT
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  -- the chosen cone is empty
  have hempty : ∀ l, ¬ InsideCone q r a i j ε l := by
    intro l hl
    set D := (a i q) * (ε * a j r) - (a i r) * (ε * a j q) with hD
    have hDne : D ≠ 0 := by
      have : D = ε * det2 q r (a i) (a j) := by simp only [hD, det2]; ring
      rw [this]; exact mul_ne_zero (by rcases hε with rfl | rfl <;> norm_num) hDij
    set σ : ℤ := if 0 < det2 q r (a i) (a l) * D then 1 else -1 with hσ
    have hσσ : σ * σ = 1 := by simp only [hσ]; split_ifs <;> norm_num
    have hil : det2 q r (a i) (a l) ≠ 0 := by
      intro h0; unfold InsideCone at hl; rw [h0, zero_mul] at hl; exact lt_irrefl 0 hl
    have hsign : 0 < σ * det2 q r (a i) (a l) * D := by
      simp only [hσ]; split_ifs with h
      · linarith
      · push Not at h
        have : det2 q r (a i) (a l) * D ≠ 0 := mul_ne_zero hil hDne
        have : det2 q r (a i) (a l) * D < 0 := lt_of_le_of_ne h this
        linarith
    -- the smaller cone `(i, l, σ)`
    have hmemT : (i, l, σ) ∈ T := by
      simp only [hT, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      refine ⟨?_, hil⟩
      simp only [hσ]; split_ifs <;> simp
    have hsub : Finset.univ.filter (fun l' => InsideCone q r a i l σ l') ⊂
        Finset.univ.filter (fun l' => InsideCone q r a i j ε l') := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨l, by simpa using hl, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, InsideCone, det2]
        intro h
        have : (a l q) * (σ * a l r) - (a l r) * (σ * a l q) = 0 := by ring
        rw [this, mul_zero] at h; exact lt_irrefl 0 h
      · intro l' hl'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, InsideCone, det2] at hl' ⊢
        unfold InsideCone det2 at hl
        simp only [hD, det2] at hsign
        exact inside_shrink (a1 := a i q) (a2 := a i r) (b1 := ε * a j q) (b2 := ε * a j r)
          (c1 := a l q) (c2 := a l r) (w1 := a l' q) (w2 := a l' r) hσσ hl hsign hl'
    have := hmin _ hmemT
    simp only [hcnt] at this
    exact absurd (Finset.card_lt_card hsub) (not_lt.mpr this)
  -- the merge direction `aᵢ + ε·aⱼ` is blocked by no row
  have hij : i ≠ j := by
    rintro rfl; apply hDij; simp only [det2]; ring
  set d : Fin m → ℤ := fun x => a i x - (-ε) * a j x with hd
  have hdq : d q = a i q + ε * a j q := by simp only [hd]; ring
  have hdr : d r = a i r + ε * a j r := by simp only [hd]; ring
  have hdz : d q ≠ 0 ∨ d r ≠ 0 := by
    by_contra h; push Not at h
    apply hDij
    have h1 : a i q = -(ε * a j q) := by linarith [h.1, hdq]
    have h2 : a i r = -(ε * a j r) := by linarith [h.2, hdr]
    simp only [det2, h1, h2]; ring
  have hd0 : d ≠ 0 := by
    intro h0; rcases hdz with h | h <;> exact h (by rw [h0]; rfl)
  have hfree : ∀ l, ¬ Parallel (a l) d := by
    intro l hpar
    -- the blocker is non-zero on the two coordinates
    have hlz : a l q ≠ 0 ∨ a l r ≠ 0 := by
      by_contra h; push Not at h
      apply hnz l
      funext x
      rcases hdz with hz | hz
      · have := hpar x q
        rw [h.1, zero_mul] at this
        exact (mul_eq_zero.mp this).resolve_right hz
      · have := hpar x r
        rw [h.2, zero_mul] at this
        exact (mul_eq_zero.mp this).resolve_right hz
    apply hempty l
    unfold InsideCone det2
    have hp := hpar q r
    rw [hdq, hdr] at hp
    have hDne' : a i q * (ε * a j r) - a i r * (ε * a j q) ≠ 0 := by
      have : a i q * (ε * a j r) - a i r * (ε * a j q) = ε * det2 q r (a i) (a j) := by
        simp only [det2]; ring
      rw [this]; exact mul_ne_zero (by rcases hε with rfl | rfl <;> norm_num) hDij
    exact inside_of_parallel (a1 := a i q) (a2 := a i r) (b1 := ε * a j q) (b2 := ε * a j r)
      (x1 := a l q) (x2 := a l r) hDne' (by linarith) hlz
  have hεε' : (-ε) * (-ε) = 1 := by rw [neg_mul_neg]; exact hεε
  exact merge_of_free a hij hεε' hd0 hfree

end LRC.OrderSevenN
