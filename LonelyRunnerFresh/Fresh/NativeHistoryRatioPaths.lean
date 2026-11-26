import Fresh.NativeGateSixHistory

/-!
Products of inequalities from native moves can force closed clearance
at a subsequent opening. The path proves the numerical bound and keeps
each source comparison explicit. No bound on the lap labels is needed.
-/

namespace Fresh.NativeHistoryRatioPaths

open Fresh Fresh.Localisation Fresh.Cascade

/-- A product of comparisons between readings. The directed edge
`i → j` with factor `c` means `reading j ≤ c * reading i`. -/
inductive Path {ι : Type*} (edge : ι → ι → ℝ → Prop) :
    ι → ι → ℝ → Prop where
  | refl (i) : Path edge i i 1
  | edge {i j c} (h : edge i j c) (hc : 0 ≤ c) : Path edge i j c
  | trans {i j k c d} (h₁ : Path edge i j c) (h₂ : Path edge j k d) :
      Path edge i k (d * c)

/-- The product bound follows from the original move comparisons. -/
theorem path_bound {ι : Type*} {edge : ι → ι → ℝ → Prop} (reading : ι → ℝ)
    (he : ∀ i j c, edge i j c → reading j ≤ c * reading i)
    {i j c} (h : Path edge i j c) : 0 ≤ c ∧ reading j ≤ c * reading i := by
  induction h with
  | refl i => simp
  | edge h hc => exact ⟨hc, he _ _ _ h⟩
  | trans h₁ h₂ ih₁ ih₂ =>
    exact ⟨mul_nonneg ih₂.1 ih₁.1,
      ih₂.2.trans (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left ih₁.2 ih₂.1)⟩

/-- At the opening with numerator A, two directed paths to and from
the opener can certify a reading's whole closed clear band. -/
theorem clear_of_paths {ι : Type*} {edge : ι → ι → ℝ → Prop} (reading : ι → ℝ)
    (hpos : ∀ i, 0 < reading i)
    (he : ∀ i j c, edge i j c → reading j ≤ c * reading i)
    {a i : ι} {A lo hi : ℝ} (hA : 0 ≤ A) (j : ℤ)
    (hin : Path edge i a lo) (hout : Path edge a i hi)
    (hlo : 0 ≤ (j : ℝ) + 1 / 8)
    (hl : ((j : ℝ) + 1 / 8) * lo ≤ A)
    (hu : A * hi ≤ (j : ℝ) + 7 / 8) :
    (1 / 8 : ℝ) ≤ distInt (reading i * (A / reading a)) := by
  apply clear_of_window j
  · rw [← mul_div_assoc, le_div_iff₀ (hpos a), mul_comm (reading i) A]
    calc
      ((j : ℝ) + 1 / 8) * reading a ≤ ((j : ℝ) + 1 / 8) * (lo * reading i) :=
        mul_le_mul_of_nonneg_left (path_bound reading he hin).2 hlo
      _ ≤ A * reading i := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hl (hpos i).le
  · rw [← mul_div_assoc, div_le_iff₀ (hpos a), mul_comm (reading i) A]
    calc
      A * reading i ≤ A * (hi * reading a) :=
        mul_le_mul_of_nonneg_left (path_bound reading he hout).2 hA
      _ ≤ ((j : ℝ) + 7 / 8) * reading a := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hu (hpos a).le

/-- History paths for every indexed reading give a fixed point at the
specified opening. Equal absolute readings can occupy several indices. -/
theorem fixes_of_paths {ι : Type*} [Fintype ι] {edge : ι → ι → ℝ → Prop}
    (reading : ι → ℝ) (hpos : ∀ i, 0 < reading i)
    (he : ∀ i j c, edge i j c → reading j ≤ c * reading i)
    (a : ι) {A : ℝ} (hA : 0 ≤ A)
    (hfaces : ∀ i, ∃ (j : ℤ) (lo hi : ℝ),
      Path edge i a lo ∧ Path edge a i hi ∧ 0 ≤ (j : ℝ) + 1 / 8 ∧
      ((j : ℝ) + 1 / 8) * lo ≤ A ∧ A * hi ≤ (j : ℝ) + 7 / 8) :
    IsMove (Finset.univ.image reading) (A / reading a) (A / reading a) := by
  classical
  have hp : ∀ r ∈ Finset.univ.image reading, 0 < r := by
    intro r hr
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    exact hpos i
  apply (isMove_self_iff hp).2
  intro r hr
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨j, lo, hi, hin, hout, hj, hl, hu⟩ := hfaces i
  exact clear_of_paths reading hpos he hA j hin hout hj hl hu

/-- If a weak boundary model violates a proposed ratio bound, move a
positive distance toward an actual model. This preserves all strict
history faces and still violates the bound. -/
theorem strict_countermodel {ι : Type*} (weak strict : ι → ι → ℝ → Prop)
    (x p : ι → ℝ) (hx : ∀ i, 0 < x i) (hp : ∀ i, 0 < p i)
    (hxw : ∀ i j c, weak i j c → x j ≤ c * x i)
    (hpw : ∀ i j c, weak i j c → p j ≤ c * p i)
    (hxs : ∀ i j c, strict i j c → x j < c * x i)
    (hps : ∀ i j c, strict i j c → p j ≤ c * p i)
    {a b : ι} {C : ℝ} (hbad : C * p a < p b) :
    ∃ y : ι → ℝ, (∀ i, 0 < y i) ∧
      (∀ i j c, weak i j c → y j ≤ c * y i) ∧
      (∀ i j c, strict i j c → y j < c * y i) ∧
      C * y a < y b := by
  let margin := p b - C * p a
  let loss := |x b - C * x a|
  have hm : 0 < margin := sub_pos.mpr hbad
  have hl : 0 ≤ loss := abs_nonneg _
  have hden : 0 < 2 * (margin + loss) := by linarith
  let t := margin / (2 * (margin + loss))
  have ht : 0 < t := div_pos hm hden
  have ht' : t < 1 := (div_lt_iff₀ hden).2 (by linarith)
  have htprod : t * (2 * (margin + loss)) = margin :=
    div_mul_cancel₀ _ hden.ne'
  let y := fun i => t * x i + (1 - t) * p i
  refine ⟨y, ?_, ?_, ?_, ?_⟩
  · intro i
    exact add_pos (mul_pos ht (hx i)) (mul_pos (sub_pos.mpr ht') (hp i))
  · intro i j c h
    dsimp [y]
    nlinarith only [mul_le_mul_of_nonneg_left (hxw i j c h) ht.le,
      mul_le_mul_of_nonneg_left (hpw i j c h) (sub_nonneg.mpr ht'.le)]
  · intro i j c h
    dsimp [y]
    nlinarith only [mul_lt_mul_of_pos_left (hxs i j c h) ht,
      mul_le_mul_of_nonneg_left (hps i j c h) (sub_nonneg.mpr ht'.le)]
  · have hxl : -loss ≤ x b - C * x a := neg_abs_le _
    have htl := mul_le_mul_of_nonneg_left hxl ht.le
    have hpositive : 0 < t * (x b - C * x a) + (1 - t) * margin := by
      nlinarith only [htl, htprod, hm]
    change C * (t * x a + (1 - t) * p a) < t * x b + (1 - t) * p b
    dsimp [margin] at hpositive
    nlinarith only [hpositive]

/-- When only one upper face remains open, its closed edge selects
between the fixed point and that reading's next opening. All other
clearances come from the historical paths. -/
theorem one_open_face {ι : Type*} [Fintype ι] {edge : ι → ι → ℝ → Prop}
    (reading : ι → ℝ) (hpos : ∀ i, 0 < reading i)
    (he : ∀ i j c, edge i j c → reading j ≤ c * reading i)
    (a k : ι) {A : ℝ} (hA : 0 ≤ A) (J : ℤ)
    (hfaces : ∀ i, i ≠ k → ∃ (j : ℤ) (lo hi : ℝ),
      Path edge i a lo ∧ Path edge a i hi ∧ 0 ≤ (j : ℝ) + 1 / 8 ∧
      ((j : ℝ) + 1 / 8) * lo ≤ A ∧ A * hi ≤ (j : ℝ) + 7 / 8)
    (hlo : (J : ℝ) + 1 / 8 ≤ reading k * (A / reading a))
    (hhi : reading k * (A / reading a) < (J : ℝ) + 9 / 8) :
    let T := A / reading a
    IsMove (Finset.univ.image reading) T
      (if reading k * T ≤ (J : ℝ) + 7 / 8 then T else
        ((J : ℝ) + 9 / 8) / reading k) := by
  classical
  let T := A / reading a
  have other (i : ι) (hi : i ≠ k) : (1 / 8 : ℝ) ≤ distInt (reading i * T) := by
    obtain ⟨j, lo, hi', hin, hout, hj, hl, hu⟩ := hfaces i hi
    exact clear_of_paths reading hpos he hA j hin hout hj hl hu
  change IsMove (Finset.univ.image reading) T (if reading k * T ≤ (J : ℝ) + 7 / 8
    then T else ((J : ℝ) + 9 / 8) / reading k)
  by_cases hs : reading k * T ≤ (J : ℝ) + 7 / 8
  · rw [if_pos hs]
    refine Or.inl ⟨?_, rfl⟩
    intro r hr
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    apply not_lt.mpr
    by_cases hi : i = k
    · subst i
      exact clear_of_window J hlo hs
    · exact other i hi
  · rw [if_neg hs]
    have hband : |reading k * T - ((J + 1 : ℤ) : ℝ)| < 1 / 8 := by
      rw [abs_lt]
      push_cast
      exact ⟨by linarith only [lt_of_not_ge hs], by linarith only [hhi]⟩
    have hnext := nextOpening_eq hband
    have hexit : ((J : ℝ) + 9 / 8) / reading k = nextOpening (reading k) T := by
      rw [hnext]
      push_cast
      ring
    refine Or.inr ⟨reading k, Finset.mem_image_of_mem reading (Finset.mem_univ k),
      (Cascade.distInt_le _ (J + 1)).trans_lt hband, hexit, ?_⟩
    intro r hr hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    by_cases hi : i = k
    · subst i
      exact hexit.ge
    · exact (not_lt_of_ge (other i hi) hw).elim

#print axioms path_bound
#print axioms clear_of_paths
#print axioms fixes_of_paths
#print axioms strict_countermodel
#print axioms one_open_face

end Fresh.NativeHistoryRatioPaths
