import Fresh.FiniteRelations

set_option maxRecDepth 4096

namespace Fresh.FiniteRelations

open scoped BigOperators

/-- The linear map whose entries are the real evaluations of a tuple of integer rows. -/
noncomputable def evaluate {n r : ℕ} (rows : Fin r → Fin n → ℤ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin r → ℝ) :=
  (Matrix.mulVecLin (fun i j => (rows i j : ℝ)))

theorem evaluate_apply {n r : ℕ} (rows : Fin r → Fin n → ℤ) (v : Fin n → ℝ)
    (i : Fin r) : evaluate rows v i = ∑ j, (rows i j : ℝ)*v j := rfl

/-- A finite family of linear maps admits a uniform bound on the
correction needed to move an input into its corresponding kernel. -/
theorem uniform_kernel_correction {ι : Type*} [Fintype ι] {n r : ℕ}
    (A : ι → (Fin n → ℝ) →ₗ[ℝ] (Fin r → ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i v, ∃ w ∈ LinearMap.ker (A i), ‖v-w‖ ≤ C * ‖A i v‖ := by
  classical
  have sectionExists (i : ι) :
      ∃ g : (Fin r → ℝ) →L[ℝ] (Fin n → ℝ), ∀ v, A i (g (A i v)) = A i v := by
    let R := LinearMap.range (A i)
    obtain ⟨f,hf⟩ := (A i).rangeRestrict.exists_rightInverse_of_surjective
      (A i).range_rangeRestrict
    obtain ⟨e,he⟩ := R.subtype.exists_leftInverse_of_injective R.ker_subtype
    refine ⟨LinearMap.toContinuousLinearMap (f.comp e), fun v => ?_⟩
    have hy : e (A i v) = (A i).rangeRestrict v :=
      DFunLike.congr_fun he ((A i).rangeRestrict v)
    change A i (f (e (A i v))) = A i v
    rw [hy]
    exact congrArg Subtype.val (DFunLike.congr_fun hf ((A i).rangeRestrict v))
  choose g hg using sectionExists
  let C : ℝ := ∑ i, ‖g i‖
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => norm_nonneg _
  refine ⟨C,hC,fun i v => ?_⟩
  refine ⟨v-g i (A i v), ?_, ?_⟩
  · rw [LinearMap.mem_ker, map_sub, hg i, sub_self]
  · rw [sub_sub_cancel]
    have hgC : ‖g i‖ ≤ C :=
      Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => norm_nonneg (g j)) (Finset.mem_univ i)
    exact ((g i).le_opNorm (A i v)).trans (mul_le_mul_of_nonneg_right hgC (norm_nonneg _))

/-- Bounded integer matrices form a finite type for any chosen row bound. -/
abbrev RowTable (n r bound : ℕ) := Fin r → Fin n → Fin (2*bound+1)

def tableRows {n r bound : ℕ} (A : RowTable n r bound) : Fin r → Fin n → ℤ :=
  fun i j => ((A i j).val : ℤ)-bound

theorem tableRows_surj {n r bound : ℕ} (rows : Fin r → Fin n → ℤ)
    (hb : ∀ i j, |rows i j| ≤ (bound : ℤ)) :
    ∃ A : RowTable n r bound, tableRows A = rows := by
  have hnonneg (i : Fin r) (j : Fin n) : 0 ≤ rows i j + (bound : ℤ) := by
    have := (abs_le.mp (hb i j)).1
    omega
  let A : RowTable n r bound := fun i j =>
    ⟨(rows i j + (bound : ℤ)).toNat, by
      have := (abs_le.mp (hb i j)).2
      have := hnonneg i j
      omega⟩
  refine ⟨A,?_⟩
  funext i j
  unfold tableRows A
  rw [Int.toNat_of_nonneg (hnonneg i j)]
  omega

/-- Approximate integer relations reduce to finitely many exact real
kernels plus a uniformly bounded additive error. The dimension is
computed from the rank of the same relation matrix. -/
theorem bounded_rows_kernel_types (n r bound : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : Fin n → ℝ) (D : ℝ), 0 ≤ D →
      ∀ rows : Fin r → Fin n → ℤ, (∀ i j, |rows i j| ≤ (bound : ℤ)) →
      (∀ i, |∑ j, (rows i j : ℝ)*v j| ≤ D) →
      ∃ A : RowTable n r bound,
        tableRows A = rows ∧
        ∃ w ∈ LinearMap.ker (evaluate (tableRows A)),
          ‖v-w‖ ≤ C*D ∧
          Module.finrank ℝ (LinearMap.ker (evaluate (tableRows A))) +
            Module.finrank ℝ (LinearMap.range (evaluate rows)) = n := by
  obtain ⟨C,hC,h⟩ := uniform_kernel_correction
    (fun A : RowTable n r bound => evaluate (tableRows A))
  refine ⟨C,hC,fun v D hD rows hb hr => ?_⟩
  obtain ⟨A,hA⟩ := tableRows_surj rows hb
  obtain ⟨w,hw,he⟩ := h A v
  have hv : ‖evaluate (tableRows A) v‖ ≤ D := by
    apply (pi_norm_le_iff_of_nonneg hD).2
    intro i
    simpa only [hA, Real.norm_eq_abs, evaluate_apply] using hr i
  refine ⟨A,hA,w,hw,he.trans (mul_le_mul_of_nonneg_left hv hC),?_⟩
  rw [hA, add_comm]
  simpa using (LinearMap.finrank_range_add_finrank_ker (evaluate rows))

#print axioms uniform_kernel_correction
#print axioms bounded_rows_kernel_types



/-- For an arbitrary real arrangement, the first reduction uses proper
kernels of dimension five, rather than general subsets of rate space. -/
theorem arrangement_cascade_or_kernel (v : Fin 8 → ℝ) (hv : IsArrangement v) (k : Fin 8)
    {minimum : ℝ} (hm : IsDmin v k minimum) :
    CascadeFixes (disparitySet v k) (1/(8*minimum)) ∨
      ∃ j : Fin 7, |v (k.succAbove j)-v k| = minimum ∧
        ∃ m ∈ catalogue 6,
          Module.finrank ℝ (LinearMap.ker (evaluate (fun _ : Fin 1 => row m))) = 5 ∧
          ∃ w ∈ LinearMap.ker (evaluate (fun _ : Fin 1 => row m)),
            ‖reducedReadings v k j minimum-w‖ ≤ (4*10^9/3:ℝ) := by
  rcases arrangement_cascade_or_relation v hv k hm with hfix | ⟨j,hj,m,hmem,hfreq⟩
  · exact Or.inl hfix
  let rows : Fin 1 → Fin 6 → ℤ := fun _ => row m
  let x := reducedReadings v k j minimum
  have hmne : m ≠ center 6 := (mem_catalogue m).1 hmem
  have hrow : row m ≠ 0 := row_ne_zero hmne
  obtain ⟨j₀,hj₀⟩ := Function.ne_iff.mp hrow
  change row m j₀ ≠ 0 at hj₀
  let z : ℝ := row m j₀
  have hz : z ≠ 0 := by dsimp [z]; exact_mod_cast hj₀
  have hzabs : 1 ≤ |z| := by
    have hh : (1:ℤ) ≤ |row m j₀| := by
      have ha := abs_pos.mpr hj₀
      omega
    dsimp [z]
    exact_mod_cast hh
  have hs (u : ℝ) (i : Fin 1) : evaluate rows (Pi.single j₀ u) i = z*u := by
    rw [evaluate_apply, Finset.sum_eq_single j₀]
    · simp [Pi.single_eq_same,rows,z]
    · intro l _ hl
      simp [Pi.single_eq_of_ne hl]
    · simp
  have hsurj : Function.Surjective (evaluate rows) := by
    intro y
    refine ⟨Pi.single j₀ (y 0/z),?_⟩
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [hs]
    field_simp
  have hrange : LinearMap.range (evaluate rows) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hd := LinearMap.finrank_range_add_finrank_ker (evaluate rows)
  rw [hrange, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hd
  have hdim : Module.finrank ℝ (LinearMap.ker (evaluate rows)) = 5 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hd
    omega
  let correction : Fin 6 → ℝ := Pi.single j₀ (frequency m x/z)
  refine Or.inr ⟨j,hj,m,hmem,hdim,x-correction,?_ ,?_⟩
  · change x-correction ∈ LinearMap.ker (evaluate rows)
    rw [LinearMap.mem_ker, map_sub]
    funext i
    change evaluate rows x i - evaluate rows correction i = 0
    rw [show evaluate rows x i = frequency m x by rfl, show evaluate rows correction i =
      z * (frequency m x/z) from hs _ _]
    field_simp
    ring
  · change ‖x-(x-correction)‖ ≤ _
    rw [sub_sub_cancel, show correction = Pi.single j₀ (frequency m x/z) by rfl,
      Pi.norm_single, Real.norm_eq_abs, abs_div]
    exact (div_le_self (abs_nonneg _) hzabs).trans hfreq

#print axioms arrangement_cascade_or_kernel



/-- The four-row reduction used by the fast sectors. A sufficiently
positive input has a positive representative in the exact kernel.
For five readings the kernel is a line, and for six it is a plane. -/
theorem four_rows_positive_kernel (n bound : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : Fin n → ℝ) (D : ℝ), 0 ≤ D →
      (∀ j, C*D < v j) →
      ∀ rows : Fin 4 → Fin n → ℤ, (∀ i j, |rows i j| ≤ (bound : ℤ)) →
      (∀ i, |∑ j, (rows i j : ℝ)*v j| ≤ D) →
      Module.finrank ℝ (LinearMap.range (evaluate rows)) = 4 →
      ∃ A : RowTable n 4 bound,
        ∃ w ∈ LinearMap.ker (evaluate (tableRows A)),
          ‖v-w‖ ≤ C*D ∧ (∀ j, 0 < w j) ∧
          Module.finrank ℝ (LinearMap.ker (evaluate (tableRows A))) = n-4 := by
  obtain ⟨C,hC,h⟩ := bounded_rows_kernel_types n 4 bound
  refine ⟨C,hC,fun v D hD hv rows hb hr hrank => ?_⟩
  obtain ⟨A,_,w,hw,he,hd⟩ := h v D hD rows hb hr
  refine ⟨A,w,hw,he,fun j => ?_,?_⟩
  · have hj := (norm_le_pi_norm (v-w) j).trans he
    change ‖v j-w j‖ ≤ C*D at hj
    rw [Real.norm_eq_abs] at hj
    linarith only [hv j, (abs_le.mp hj).2]
  · omega

#print axioms four_rows_positive_kernel

end Fresh.FiniteRelations
