import Fresh.RankFourTransfer

namespace Fresh.FiniteRelations

open Set
open scoped BigOperators

/-- There can be at most three strict increases while the rank is at most
three. Thus four transitions suffice, irrespective of the number of modes. -/
theorem stable_rank_transition {n : ℕ} (L : ℕ → Submodule ℝ (Fin n → ℝ))
    (hmono : Monotone L) (hrank : Module.finrank ℝ (L 4) ≤ 3) :
    ∃ j < 4, L j = L (j+1) := by
  by_contra! h
  have hstep (j : ℕ) (hj : j < 4) :
      Module.finrank ℝ (L j) < Module.finrank ℝ (L (j+1)) :=
    Submodule.finrank_lt_finrank_of_lt
      (lt_of_le_of_ne (hmono (Nat.le_succ j)) (h j hj))
  have h0 := hstep 0 (by decide)
  have h1 := hstep 1 (by decide)
  have h2 := hstep 2 (by decide)
  have h3 := hstep 3 (by decide)
  simp only [Nat.reduceAdd] at h0 h1 h2 h3
  omega

theorem shortSpan_mono {n : ℕ} {S T : Finset (Fin n → ℤ)} {v : Fin n → ℝ}
    {D E : ℝ} (hS : S ⊆ T) (hD : D ≤ E) :
    shortSpan S v D ≤ shortSpan T v E := by
  apply Submodule.span_mono
  rintro x ⟨m,hm,hf,rfl⟩
  exact ⟨m,hS hm,hf.trans hD,rfl⟩

/-- The bounded rank ladder only needs projected tests for spaces generated
at the *preceding* stage. In particular each stage needs only a finite
family of row spaces, regardless of the size of the input rates. -/
theorem clear_or_four_rows_of_ladder {n bound : ℕ}
    (S : ℕ → Finset (Fin n → ℤ)) (D : ℕ → ℝ)
    (hS : Monotone S) (hD : Monotone D) (hpos : 0 < D 0)
    (hb : ∀ m ∈ S 4, ∀ i, |m i| ≤ (bound : ℤ))
    (A : ℕ → (Fin n → ℤ) → ℂ) (ε μ : ℕ → ℝ)
    (ha : ∀ j < 4, ∑ m ∈ S (j+1), ‖A j m‖ ≤ 1)
    (hblocked : ∀ j < 4, ∀ x : Fin n → ℝ,
      (∃ i, distInt (x i) ≤ 1/8) → (phasePolynomial (S (j+1)) (A j) x).re ≤ ε j)
    (hproj : ∀ j < 4, ∀ T : Finset (Fin n → ℤ), T ⊆ S j →
      let L := Submodule.span ℝ ((fun m : Fin n → ℤ => fun i => (m i : ℝ)) '' (↑T : Set _))
      Module.finrank ℝ L ≤ 3 →
      (∃ w : Fin n → ℝ, (∀ i, 0 < w i) ∧ ∀ z ∈ L, ∑ i, z i*w i = 0) →
      ∀ x : Fin n → ℝ,
        μ j ≤ (phasePolynomial (projectedModes (S (j+1)) L) (A j) x).re +
              (phasePolynomial (projectedModes (S (j+1)) L) (A j)
                (fun i => 2*x i)).re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : Fin n → ℝ) (a b : ℝ), a < b →
      (∀ i, C*D 4 < v i) →
      (∀ j < 4, 2*ε j*(b-a) + 2/D (j+1) < μ j*(b-a)) →
      (∃ t ∈ Icc a b,
        (∀ i, (1/8:ℝ) < distInt (v i*t)) ∨
        (∀ i, (1/8:ℝ) < distInt (2*(v i*t)))) ∨
      (∃ rows : Fin 4 → Fin n → ℤ, (∀ j, rows j ∈ S 4) ∧
        (∀ j, |rowEval (rows j) v| ≤ D 4) ∧
        LinearIndependent ℝ (fun j i => (rows j i : ℝ))) := by
  classical
  obtain ⟨C,hC,hrows⟩ := four_short_rows_or_positive_annihilator n bound
  refine ⟨C,hC,fun v a b hab hv hgap => ?_⟩
  rcases hrows (S 4) v (D 4) (hpos.le.trans (hD (by decide))) hb hv with hfour | ⟨hr,hw⟩
  · exact Or.inr hfour
  let L (j : ℕ) := shortSpan (S j) v (D j)
  have hm : Monotone L := fun _ _ h => shortSpan_mono (hS h) (hD h)
  obtain ⟨j,hj,he⟩ := stable_rank_transition L hm hr
  have hj4 := hm (show j ≤ 4 by omega)
  let T := (S j).filter fun m => |rowEval m v| ≤ D j
  have hT : Submodule.span ℝ ((fun m : Fin n → ℤ => fun i => (m i : ℝ)) '' (↑T : Set _)) = L j := by
    unfold L shortSpan
    apply congrArg (Submodule.span ℝ)
    ext x
    simp only [T,Finset.coe_filter,Set.mem_image,Set.mem_setOf_eq]
    exact ⟨fun ⟨m,⟨hm,hf⟩,he⟩ => ⟨m,hm,hf,he.symm⟩,
      fun ⟨m,hm,hf,he⟩ => ⟨m,⟨hm,hf⟩,he.symm⟩⟩
  have hp := hproj j hj T (Finset.filter_subset _ _)
  rw [hT] at hp
  apply Or.inl
  apply clear_of_projected_polynomial (S (j+1)) (A j) (ha j hj) (L j) v (D (j+1))
    a b (ε j) (μ j) (hpos.trans_le (hD (Nat.zero_le _))) hab _ (hblocked j hj)
    (hp ((Submodule.finrank_mono hj4).trans hr) (by
      obtain ⟨w,hwpos,hwe⟩ := hw
      exact ⟨w,hwpos,fun z hz => hwe z (hj4 hz)⟩)) (hgap j hj)
  intro m hm'
  by_contra! hf
  obtain ⟨hmm,hnr⟩ := Finset.mem_sdiff.mp hm'
  apply hnr
  unfold projectedModes
  refine Finset.mem_filter.mpr ⟨hmm,?_⟩
  rw [he]
  exact mem_shortSpan hmm hf.le

#print axioms stable_rank_transition
#print axioms clear_or_four_rows_of_ladder

end Fresh.FiniteRelations
