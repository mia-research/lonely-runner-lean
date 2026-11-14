import Fresh.ProjectedTest
import Fresh.RankLadder

namespace Fresh.FiniteRelations

open Set
open scoped BigOperators

noncomputable section

structure Stage {n : ℕ} (S : Finset (Fin n → ℤ)) where
  modes : Finset (Fin n → ℤ)
  coeff : (Fin n → ℤ) → ℂ
  eps : ℝ
  mu : ℝ
  subset : S ⊆ modes
  gap : 0 < mu - 2*eps
  mass : ∑ m ∈ modes, ‖coeff m‖ ≤ 1
  blocked : ∀ x : Fin n → ℝ, (∃ i, distInt (x i) ≤ 1/8) →
    (phasePolynomial modes coeff x).re ≤ eps
  projected : ∀ T ⊆ S, AdmissibleRows T → ∀ x : Fin n → ℝ,
    mu ≤ (phasePolynomial (projectedModes modes (rowSpace T)) coeff x).re +
      (phasePolynomial (projectedModes modes (rowSpace T)) coeff (fun i => 2*x i)).re

def next {n : ℕ} (S : Finset (Fin n → ℤ)) : Stage S :=
  Classical.choice (by
    obtain ⟨S',A,ε,μ,h1,h2,h3,h4,h5⟩ := finite_projected_test S
    exact ⟨⟨S',A,ε,μ,h1,h2,h3,h4,h5⟩⟩)

def stages (n : ℕ) : ℕ → Finset (Fin n → ℤ)
  | 0 => ∅
  | j+1 => (next (stages n j)).modes

theorem rowSpace_eq_span_image {n : ℕ} (T : Finset (Fin n → ℤ)) :
    rowSpace T = Submodule.span ℝ ((fun m : Fin n → ℤ => fun i => (m i : ℝ)) '' (↑T : Set _)) := by
  unfold rowSpace
  congr 1
  ext x
  constructor
  · rintro ⟨m,rfl⟩
    exact ⟨m.val,m.property,rfl⟩
  · rintro ⟨m,hm,rfl⟩
    exact ⟨⟨m,hm⟩,rfl⟩

/-- Arbitrary fast real rates on any two buffered intervals J and 2J:
either an allowed time clears the fast block, or four independent
bounded integer rows have bounded evaluations on the actual rates.
The cutoffs depend only on the number of rates and a lower bound on
the interval length. No harmonic ansatz is assumed. -/
theorem buffered_clear_or_four_relations (n : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ (N : ℕ) (D C : ℝ), 0 < D ∧ 0 ≤ C ∧
      ∀ (v : Fin n → ℝ) (a b : ℝ), ℓ ≤ b-a → (∀ i, C < v i) →
        (∃ t ∈ Icc a b, (∀ i, (1/8:ℝ) < distInt (v i*t)) ∨
          (∀ i, (1/8:ℝ) < distInt (2*(v i*t)))) ∨
        (∃ rows : Fin 4 → Fin n → ℤ, (∀ j i, |rows j i| ≤ (N:ℤ)) ∧
          (∀ j, |rowEval (rows j) v| ≤ D) ∧
          LinearIndependent ℝ (fun j i => (rows j i : ℝ))) := by
  classical
  let S := stages n
  let A (j : ℕ) := (next (S j)).coeff
  let ε (j : ℕ) := (next (S j)).eps
  let μ (j : ℕ) := (next (S j)).mu
  have hμ (j : ℕ) : 0 < μ j-2*ε j := (next (S j)).gap
  let D : ℕ → ℝ := Nat.rec 1 (fun j r => max r (1 + 2/(ℓ*(μ j-2*ε j))))
  have hS : Monotone S := monotone_nat_of_le_succ fun j => (next (S j)).subset
  have hD : Monotone D := monotone_nat_of_le_succ fun j => le_max_left _ _
  have hD0 : 0 < D 0 := by change (0:ℝ) < 1; norm_num
  let N := ∑ m ∈ S 4, ∑ i : Fin n, (m i).natAbs
  have hb (m : Fin n → ℤ) (hm : m ∈ S 4) (i : Fin n) : |m i| ≤ (N : ℤ) := by
    have h1 : (m i).natAbs ≤ ∑ i : Fin n, (m i).natAbs :=
      Finset.single_le_sum (f := fun k : Fin n => (m k).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have h2 : (∑ i : Fin n, (m i).natAbs) ≤ N :=
      Finset.single_le_sum (f := fun z : Fin n → ℤ => ∑ i : Fin n, (z i).natAbs)
        (fun _ _ => Nat.zero_le _) hm
    rw [← Int.natCast_natAbs]
    exact_mod_cast h1.trans h2
  obtain ⟨C,hC,hh⟩ := clear_or_four_rows_of_ladder S D hS hD hD0 hb A ε μ
    (fun j _ => (next (S j)).mass) (fun j _ => (next (S j)).blocked) (by
      intro j _ T hT
      dsimp only
      rw [← rowSpace_eq_span_image T]
      intro h₁ h₂
      exact (next (S j)).projected T hT ⟨h₁,h₂⟩)
  have hD4 : 0 < D 4 := hD0.trans_le (hD (show (0:ℕ) ≤ 4 by decide))
  refine ⟨N,D 4,C*D 4,hD4,mul_nonneg hC hD4.le,fun v a b hab hv => ?_⟩
  have hab' : a < b := by linarith
  have hgap (j : ℕ) (_ : j < 4) :
      2*ε j*(b-a) + 2/D (j+1) < μ j*(b-a) := by
    have hpos : 0 < ℓ*(μ j-2*ε j) := mul_pos hℓ (hμ j)
    have hbig : 2/(ℓ*(μ j-2*ε j)) < D (j+1) :=
      (by linarith : 2/(ℓ*(μ j-2*ε j)) < 1+2/(ℓ*(μ j-2*ε j))).trans_le (le_max_right _ _)
    have he := (div_lt_iff₀ hpos).1 hbig
    have hd : 0 < D (j+1) := hD0.trans_le (hD (Nat.zero_le (j+1)))
    have h := (div_lt_iff₀ hd).2 (show 2 < (ℓ*(μ j-2*ε j))*D (j+1) by
      simpa only [mul_comm] using he)
    have hg := h.trans_le (mul_le_mul_of_nonneg_right hab (hμ j).le)
    nlinarith only [hg]
  rcases hh v a b hab' hv hgap with h | ⟨r,hr,hv',hli⟩
  · exact Or.inl h
  · exact Or.inr ⟨r,fun j => hb _ (hr j),hv',hli⟩

#print axioms buffered_clear_or_four_relations

end
end Fresh.FiniteRelations
