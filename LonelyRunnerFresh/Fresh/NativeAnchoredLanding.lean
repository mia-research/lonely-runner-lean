import Fresh.NativeAffineMoveFaces

namespace Fresh.NativeAnchoredLanding

open Fresh Cascade Localisation NativeAffineMoveFaces

/-- A proposed sequence of opening anchors and symbolic lap labels
certifies its first landing using only inequalities on the readings.
Each strict move excludes an earlier fixation. -/
theorem first_landing_of_faces {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (hx : ∀ i, 0 < x i) (a : ℕ → ι) (A : ℕ → ℝ) (J : ℕ → ι → ℤ)
    (N : ℕ)
    (hanchor : ∀ n < N, A (n + 1) = (J n (a (n + 1)) : ℝ) + 1 / 8)
    (htime : ∀ n < N, A n * x (a (n + 1)) < A (n + 1) * x (a n))
    (hphase : ∀ n < N, ∀ i, ((J n i : ℝ) - 1 / 8) * x (a n) < A n * x i ∧
      A n * x i ≤ ((J n i : ℝ) + 7 / 8) * x (a n))
    (horder : ∀ n < N, ∀ i, ((J n i : ℝ) + 1 / 8) * x (a (n + 1)) ≤
      A (n + 1) * x i)
    (K : ι → ℤ)
    (hfinal : ∀ i, ((K i : ℝ) + 1 / 8) * x (a N) ≤ A N * x i ∧
      A N * x i ≤ ((K i : ℝ) + 7 / 8) * x (a N)) :
    let seq := cascadeSeq (Finset.univ.image x) (A 0 / x (a 0))
    (∀ n < N, seq n < seq (n + 1)) ∧
      seq N = A N / x (a N) ∧ seq (N + 1) = seq N := by
  classical
  dsimp only
  have hp := prefix_of_faces x hx a A J N hanchor
    (fun n hn => (htime n hn).le) hphase horder
  refine ⟨?_, hp N le_rfl, ?_⟩
  · intro n hn
    rw [hp n hn.le, hp (n + 1) hn]
    exact (div_lt_div_iff₀ (hx (a n)) (hx (a (n + 1)))).2 (htime n hn)
  · have hfix : IsMove (Finset.univ.image x) (A N / x (a N)) (A N / x (a N)) := by
      refine Or.inl ⟨?_, rfl⟩
      intro r hr
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
      apply not_inWay_iff.mpr
      apply clear_of_window (K i)
      · rw [← mul_div_assoc, le_div_iff₀ (hx (a N)), mul_comm (x i)]
        exact (hfinal i).1
      · rw [← mul_div_assoc, div_le_iff₀ (hx (a N)), mul_comm (x i)]
        exact (hfinal i).2
    have hm := cascadeSeq_isMove (Finset.univ.image x) (A 0 / x (a 0)) N
    rw [hp N le_rfl] at hm ⊢
    exact isMove_unique hm hfix

#print axioms first_landing_of_faces

end Fresh.NativeAnchoredLanding
