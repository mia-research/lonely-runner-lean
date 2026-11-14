import Fresh.BufferedSectors

namespace Fresh.FiniteRelations

open Set
open scoped BigOperators

/-- Rescaling the input on an unrestricted time horizon turns the bounded
approximate relations into exact relations from the same finite catalogue. -/
theorem positive_clear_or_exact_four_kernel (n : ℕ) :
    ∃ N : ℕ, ∀ v : Fin n → ℝ, (∀ i, 0 < v i) →
      (∃ t : ℝ, 0 < t ∧ ∀ i, (1/8:ℝ) < distInt (v i*t)) ∨
      ∃ A : RowTable n 4 N, v ∈ LinearMap.ker (evaluate (tableRows A)) ∧
        Module.finrank ℝ (LinearMap.range (evaluate (tableRows A))) = 4 := by
  classical
  obtain ⟨N,D,C,hD,hC,h⟩ := buffered_clear_or_four_relations n (show (0:ℝ) < 1 by norm_num)
  refine ⟨N,fun v hv => ?_⟩
  let f (i : Fin n) := C/v i
  let g (a : RowTable n 4 N × Fin 4) := D/|rowEval (tableRows a.1 a.2) v|
  have hf (i : Fin n) : 0 ≤ f i := div_nonneg hC (hv i).le
  have hg (a : RowTable n 4 N × Fin 4) : 0 ≤ g a := div_nonneg hD.le (abs_nonneg _)
  have hF : 0 ≤ ∑ i, f i := Finset.sum_nonneg fun i _ => hf i
  have hG : 0 ≤ ∑ a, g a := Finset.sum_nonneg fun a _ => hg a
  let K := 1 + (∑ i, f i) + ∑ a, g a
  have hK : 0 < K := by dsimp [K]; linarith
  have hfi (i : Fin n) : f i < K := by
    have hi := Finset.single_le_sum (f := f) (fun i _ => hf i) (Finset.mem_univ i)
    dsimp [K]
    linarith
  have hga (a : RowTable n 4 N × Fin 4) : g a < K := by
    have ha := Finset.single_le_sum (f := g) (fun i _ => hg i) (Finset.mem_univ a)
    dsimp [K]
    linarith
  let w (i : Fin n) := K * v i
  have hw (i : Fin n) : C < w i := (div_lt_iff₀ (hv i)).mp (hfi i)
  rcases h w 1 2 (by norm_num) hw with ⟨t,ht,h1 | h2⟩ | ⟨r,hr,hfreq,hli⟩
  · refine Or.inl ⟨K*t,mul_pos hK (zero_lt_one.trans_le ht.1),fun i => ?_⟩
    convert h1 i using 2
    dsimp [w]
    ring
  · refine Or.inl ⟨2*K*t,by have := ht.1; positivity,fun i => ?_⟩
    convert h2 i using 2
    dsimp [w]
    ring
  obtain ⟨A,hA⟩ := tableRows_surj r hr
  have he (j : Fin 4) : rowEval (tableRows A j) v = 0 := by
    by_contra hn
    have hl := (div_lt_iff₀ (abs_pos.mpr hn)).mp (hga (A,j))
    have hh := hfreq j
    rw [← hA] at hh
    have hm : rowEval (tableRows A j) w = K * rowEval (tableRows A j) v := by
      unfold rowEval
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [w]
      ring
    rw [hm,abs_mul,abs_of_pos hK] at hh
    exact (not_lt_of_ge hh) hl
  apply Or.inr
  refine ⟨A,LinearMap.mem_ker.mpr (funext he),?_⟩
  rw [hA]
  change (Matrix.rank (fun j i => (r j i : ℝ) : Matrix (Fin 4) (Fin n) ℝ)) = 4
  rw [Matrix.rank_eq_finrank_span_row]
  change Module.finrank ℝ (Submodule.span ℝ (range (fun j i => (r j i : ℝ)))) = 4
  rw [finrank_span_eq_card hli,Fintype.card_fin]

/-- A finite family of exact three-dimensional kernels suffices for
classical eight-runner isolation. -/
theorem lonelyRunnerEight_iff_exact_four_kernels :
    ∃ N : ℕ, LonelyRunnerEight ↔
      ∀ A : RowTable 7 4 N, Module.finrank ℝ (LinearMap.range (evaluate (tableRows A))) = 4 →
      ∀ v : Fin 8 → ℝ, IsArrangement v → ∀ k : Fin 8,
        (fun i => |v (k.succAbove i)-v k|) ∈ LinearMap.ker (evaluate (tableRows A)) →
        Isolation v k := by
  obtain ⟨N,h⟩ := positive_clear_or_exact_four_kernel 7
  refine ⟨N,⟨fun h _ _ v hv k _ => h v hv k,?_⟩⟩
  intro hc v hv k
  have hp (i : Fin 7) : 0 < |v (k.succAbove i)-v k| := by
    exact abs_pos.mpr (sub_ne_zero.mpr (fun he => Fin.succAbove_ne _ _ (hv.2 he)))
  rcases h _ hp with ⟨t,ht,hi⟩ | ⟨A,hA,hr⟩
  · refine ⟨t,ht,(Cascade.isolatedAt_iff_lonelyAt v k _).2 ?_⟩
    intro d hd
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨i,rfl⟩ := Fin.exists_succAbove_eq (Finset.mem_erase.mp hl).1
    exact (hi i).le
  · exact hc A hr v hv k hA

#print axioms positive_clear_or_exact_four_kernel
#print axioms lonelyRunnerEight_iff_exact_four_kernels

end Fresh.FiniteRelations
