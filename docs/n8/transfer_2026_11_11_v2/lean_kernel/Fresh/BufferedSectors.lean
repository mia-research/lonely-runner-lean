import Fresh.BufferedFast
import Fresh.HarmonicSlow

namespace Fresh.FiniteRelations

open Set Fresh.Harmonic
open scoped BigOperators

/-- The finite types are row tables; each is used only if its kernel
contains a positive vector close to the actual rates. -/
def NearKernelType {n : ℕ} (N : ℕ) (E : ℝ) (v : Fin n → ℝ) : Prop :=
  ∃ A : RowTable n 4 N, ∃ w ∈ LinearMap.ker (evaluate (tableRows A)),
    ‖v-w‖ ≤ E ∧ (∀ i, 0 < w i) ∧
      Module.finrank ℝ (LinearMap.ker (evaluate (tableRows A))) = n-4

theorem buffered_clear_or_finite_kernels (n : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ (N : ℕ) (E C : ℝ), 0 ≤ E ∧ 0 ≤ C ∧
      ∀ (v : Fin n → ℝ) (a b : ℝ), ℓ ≤ b-a → (∀ i, C < v i) →
        (∃ t ∈ Icc a b, (∀ i, (1/8:ℝ) < distInt (v i*t)) ∨
          (∀ i, (1/8:ℝ) < distInt (2*(v i*t)))) ∨ NearKernelType N E v := by
  obtain ⟨N,D,C,hD,hC,h⟩ := buffered_clear_or_four_relations n hℓ
  obtain ⟨B,hB,hK⟩ := four_rows_positive_kernel n N
  refine ⟨N,B*D,max C (B*D),mul_nonneg hB hD.le,hC.trans (le_max_left _ _),
    fun v a b hl hv => ?_⟩
  rcases h v a b hl (fun i => (le_max_left _ _).trans_lt (hv i)) with ht | ⟨r,hr,hf,hi⟩
  · exact Or.inl ht
  apply Or.inr
  apply hK v D hD.le (fun i => (le_max_right _ _).trans_lt (hv i)) r hr hf
  change (Matrix.rank (fun j i => (r j i : ℝ) : Matrix (Fin 4) (Fin n) ℝ)) = 4
  rw [Matrix.rank_eq_finrank_span_row]
  change Module.finrank ℝ (Submodule.span ℝ (range (fun j i => (r j i : ℝ)))) = 4
  rw [finrank_span_eq_card hi,Fintype.card_fin]

private theorem nearby_window {s t e : ℝ} (ht : Buffered t e) (h : |s-t| ≤ e) :
    InWindows s := by
  obtain ⟨hl,hu⟩ := abs_le.mp h
  rcases ht with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact Or.inl ⟨by linarith,by linarith⟩
  · exact Or.inr ⟨by linarith,by linarith⟩

private theorem nearby_slow {a s t e : ℝ} (ha : 0 ≤ a)
    (ht : 1/8+e ≤ distInt (a*t)) (h : a*|s-t| ≤ e) :
    (1/8:ℝ) ≤ distInt (a*s) := by
  have hh := phase_distance_le (a*t) (a*s)
  rw [← mul_sub,abs_mul,abs_of_nonneg ha,abs_sub_comm t s] at hh
  linarith

/-- For a bounded second slow rate and five fast rates, the actual two
cascade windows supply the intervals required by the finite reduction. -/
theorem five_fast_window_types {A : ℝ} (hA : 1 ≤ A) :
    ∃ (N : ℕ) (E C : ℝ), 0 ≤ E ∧ 0 ≤ C ∧
      ∀ (a : ℝ) (v : Fin 5 → ℝ), 1 ≤ a → a ≤ A → (∀ i, C < v i) →
        (∃ t : ℝ, InWindows t ∧ (1/8:ℝ) ≤ distInt t ∧ (1/8:ℝ) ≤ distInt (a*t) ∧
          ∀ i, (1/8:ℝ) < distInt (v i*t)) ∨ NearKernelType N E v := by
  let δ : ℝ := 1/(320*A)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N,E,C,hE,hC,h⟩ := buffered_clear_or_finite_kernels 5 (show 0 < 2*δ by positivity)
  refine ⟨N,E,C,hE,hC,fun a v ha haA hv => ?_⟩
  obtain ⟨t,ht⟩ := slow125 a ha
  have hsize : A*(2*δ) = 1/160 := by dsimp [δ]; field_simp; ring
  have hdsmall : 2*δ ≤ 1/80 := by
    nlinarith only [hsize,mul_nonneg (sub_nonneg.mpr hA) hδ.le]
  have hadsmall : a*(2*δ) ≤ 1/80 :=
    (mul_le_mul_of_nonneg_right haA (by positivity)).trans (by rw [hsize]; norm_num)
  have hslow (q : ℕ) (hq : q ∈ [1,2,5]) (s : ℝ)
      (hs : |s-(q:ℝ)*t| ≤ 2*δ) :
      InWindows s ∧ (1/8:ℝ) ≤ distInt s ∧ (1/8:ℝ) ≤ distInt (a*s) := by
    obtain ⟨hb,hb'⟩ := ht q hq
    refine ⟨nearby_window hb (hs.trans hdsmall),?_,?_⟩
    · simpa only [one_mul] using nearby_slow (a := 1) (by norm_num)
        (by simpa only [one_mul] using pinned_buffer hb) (by simpa only [one_mul] using hs.trans hdsmall)
    · exact nearby_slow (zero_le_one.trans ha) (by linarith) <|
        (mul_le_mul_of_nonneg_left hs (zero_le_one.trans ha)).trans hadsmall
  rcases h v (t-δ) (t+δ) (by linarith) hv with ⟨s,hs,hv'⟩ | hK
  · have hst : |s-t| ≤ δ := abs_le.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩
    rcases hv' with hf | hf
    · have hs' := hst.trans (show δ ≤ 2*δ by linarith)
      have h₁ := hslow 1 (by simp) s (by simpa only [Nat.cast_one,one_mul] using hs')
      exact Or.inl ⟨s,h₁.1,h₁.2.1,h₁.2.2,hf⟩
    · have h₂ := hslow 2 (by simp) (2*s) (by
        rw [Nat.cast_ofNat,← mul_sub,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
        exact mul_le_mul_of_nonneg_left hst (by norm_num))
      exact Or.inl ⟨2*s,h₂.1,h₂.2.1,h₂.2.2,fun i => by
        rw [← mul_assoc, mul_comm (v i) 2, mul_assoc]; exact hf i⟩
  · exact Or.inr hK

/-- With only the pinned slow rate, the same generic proof gives a
finite family of plane types for six fast rates. -/
theorem six_fast_window_types :
    ∃ (N : ℕ) (E C : ℝ), 0 ≤ E ∧ 0 ≤ C ∧
      ∀ v : Fin 6 → ℝ, (∀ i, C < v i) →
        (∃ t : ℝ, InWindows t ∧ (1/8:ℝ) ≤ distInt t ∧
          ∀ i, (1/8:ℝ) < distInt (v i*t)) ∨ NearKernelType N E v := by
  obtain ⟨N,E,C,hE,hC,h⟩ := buffered_clear_or_finite_kernels 6 (show (0:ℝ) < 1/80 by norm_num)
  refine ⟨N,E,C,hE,hC,fun v hv => ?_⟩
  rcases h v (3/20-1/160) (3/20+1/160) (by norm_num) hv with ⟨s,hs,hf⟩ | hK
  · have hst : |s-3/20| ≤ 1/160 := abs_le.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩
    have hl (q : ℕ) (hq : q ∈ [1,2,3,4,5]) (y : ℝ)
        (hy : |y-(q:ℝ)*(3/20)| ≤ 1/40) :
        InWindows y ∧ (1/8:ℝ) ≤ distInt y := by
      have hb := slow12345 q hq
      refine ⟨nearby_window hb hy,?_⟩
      simpa only [one_mul] using nearby_slow (a := 1) (by norm_num)
        (by simpa only [one_mul] using pinned_buffer hb) (by simpa only [one_mul] using hy)
    rcases hf with hf | hf
    · have hs' := hst.trans (by norm_num : (1/160:ℝ) ≤ 1/40)
      have h₁ := hl 1 (by simp) s (by simpa only [Nat.cast_one,one_mul] using hs')
      exact Or.inl ⟨s,h₁.1,h₁.2,hf⟩
    · have h₂ := hl 2 (by simp) (2*s) (by
        rw [Nat.cast_ofNat,← mul_sub,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
        linarith)
      exact Or.inl ⟨2*s,h₂.1,h₂.2,fun i => by rw [← mul_assoc, mul_comm (v i) 2, mul_assoc]; exact hf i⟩
  · exact Or.inr hK

/-- Sorted normalized readings enter one of the two checked fast sectors,
or their three smallest rates are bounded. No prior speed split is needed. -/
theorem normalized_fast_dispatch :
    ∃ (B : ℝ) (N₅ N₆ : ℕ) (E₅ E₆ : ℝ), 1 ≤ B ∧ 0 ≤ E₅ ∧ 0 ≤ E₆ ∧
      ∀ (a b : ℝ) (v : Fin 4 → ℝ), 1 ≤ a → a ≤ b → (∀ i, b ≤ v i) →
        (∃ t : ℝ, InWindows t ∧ (1/8:ℝ) ≤ distInt t ∧
          (1/8:ℝ) ≤ distInt (a*t) ∧ (1/8:ℝ) ≤ distInt (b*t) ∧
          ∀ i, (1/8:ℝ) ≤ distInt (v i*t)) ∨
        NearKernelType N₅ E₅ (Fin.cons b v) ∨
        NearKernelType N₆ E₆ (Fin.cons a (Fin.cons b v)) ∨ b ≤ B := by
  obtain ⟨N₆,E₆,C₆,hE₆,_,h₆⟩ := six_fast_window_types
  let A := max 1 C₆
  obtain ⟨N₅,E₅,C₅,hE₅,_,h₅⟩ := five_fast_window_types (le_max_left 1 C₆)
  let B := max A C₅
  refine ⟨B,N₅,N₆,E₅,E₆,(le_max_left _ _).trans (le_max_left _ _),hE₅,hE₆,
    fun a b v ha hab hv => ?_⟩
  by_cases ha₆ : C₆ < a
  · let f : Fin 6 → ℝ := Fin.cons a (Fin.cons b v)
    have hfast (i : Fin 6) : C₆ < f i := by
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
      · simpa [f] using ha₆
      · simpa [f] using ha₆.trans_le hab
      · simpa [f] using ha₆.trans_le (hab.trans (hv k))
    rcases h₆ f hfast with ⟨t,ht,hp,hf⟩ | hK
    · exact Or.inl ⟨t,ht,hp,(hf 0).le,(hf 1).le,fun i => (hf i.succ.succ).le⟩
    · exact Or.inr (Or.inr (Or.inl hK))
  have haA : a ≤ A := (le_of_not_gt ha₆).trans (le_max_right _ _)
  by_cases hb : C₅ < b
  · let f : Fin 5 → ℝ := Fin.cons b v
    have hfast (i : Fin 5) : C₅ < f i := by
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [f] using hb
      · simpa [f] using hb.trans_le (hv j)
    rcases h₅ a f ha haA hfast with ⟨t,ht,hp,hs,hf⟩ | hK
    · exact Or.inl ⟨t,ht,hp,hs,(hf 0).le,fun i => (hf i.succ).le⟩
    · exact Or.inr (Or.inl hK)
  exact Or.inr (Or.inr (Or.inr ((le_of_not_gt hb).trans (le_max_right _ _))))

#print axioms five_fast_window_types
#print axioms six_fast_window_types
#print axioms normalized_fast_dispatch

end Fresh.FiniteRelations
