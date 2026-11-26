import Fresh.TranslatedSixSmall
import Fresh.OpeningClump

/-!
Rules 1–4, 8–18. Two AP blocks sharing a unit step:
{1,…,r} ∪ {a,…,a+(6-r)}, 1≤r≤6.
The small branch retains all integer-shift laps at smallTime a;
the tail selects the translated block's opening inside the frozen AP window.
[PROVISIONAL: counting tool] at ceiling/opening selection, supporting
placement of the explicit instant. No covering or density argument.
-/
namespace Fresh.SplitAPBands
open Fresh Fresh.Localisation Fresh.TranslatedSix Fresh.OpeningClump

noncomputable def splitTrain (r : ℕ) (a : ℝ) : Finset ℝ :=
  (Finset.range r).image (fun j : ℕ => ((j+1 : ℕ) : ℝ)) ∪
    (Finset.range (7-r)).image (fun j : ℕ => a+(j : ℝ))

theorem shift_time_band {a : ℝ} (ha : 0 < a) :
    0 < smallTime a ∧ (1/8 : ℝ) ≤ a*smallTime a ∧
      a*smallTime a < 1/8+a := by
  have h1 := Int.le_ceil (1/(8*a)-1/8)
  have h2 := Int.ceil_lt_add_one (1/(8*a)-1/8)
  have he : a*(1/(8*a))=1/8 := by field_simp
  have hlo : 1/8≤a*smallTime a := by
    unfold smallTime
    have := mul_le_mul_of_nonneg_left h1 ha.le
    nlinarith
  have hhi : a*smallTime a<1/8+a := by
    unfold smallTime
    have := mul_lt_mul_of_pos_left h2 ha
    nlinarith
  refine ⟨?_,hlo,hhi⟩
  by_contra hn
  have : a*smallTime a≤0 := mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt hn)
  linarith

theorem split_train_small (r : ℕ) (hr1 : 1 ≤ r) (hr6 : r ≤ 6)
    (a : ℝ) (ha : 0 < a) (hb : a ≤ (r : ℝ)/8) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain r a, (1/8 : ℝ) ≤ distInt (d*t) := by
  obtain ⟨ht,hlo,hhi⟩ := shift_time_band ha
  let N : ℤ := ⌈1/(8*a)-1/8⌉
  have he : smallTime a=(N : ℝ)+1/8 := rfl
  refine ⟨smallTime a,ht,fun d hd => ?_⟩
  rcases Finset.mem_union.mp hd with hd | hd
  · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
    have hjr : j+1≤r := Finset.mem_range.mp hj
    have hj1 : (1 : ℝ)≤((j+1 : ℕ) : ℝ) := by exact_mod_cast (show 1≤j+1 by omega)
    have hj6 : ((j+1 : ℕ) : ℝ)≤6 := by exact_mod_cast (show j+1≤6 by omega)
    push_cast at hj1 hj6
    apply clear_of_window (((j+1 : ℕ) : ℤ)*N)
    · rw [he]; push_cast; nlinarith
    · rw [he]; push_cast; nlinarith
  · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
    have hjr : j+r≤6 := by have := Finset.mem_range.mp hj; omega
    have hjrR : (j : ℝ)+(r : ℝ)≤6 := by exact_mod_cast hjr
    have hj0 : (0 : ℝ)≤j := Nat.cast_nonneg _
    apply clear_of_window ((j : ℤ)*N)
    · push_cast
      have he2 : (a+(j : ℝ))*smallTime a=a*smallTime a+(j : ℝ)*(N+1/8) := by rw [he]; ring
      rw [he2]; nlinarith
    · push_cast
      have he2 : (a+(j : ℝ))*smallTime a=a*smallTime a+(j : ℝ)*(N+1/8) := by rw [he]; ring
      rw [he2]; nlinarith

theorem split_train_tail (r : ℕ) (hr1 : 1 ≤ r) (hr6 : r ≤ 6)
    (a : ℝ) (ha : 0 < a)
    (hsep : 8*(r : ℝ) ≤ a*(7-(r : ℝ)))
    (hwidth : 8*(6-(r : ℝ)) ≤ a*(r : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain r a, (1/8 : ℝ) ≤ distInt (d*t) := by
  have hrpos : (0 : ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have hr6R : (r : ℝ)≤6 := by exact_mod_cast hr6
  have hfit : 1/8+1/a≤7/(8*(r : ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0<8*(r : ℝ))).2
    have he : (1/8+1/a)*(8*(r : ℝ))=(a*(r : ℝ)+8*(r : ℝ))/a := by field_simp
    rw [he,div_le_iff₀ ha]
    nlinarith
  have hdev : (6-(r : ℝ))*(1/8+1/a)≤3/4 := by
    have he : (6-(r : ℝ))*(1/8+1/a)=((6-(r : ℝ))*a+8*(6-(r : ℝ)))/(8*a) := by field_simp
    rw [he,div_le_iff₀ (by positivity : 0<8*a)]
    nlinarith
  obtain ⟨h1,h2,h3⟩ := openingAfter_spec (lo:=(1/8 : ℝ)) ha
  have ht : 0<openingAfter a (1/8) := lt_of_lt_of_le (by norm_num) h1
  have hupper : openingAfter a (1/8)≤7/(8*(r : ℝ)) := h2.le.trans hfit
  refine ⟨openingAfter a (1/8),ht,fun d hd => ?_⟩
  rcases Finset.mem_union.mp hd with hd | hd
  · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
    have hjr : j+1≤r := Finset.mem_range.mp hj
    have hj1 : (1 : ℝ)≤((j+1 : ℕ) : ℝ) := by exact_mod_cast (show 1≤j+1 by omega)
    have hjrR : ((j+1 : ℕ) : ℝ)≤r := by exact_mod_cast hjr
    push_cast at hj1 hjrR
    have hrt : (r : ℝ)*openingAfter a (1/8)≤7/8 := by
      have := (le_div_iff₀ (by positivity : 0<8*(r : ℝ))).mp hupper
      nlinarith
    apply clear_of_window (0 : ℤ)
    · norm_num
      nlinarith [mul_le_mul_of_nonneg_right hj1 ht.le]
    · norm_num
      nlinarith [mul_le_mul_of_nonneg_right hjrR ht.le]
  · apply clump_at_opening ht.le h3 (w:=6-(r : ℝ)) (C:=(Finset.range (7-r)).image (fun j : ℕ=>a+(j : ℝ))) ?_ ?_ _ hd
    · intro d hd
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
      have hjR : (j : ℝ)+(r : ℝ)≤6 := by exact_mod_cast (show j+r≤6 by have := Finset.mem_range.mp hj; omega)
      have hj0 : (0 : ℝ)≤j := Nat.cast_nonneg _
      constructor <;> linarith
    · exact (mul_le_mul_of_nonneg_left h2.le (by linarith : 0≤6-(r : ℝ))).trans hdev

#print axioms split_train_tail

#print axioms shift_time_band
#print axioms split_train_small
end Fresh.SplitAPBands
