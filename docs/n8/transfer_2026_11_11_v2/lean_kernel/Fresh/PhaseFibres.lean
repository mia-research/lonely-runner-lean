import Fresh.Cascade

namespace Fresh.FiniteRelations

open scoped BigOperators

/-- A row evaluation on the real rates or phases. -/
def rowEval {n : ℕ} (m : Fin n → ℤ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, (m i : ℝ) * x i

theorem clear_quarter {t : ℝ} (hl : 1/4 ≤ t) (hu : t ≤ 3/4) :
    1/4 ≤ distInt t := by
  unfold distInt
  by_cases h : round t ≤ 0
  · have h' : (round t : ℝ) ≤ 0 := by exact_mod_cast h
    exact (by linarith : (1/4:ℝ) ≤ t-(round t:ℝ)).trans (le_abs_self _)
  · have h' : (1:ℝ) ≤ (round t : ℝ) := by
      exact_mod_cast (show (1:ℤ) ≤ round t by omega)
    exact (by linarith : (1/4:ℝ) ≤ -(t-(round t:ℝ))).trans (neg_le_abs _)

/-- A single row with at least two nonzero coefficients can be matched
exactly while clearing every phase at distance one quarter. The only
integer translation is in the coordinate of the smaller coefficient. -/
theorem rank_one_fibre {n : ℕ} (m : Fin n → ℤ) (x : Fin n → ℝ)
    {i j : Fin n} (hne : i ≠ j) (hi : m i ≠ 0)
    (hsmall : |(m i : ℝ)| ≤ |(m j : ℝ)|) :
    ∃ y : Fin n → ℝ, rowEval m y = rowEval m x ∧ ∀ l, (1/4:ℝ) ≤ distInt (y l) := by
  classical
  let a : ℝ := m i
  let b : ℝ := m j
  have ha : a ≠ 0 := by dsimp [a]; exact_mod_cast hi
  have hab : |a| ≤ |b| := hsmall
  let base : Fin n → ℝ := fun _ => 1/2
  let target := rowEval m x - rowEval m base
  let k : ℤ := round (target/a)
  let d := target-a*(k:ℝ)
  let u := d/(|a|+|b|)
  let sa : ℝ := if a < 0 then -1 else 1
  let sb : ℝ := if b < 0 then -1 else 1
  have hsa : a*sa = |a| := by
    by_cases h : a < 0
    · simp [sa,h,abs_of_neg h]
    · simp [sa,h,abs_of_nonneg (le_of_not_gt h)]
  have hsb : b*sb = |b| := by
    by_cases h : b < 0
    · simp [sb,h,abs_of_neg h]
    · simp [sb,h,abs_of_nonneg (le_of_not_gt h)]
  have has : |sa| = 1 := by unfold sa; split <;> norm_num
  have hbs : |sb| = 1 := by unfold sb; split <;> norm_num
  have hden : 0 < |a|+|b| := add_pos_of_pos_of_nonneg (abs_pos.mpr ha) (abs_nonneg _)
  have hd : |d| ≤ |a|/2 := by
    have he : d = a*(target/a-(k:ℝ)) := by dsimp [d]; field_simp
    rw [he,abs_mul]
    have hr : |target/a-(k:ℝ)| ≤ 1/2 := abs_sub_round _
    simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hr (abs_nonneg a)
  have hu : |u| ≤ 1/4 := by
    rw [show |u| = |d|/(|a|+|b|) by simp [u,abs_div,abs_of_pos hden], div_le_iff₀ hden]
    linarith only [hd,hab]
  let y := base + Pi.single i ((k:ℝ)+sa*u) + Pi.single j (sb*u)
  have hs (l : Fin n) (z : ℝ) : rowEval m (Pi.single l z) = (m l : ℝ)*z := by
    rw [rowEval, Finset.sum_eq_single l]
    · simp
    · intro w _ hw
      simp [Pi.single_eq_of_ne hw]
    · simp
  have hadd (v w : Fin n → ℝ) : rowEval m (v+w) = rowEval m v + rowEval m w := by
    simp [rowEval,mul_add,Finset.sum_add_distrib]
  refine ⟨y,?_ ,?_⟩
  · dsimp only [y]
    rw [hadd,hadd,hs,hs]
    change rowEval m base + a*((k:ℝ)+sa*u) + b*(sb*u) = rowEval m x
    rw [mul_add, ← mul_assoc a sa, ← mul_assoc b sb, hsa,hsb]
    have he : (|a|+|b|)*u = d := by dsimp [u]; field_simp
    dsimp [d,target] at he
    linarith only [he, add_mul (|a|) (|b|) u]
  · intro l
    by_cases hl : l = i
    · subst l
      change (1/4:ℝ) ≤ distInt (1/2 + (Pi.single i ((k:ℝ)+sa*u) : Fin n → ℝ) i + (Pi.single j (sb*u) : Fin n → ℝ) i)
      rw [Pi.single_eq_same, Pi.single_eq_of_ne hne, add_zero,
        show (1/2:ℝ) + ((k:ℝ)+sa*u) = (1/2+sa*u)+(k:ℝ) by ring,
        Cascade.distInt_add_int]
      have hb : |sa*u| ≤ 1/4 := by rwa [abs_mul,has,one_mul]
      exact clear_quarter (by linarith [(abs_le.mp hb).1]) (by linarith [(abs_le.mp hb).2])
    · by_cases hl' : l = j
      · subst l
        change (1/4:ℝ) ≤ distInt (1/2 + (Pi.single i ((k:ℝ)+sa*u) : Fin n → ℝ) j + (Pi.single j (sb*u) : Fin n → ℝ) j)
        rw [Pi.single_eq_of_ne hl, add_zero,Pi.single_eq_same]
        have hb : |sb*u| ≤ 1/4 := by rwa [abs_mul,hbs,one_mul]
        exact clear_quarter (by linarith [(abs_le.mp hb).1]) (by linarith [(abs_le.mp hb).2])
      · change (1/4:ℝ) ≤ distInt (1/2 + (Pi.single i ((k:ℝ)+sa*u) : Fin n → ℝ) l + (Pi.single j (sb*u) : Fin n → ℝ) l)
        rw [Pi.single_eq_of_ne hl, Pi.single_eq_of_ne hl',add_zero,add_zero]
        exact clear_quarter (by norm_num) (by norm_num)

#print axioms rank_one_fibre



/-- Once the complement is clear, motion on a supported direction
can settle the circuit without changing the complement. -/
theorem clear_by_supported_direction {n : ℕ} (V : Submodule ℝ (Fin n → ℝ))
    (S : Finset (Fin n)) {p : Fin n → ℝ} (hp : p ∈ V)
    (hzero : ∀ i ∉ S, p i = 0) (x : Fin n → ℝ) (c : ℝ)
    (hout : ∃ w ∈ V, ∀ i ∉ S, c ≤ distInt (x i+w i))
    (hin : ∀ y : Fin n → ℝ, ∃ t : ℝ, ∀ i ∈ S, c ≤ distInt (y i+t*p i)) :
    ∃ w ∈ V, ∀ i, c ≤ distInt (x i+w i) := by
  obtain ⟨w,hw,hout⟩ := hout
  obtain ⟨t,ht⟩ := hin (fun i => x i+w i)
  refine ⟨w+t • p,V.add_mem hw (V.smul_mem t hp),fun i => ?_⟩
  change c ≤ distInt (x i+(w i+t*p i))
  by_cases hi : i ∈ S
  · rw [← add_assoc]
    exact ht i hi
  · rw [hzero i hi,mul_zero,add_zero]
    exact hout i hi

/-- If the circuit spans the quotient, fix the other coordinates at one
third. They remain clear after either dilation. -/
theorem freeze_complement_and_double {n : ℕ} (V : Submodule ℝ (Fin n → ℝ))
    (S : Finset (Fin n)) {p : Fin n → ℝ} (hp : p ∈ V)
    (hzero : ∀ i ∉ S, p i = 0) {c : ℝ} (hc : c ≤ 1/3)
    (hfree : ∀ y : Fin n → ℝ, ∃ w ∈ V, ∀ i ∉ S, w i = y i)
    (hin : ∀ y : Fin n → ℝ, ∃ q : ℕ, (q = 1 ∨ q = 2) ∧
      ∃ t : ℝ, ∀ i ∈ S, c ≤ distInt ((q:ℝ)*y i+t*p i))
    (x : Fin n → ℝ) :
    ∃ q : ℕ, (q = 1 ∨ q = 2) ∧ ∃ w ∈ V, ∀ i, c ≤ distInt ((q:ℝ)*x i+w i) := by
  obtain ⟨w,hw,hf⟩ := hfree (fun i => 1/3-x i)
  obtain ⟨q,hq,t,ht⟩ := hin (fun i => x i+w i)
  refine ⟨q,hq,(q:ℝ) • w+t • p,V.add_mem (V.smul_mem _ hw) (V.smul_mem _ hp),fun i => ?_⟩
  change c ≤ distInt ((q:ℝ)*x i+((q:ℝ)*w i+t*p i))
  rw [show (q:ℝ)*x i+((q:ℝ)*w i+t*p i) = (q:ℝ)*(x i+w i)+t*p i by ring]
  by_cases hi : i ∈ S
  · exact ht i hi
  · rw [hzero i hi,mul_zero,add_zero,hf i hi,add_sub_cancel]
    apply hc.trans
    rcases hq with rfl | rfl <;> norm_num [distInt,round_eq_iff]

#print axioms clear_by_supported_direction
#print axioms freeze_complement_and_double

end Fresh.FiniteRelations
