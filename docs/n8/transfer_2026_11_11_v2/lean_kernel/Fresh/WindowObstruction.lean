import Fresh.ThreeFast

namespace Fresh.FiniteRelations

open Set Fresh.Harmonic

/-- Simultaneous recurrence on a finite product of unit circles. -/
private theorem simultaneous_small {ι : Type*} [Fintype ι] (y : ι → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ ∀ i, distInt ((m : ℝ) * y i) < ε := by
  let z : ι → UnitAddCircle := fun i => (y i : UnitAddCircle)
  let s : ℕ → (ι → UnitAddCircle) := fun n => n • z
  obtain ⟨a, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq s
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N, hN⟩ := hlim (ε / 2) (by positivity)
  have h1 := hN N le_rfl
  have h2 := hN (N + 1) (Nat.le_succ N)
  have hd : dist (s (φ (N + 1))) (s (φ N)) < ε := by
    calc
      dist (s (φ (N + 1))) (s (φ N)) ≤
          dist (s (φ (N + 1))) a + dist a (s (φ N)) := dist_triangle _ _ _
      _ < ε := by
        simp only [Function.comp_apply] at h1 h2
        rw [dist_comm a]
        linarith
  have hlt : φ N < φ (N+1) := hφ (Nat.lt_succ_self N)
  let m := φ (N + 1) - φ N
  refine ⟨m, by dsimp [m]; omega, fun i => ?_⟩
  have hs : s (φ (N + 1)) - s (φ N) = m • z := by
    exact (sub_nsmul z hlt.le).symm
  have hnorm : ‖m • z‖ < ε := by
    rw [← hs, ← dist_eq_norm]
    exact hd
  have hi := (norm_le_pi_norm (m • z) i).trans_lt hnorm
  have hcast : (m • z) i = (((m : ℝ) * y i : ℝ) : UnitAddCircle) := by
    simp only [Pi.smul_apply, z, ← AddCircle.coe_nsmul, nsmul_eq_mul]
  rw [hcast, UnitAddCircle.norm_eq] at hi
  exact hi

/-- A finite set of times can be blocked by one arbitrarily fast reading. -/
theorem finite_times_blocked (T : Set ℝ) (hT : T.Finite) (C : ℝ) :
    ∃ v : ℝ, C < v ∧ ∀ t ∈ T, distInt (v * t) < 1/8 := by
  classical
  letI := hT.fintype
  obtain ⟨K, hK⟩ := exists_nat_gt (max C (0 : ℝ))
  have hK0 : 0 < (K : ℝ) := (le_max_right _ _).trans_lt hK
  obtain ⟨m, hm, h⟩ := simultaneous_small
    (fun t : T => (K : ℝ) * (t : ℝ)) (show (0 : ℝ) < 1/8 by norm_num)
  have hm' : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  refine ⟨(m : ℝ) * K, ?_, ?_⟩
  · exact ((le_max_left C 0).trans_lt hK).trans_le (le_mul_of_one_le_left hK0.le hm')
  · intro t ht
    simpa only [mul_assoc] using h ⟨t, ht⟩

/-- With positive slow readings, if a bounded time set has no strict
witness then all its weak witnesses belong to a finite set of touch times. -/
theorem weak_times_finite_of_no_strict {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (W : Set ℝ) (M : ℝ) (hM : ∀ t ∈ W, |t| ≤ M)
    (h : ¬ ∃ t ∈ W, ∀ i, (1/8 : ℝ) < distInt (r i*t)) :
    {t ∈ W | ∀ i, (1/8 : ℝ) ≤ distInt (r i*t)}.Finite := by
  classical
  let K (i : Fin n) := ⌈r i * M + 1⌉
  let P (i : Fin n) (s : Bool) : Set ℝ :=
    (fun k : ℤ => ((k : ℝ) + (if s then 1/8 else -1/8)) / r i) '' Icc (-K i) (K i)
  have hf (i : Fin n) (s : Bool) : (P i s).Finite := (finite_Icc _ _).image _
  apply (Set.finite_iUnion fun i : Fin n => (hf i true).union (hf i false)).subset
  intro t ht
  have htW := ht.1
  have hall := ht.2
  have hn : ¬ ∀ i, (1/8 : ℝ) < distInt (r i*t) := fun he => h ⟨t, htW, he⟩
  push Not at hn
  obtain ⟨i, hi⟩ := hn
  have he : distInt (r i*t) = 1/8 := le_antisymm hi (hall i)
  let k : ℤ := round (r i*t)
  have hk : |(k : ℝ)| ≤ r i * M + 1 := by
    have h1 : |(k : ℝ) - r i*t| = 1/8 := by rw [abs_sub_comm]; exact he
    have h2 : |r i*t| ≤ r i * M := by
      rw [abs_mul, abs_of_pos (hr i)]
      exact mul_le_mul_of_nonneg_left (hM t htW) (hr i).le
    calc
      |(k : ℝ)| ≤ |(k : ℝ) - r i*t| + |r i*t| := by
        convert abs_add_le ((k : ℝ)-r i*t) (r i*t) using 2
        ring
      _ ≤ _ := by linarith
  have hk' : k ∈ Icc (-K i) (K i) := by
    have hceil := Int.le_ceil (r i*M+1)
    have hbound := abs_le.mp (hk.trans hceil)
    exact ⟨by exact_mod_cast hbound.1, by exact_mod_cast hbound.2⟩
  have hcases : r i*t-(k : ℝ) = 1/8 ∨ r i*t-(k : ℝ) = -1/8 := by
    change |r i*t-(k : ℝ)| = 1/8 at he
    simpa only [neg_div] using
      abs_eq_abs.mp (he.trans (abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/8)).symm)
  refine mem_iUnion.mpr ⟨i, ?_⟩
  rcases hcases with hpos | hneg
  · exact Or.inl ⟨k, hk', by
      simp only [if_true]
      apply (div_eq_iff (hr i).ne').mpr
      linarith⟩
  · exact Or.inr ⟨k, hk', by
      simp only [Bool.false_eq_true, if_false]
      apply (div_eq_iff (hr i).ne').mpr
      linarith⟩

/-- Absence of a strict slow witness is an obstruction to a uniform
one-fast or two-fast window theorem for that slow prefix. -/
theorem arbitrarily_fast_window_failure {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i)
    (h : ¬ ∃ t, InWindows t ∧ ∀ i, (1/8 : ℝ) < distInt (r i*t)) (C : ℝ) :
    ∃ v : ℝ, C < v ∧ ∀ t, InWindows t →
      (∀ i, (1/8 : ℝ) ≤ distInt (r i*t)) → distInt (v*t) < 1/8 := by
  let W := {t | InWindows t}
  have hM : ∀ t ∈ W, |t| ≤ 2 := by
    intro t ht
    change InWindows t at ht
    rcases ht with ⟨hl, hh⟩ | ⟨hl, hh⟩ <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hf := weak_times_finite_of_no_strict r hr W 2 hM h
  obtain ⟨v, hv, hV⟩ := finite_times_blocked _ hf C
  exact ⟨v, hv, fun t ht hc => hV t ⟨ht, hc⟩⟩

/-- For a fixed slow prefix containing the pinned reading, a strict
witness is equivalent to admitting every sufficiently fast block of
one, two or three readings in the two cascade windows. -/
theorem strict_window_iff_fast_append {n k : ℕ} (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (hpin : ∃ i, r i = 1) (hk₀ : 0 < k) (hk : k ≤ 3) :
    (∃ t, InWindows t ∧ ∀ i, (1/8 : ℝ) < distInt (r i*t)) ↔
    ∃ C : ℝ, ∀ v : Fin k → ℝ, (∀ j, C < v j) →
      ∃ t, InWindows t ∧ (∀ i, (1/8 : ℝ) ≤ distInt (r i*t)) ∧
        ∀ j, (1/8 : ℝ) ≤ distInt (v j*t) := by
  constructor
  · rintro ⟨t, ht, hclear⟩
    obtain ⟨i, hi⟩ := hpin
    have hp := hclear i
    rw [hi, one_mul] at hp
    let U : Set ℝ := Ioo (1/8) (7/8) ∪ Ioo (9/8) (15/8)
    have h₀ : distInt (1/8 : ℝ) = 1/8 := by
      simpa using Fresh.Cascade.distInt_eighth_add_int 0
    have h₁ : distInt (7/8 : ℝ) = 1/8 := by
      rw [show (7/8 : ℝ) = -(1/8 : ℝ) + ((1:ℤ):ℝ) by norm_num,
        Fresh.Cascade.distInt_add_int, Fresh.Cascade.distInt_neg, h₀]
    have h₂ : distInt (9/8 : ℝ) = 1/8 := by
      convert Fresh.Cascade.distInt_eighth_add_int 1 using 2 <;> norm_num
    have h₃ : distInt (15/8 : ℝ) = 1/8 := by
      rw [show (15/8 : ℝ) = (7/8 : ℝ) + ((1:ℤ):ℝ) by norm_num,
        Fresh.Cascade.distInt_add_int, h₁]
    have htU : t ∈ U := by
      rcases ht with ⟨hl,hu⟩ | ⟨hl,hu⟩
      · exact Or.inl ⟨hl.lt_of_ne (fun he => hp.not_ge (he ▸ h₀.le)),
          hu.lt_of_ne (fun he => hp.not_ge (he ▸ h₁.le))⟩
      · exact Or.inr ⟨hl.lt_of_ne (fun he => hp.not_ge (he ▸ h₂.le)),
          hu.lt_of_ne (fun he => hp.not_ge (he ▸ h₃.le))⟩
    have hdist : Continuous distInt := by
      have hh := (AddCircle.continuous_mk' (1:ℝ)).norm
      convert hh using 1
      funext x
      exact UnitAddCircle.norm_eq.symm
    let G : Set ℝ := U ∩ ⋂ i : Fin n, {s | (1/8:ℝ) < distInt (r i*s)}
    have hG : IsOpen G := (isOpen_Ioo.union isOpen_Ioo).inter
      (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
        (hdist.comp (by fun_prop)))
    have htG : t ∈ G := ⟨htU, mem_iInter.mpr hclear⟩
    obtain ⟨δ,hδ,hsub⟩ := Metric.isOpen_iff.mp hG t htG
    refine ⟨3/(2*δ), fun v hv => ?_⟩
    obtain ⟨s,hs,hv'⟩ := at_most_three_fast_on_interval hk v (show 0 < 2*δ by positivity)
      (u := t-δ) (v := t+δ) (by linarith) hv
    have hsG := hsub (show s ∈ Metric.ball t δ by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hs.1],by linarith [hs.2]⟩)
    have hsW : InWindows s := by
      rcases hsG.1 with hs | hs
      · exact Or.inl ⟨hs.1.le,hs.2.le⟩
      · exact Or.inr ⟨hs.1.le,hs.2.le⟩
    exact ⟨s,hsW,fun i => (mem_iInter.mp hsG.2 i).le,fun j => (hv' j).le⟩
  · rintro ⟨C,hC⟩
    by_contra h
    obtain ⟨v,hv,hbad⟩ := arbitrarily_fast_window_failure r hr h C
    let w (j : Fin k) := v + (j.val:ℝ)
    obtain ⟨t,ht,hr',hw⟩ := hC w (fun j => hv.trans_le (le_add_of_nonneg_right (by positivity)))
    have hz := hw ⟨0,hk₀⟩
    change (1/8:ℝ) ≤ distInt ((v+((0:ℕ):ℝ))*t) at hz
    simp only [Nat.cast_zero,add_zero] at hz
    exact (hbad t ht hr').not_ge hz

#print axioms arbitrarily_fast_window_failure
#print axioms strict_window_iff_fast_append

end Fresh.FiniteRelations
