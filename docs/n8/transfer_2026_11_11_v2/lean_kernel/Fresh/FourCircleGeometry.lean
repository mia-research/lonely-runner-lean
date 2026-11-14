import Fresh.SmallCircuits

namespace Fresh.FiniteRelations

open Set Metric MeasureTheory
open scoped BigOperators ENNReal

/-- At least one of the first two dilations lies within one third of
an integer. -/
theorem one_or_two_near_integer (x : ℝ) :
    ∃ (q : ℕ) (k : ℤ), (q = 1 ∨ q = 2) ∧ |(q:ℝ)*x-(k:ℝ)| ≤ 1/3 := by
  let r := x-(round x:ℝ)
  have hr : |r| ≤ 1/2 := abs_sub_round x
  by_cases h : |r| ≤ 1/3
  · exact ⟨1,round x,Or.inl rfl,by simpa using h⟩
  have h' := lt_of_not_ge h
  by_cases hn : 0 ≤ r
  · rw [abs_of_nonneg hn] at hr h'
    refine ⟨2,2*round x+1,Or.inr rfl,?_⟩
    push_cast
    apply abs_le.mpr
    dsimp [r] at hr h'
    constructor <;> linarith
  · rw [abs_of_neg (lt_of_not_ge hn)] at hr h'
    refine ⟨2,2*round x-1,Or.inr rfl,?_⟩
    push_cast
    apply abs_le.mpr
    dsimp [r] at hr h'
    constructor <;> linarith

/-- Two unequal positive slopes necessarily overlap in their bad
interiors at one of the two dilations, for any pair of starting phases. -/
theorem unequal_pair_overlap {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b)
    (x y : ℝ) :
    ∃ q : ℕ, (q = 1 ∨ q = 2) ∧ ∃ t : ℝ,
      distInt ((q:ℝ)*x+(a:ℝ)*t) < 1/8 ∧ distInt ((q:ℝ)*y+(b:ℝ)*t) < 1/8 := by
  let g := a.gcd b
  let A := a/g
  let B := b/g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ ha
  have hA : A*g = a := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have hB : B*g = b := Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
  have hAp : 0 < A := by
    by_contra! h
    have h0 : A = 0 := le_antisymm h (Nat.zero_le _)
    rw [h0,zero_mul] at hA
    omega
  have hBp : 0 < B := by
    by_contra! h
    have h0 : B = 0 := le_antisymm h (Nat.zero_le _)
    rw [h0,zero_mul] at hB
    omega
  have hAB : 3 ≤ A+B := by
    have h : A ≠ B := fun h => hne (by rw [←hA,←hB,h])
    omega
  have hco : A.Coprime B := Nat.coprime_div_gcd_div_gcd (by omega)
  have hbez := Nat.gcd_eq_gcd_ab A B
  rw [hco.gcd_eq_one] at hbez
  obtain ⟨q,k,hq,hk⟩ := one_or_two_near_integer ((B:ℝ)*x-(A:ℝ)*y)
  let d := (q:ℝ)*((B:ℝ)*x-(A:ℝ)*y)-(k:ℝ)
  let e := d/((A:ℝ)+(B:ℝ))
  have hsum : (3:ℝ) ≤ (A:ℝ)+(B:ℝ) := by exact_mod_cast hAB
  have he : |e| < 1/8 := by
    have hd : |d| ≤ 1/3 := hk
    rw [show |e| = |d|/((A:ℝ)+(B:ℝ)) by simp [e,abs_div,abs_of_nonneg (show 0 ≤ (A:ℝ)+(B:ℝ) by linarith)]]
    apply (div_lt_iff₀ (by linarith)).2
    linarith
  let i : ℤ := k * Nat.gcdB A B
  let j : ℤ := -k * Nat.gcdA A B
  let s := (e+(i:ℝ)-(q:ℝ)*x)/(A:ℝ)
  have hscaleA : (A:ℝ)*(g:ℝ) = a := by exact_mod_cast hA
  have hscaleB : (B:ℝ)*(g:ℝ) = b := by exact_mod_cast hB
  have hgp : (g:ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hAp' : (A:ℝ) ≠ 0 := by exact_mod_cast hAp.ne'
  have hx : (q:ℝ)*x+(a:ℝ)*(s/(g:ℝ)) = e+(i:ℝ) := by
    rw [← hscaleA]
    dsimp [s]
    field_simp
    ring
  have hy : (q:ℝ)*y+(b:ℝ)*(s/(g:ℝ)) = -e+(j:ℝ) := by
    rw [← hscaleB]
    dsimp [s]
    have hbez' : (B:ℝ)*(i:ℝ)-(A:ℝ)*(j:ℝ) = k := by
      dsimp [i,j]
      push_cast
      have hh : (1:ℝ) = (A:ℝ)*(Nat.gcdA A B:ℝ)+(B:ℝ)*(Nat.gcdB A B:ℝ) := by
        exact_mod_cast hbez
      linear_combination (k:ℝ)*hh.symm
    have hdiv : ((A:ℝ)+(B:ℝ))*e = d := by dsimp [e]; field_simp
    dsimp [d] at hdiv
    apply (mul_right_cancel₀ hAp')
    field_simp
    linear_combination hbez' + hdiv
  refine ⟨q,hq,s/(g:ℝ),?_ ,?_⟩
  · rw [hx,Cascade.distInt_add_int]
    exact (show distInt e ≤ |e| by simpa using Cascade.distInt_le e 0).trans_lt he
  · rw [hy,Cascade.distInt_add_int,Cascade.distInt_neg]
    exact (show distInt e ≤ |e| by simpa using Cascade.distInt_le e 0).trans_lt he

#print axioms unequal_pair_overlap



/-- For four circles with bad arcs of measure one quarter each, a
single interior overlap gives a strictly clear phase. -/
theorem clear_four_of_overlap (p : Fin 4 → ℤ) (hp : ∀ i, p i ≠ 0) (x : Fin 4 → ℝ)
    {i j : Fin 4} (hne : i ≠ j) {t : ℝ}
    (hi : distInt ((p i : ℝ)*t+x i) < 1/8)
    (hj : distInt ((p j : ℝ)*t+x j) < 1/8) :
    ∃ s : ℝ, ∀ l, (1/8:ℝ) < distInt ((p l : ℝ)*s+x l) := by
  classical
  let B (l : Fin 4) := (fun z : UnitAddCircle => p l • z) ⁻¹'
    closedBall (-((x l : ℝ) : UnitAddCircle)) (1/8)
  let U (l : Fin 4) := (fun z : UnitAddCircle => p l • z) ⁻¹'
    ball (-((x l : ℝ) : UnitAddCircle)) (1/8)
  have hdist (l : Fin 4) (s : ℝ) :
      dist (p l • (s:UnitAddCircle)) (-((x l:ℝ):UnitAddCircle)) =
      distInt ((p l:ℝ)*s+x l) := by
    rw [dist_eq_norm,sub_neg_eq_add,← AddCircle.coe_zsmul,← AddCircle.coe_add,
      UnitAddCircle.norm_eq,zsmul_eq_mul]
    rfl
  have hB (l : Fin 4) : volume.real (B l) = 1/4 := by
    have h := (circle_mul_preserving (p l) (hp l)).measure_preimage
      (measurableSet_closedBall.nullMeasurableSet :
        NullMeasurableSet (closedBall (-((x l:ℝ):UnitAddCircle)) (1/8)) volume)
    unfold Measure.real B
    rw [h,AddCircle.volume_closedBall]
    norm_num
  have ho (l : Fin 4) : IsOpen (U l) :=
    isOpen_ball.preimage (continuous_id.const_smul (p l))
  have hp' : 0 < volume.real (B i ∩ B j) := by
    have he : (U i ∩ U j).Nonempty := ⟨(t:UnitAddCircle), by
      constructor
      · change dist (p i • (t:UnitAddCircle)) (-((x i:ℝ):UnitAddCircle)) < 1/8
        rwa [hdist]
      · change dist (p j • (t:UnitAddCircle)) (-((x j:ℝ):UnitAddCircle)) < 1/8
        rwa [hdist]⟩
    have hm : 0 < volume (B i ∩ B j) :=
      ((ho i).inter (ho j)).measure_pos volume he |>.trans_le
        (measure_mono (inter_subset_inter (preimage_mono ball_subset_closedBall)
          (preimage_mono ball_subset_closedBall)))
    exact ENNReal.toReal_pos hm.ne' (measure_ne_top _ _)
  let R := ((Finset.univ : Finset (Fin 4)).erase i).erase j
  have hR : R.card = 2 := by simp [R,Finset.mem_erase,hne.symm]
  have hpair := measureReal_union_add_inter (μ := (volume : Measure UnitAddCircle))
    (s := B i) (t := B j) (measurableSet_closedBall.preimage
      (continuous_id.const_smul (p j)).measurable)
  rw [hB,hB] at hpair
  by_contra! h
  have hcov : (univ : Set UnitAddCircle) ⊆ (B i ∪ B j) ∪ ⋃ l ∈ R, B l := by
    intro z _
    obtain ⟨s,rfl⟩ := QuotientAddGroup.mk_surjective z
    obtain ⟨l,hl⟩ := h s
    have hs : (s:UnitAddCircle) ∈ B l := by
      change dist (p l • (s:UnitAddCircle)) (-((x l:ℝ):UnitAddCircle)) ≤ 1/8
      rwa [hdist]
    by_cases hli : l = i
    · exact Or.inl (Or.inl (hli ▸ hs))
    by_cases hlj : l = j
    · exact Or.inl (Or.inr (hlj ▸ hs))
    exact Or.inr (mem_iUnion₂.mpr ⟨l,by simp [R,hli,hlj],hs⟩)
  have huniv : volume.real (univ : Set UnitAddCircle) = 1 := by
    simp [Measure.real,AddCircle.measure_univ]
  have hwhole := measureReal_mono (μ := (volume : Measure UnitAddCircle)) hcov
  rw [huniv] at hwhole
  have hsum := measureReal_biUnion_finset_le (μ := (volume : Measure UnitAddCircle)) R B
  simp only [hB,Finset.sum_const,hR,nsmul_eq_mul,Nat.cast_ofNat] at hsum
  linarith only [hwhole,measureReal_union_le (μ := (volume : Measure UnitAddCircle))
    (B i ∪ B j) (⋃ l ∈ R, B l),hsum,hpair,hp']

/-- The arbitrary positive, unequal four-slope case needs no numerical
bound on the slopes. -/
theorem four_positive_unequal (p : Fin 4 → ℕ) (hp : ∀ i, 0 < p i)
    {i j : Fin 4} (hne : p i ≠ p j) (x : Fin 4 → ℝ) :
    ∃ q : ℕ, (q = 1 ∨ q = 2) ∧ ∃ s : ℝ,
      ∀ l, (1/8:ℝ) < distInt ((q:ℝ)*x l+(p l:ℝ)*s) := by
  obtain ⟨q,hq,t,hi,hj⟩ := unequal_pair_overlap (hp i) (hp j) hne (x i) (x j)
  obtain ⟨s,hs⟩ := clear_four_of_overlap (fun l => (p l : ℤ))
    (fun l => by change (p l : ℤ) ≠ 0; exact_mod_cast (hp l).ne') (fun l => (q:ℝ)*x l)
    (i := i) (j := j) (fun h => hne (congrArg p h)) (t := t)
    (by simpa only [Int.cast_natCast,add_comm] using hi)
    (by simpa only [Int.cast_natCast,add_comm] using hj)
  exact ⟨q,hq,s,fun l => by simpa only [Int.cast_natCast,add_comm] using hs l⟩

#print axioms four_positive_unequal

end Fresh.FiniteRelations
