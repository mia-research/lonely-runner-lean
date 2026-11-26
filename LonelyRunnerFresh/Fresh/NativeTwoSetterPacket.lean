import Fresh.NativeOrderedReturnLevels

/-! Retention through two actual selected openings. These are local boundary
identities and disparity faces, not a budget on a cascade. Newly clear readers
retain independent duties; the old packet is discharged only when proved. -/
namespace Fresh.NativeTwoSetterPacket
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnHandoffArrangement Fresh.NativeReturnClosingOrder
  Fresh.NativeCapturedPartnerJoin Fresh.NativeCohortReturns Fresh.NativeCohortOutsiderRelay
  Fresh.NativeReturnLevelClearance Fresh.NativeOrderedReturnLevels

theorem two_deficits_upper (d e s x y : ℝ) (hd : 0 < d) (he : 0 < e) (hs : 0 ≤ s)
    (hx : d*x < 1/4) (hy : e*y < 1/4) (hf : s*(d+e) ≤ 3*d*e) : s*(x+y) ≤ 3/4 := by
  have hdx := mul_le_mul_of_nonneg_left hx.le (mul_nonneg hs he.le)
  have hey := mul_le_mul_of_nonneg_left hy.le (mul_nonneg hs hd.le)
  have hp : (d*e)*(s*(x+y)-3/4) ≤ 0 := by nlinarith only [hdx,hey,hf]
  by_contra hn
  have hpos := mul_pos (mul_pos hd he) (sub_pos.mpr (lt_of_not_ge hn))
  exact not_lt_of_ge hp hpos

theorem two_setter_zero {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (U : ℝ) (g h i : Fin 8)
    (hg : g≠k) (hh : h≠k) (hi : i≠k) (hwg : InWay (reading v k g) U)
    (hm1 : IsMove (disparitySet v k) U (handoffOpening v k U g))
    (hwh : InWay (reading v k h) (handoffOpening v k U g))
    (hm2 : IsMove (disparitySet v k) (handoffOpening v k U g) (handoffOpening v k (handoffOpening v k U g) h))
    (hwi : InWay (reading v k i) U)
    (hf : reading v k i*(reading v k g+reading v k h) ≤ 3*reading v k g*reading v k h) :
    advance (reading v k i) U (handoffOpening v k (handoffOpening v k U g) h)=0 := by
  have hd : 0 < reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  have he : 0 < reading v k h := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨h,hh,rfl⟩)
  have hs : 0 < reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  have hcg := capture_at_label (reading v k g) U hwg
  have hch := capture_at_label (reading v k h) (handoffOpening v k U g) hwh
  have hx := Fresh.NativeOpeningRetention.capture_advance _ U _ _ hd (handoff_identity hv k g U hg) hcg.1 hcg.2
  have hy := Fresh.NativeOpeningRetention.capture_advance _ (handoffOpening v k U g) _ _ he
    (handoff_identity hv k h (handoffOpening v k U g) hh) hch.1 hch.2
  have hu := two_deficits_upper _ _ (reading v k i) _ _ hd he hs.le hx.2 hy.2 hf
  have hentry := (capture_at_label (reading v k i) U hwi).2
  have hUV := le_of_isMove (disparitySet_pos hv k) hm1
  have hVW := le_of_isMove (disparitySet_pos hv k) hm2
  apply (zero_iff_original_upper _ _ _ hs.le (le_trans hUV hVW)).2
  change reading v k i*handoffOpening v k (handoffOpening v k U g) h  ≤  (label (reading v k i*U) : ℝ)+7/8
  nlinarith only [hu,hentry]

theorem two_setter_zero_split {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (U : ℝ) (g h i : Fin 8)
    (hg : g≠k) (hh : h≠k) (hi : i≠k) (hwg : InWay (reading v k g) U)
    (hm1 : IsMove (disparitySet v k) U (handoffOpening v k U g))
    (hwh : InWay (reading v k h) (handoffOpening v k U g))
    (hm2 : IsMove (disparitySet v k) (handoffOpening v k U g) (handoffOpening v k (handoffOpening v k U g) h))
    (hwi : InWay (reading v k i) U)
    (hf : reading v k i*(reading v k g+reading v k h) ≤ 3*reading v k g*reading v k h) :
    advance (reading v k i) U (handoffOpening v k U g)=0 ∧
      advance (reading v k i) (handoffOpening v k U g) (handoffOpening v k (handoffOpening v k U g) h)=0 := by
  have hz := two_setter_zero hv k U g h i hg hh hi hwg hm1 hwh hm2 hwi hf
  have ha := advance_add (reading v k i) U (handoffOpening v k U g) _ (abs_nonneg _)
    (le_of_isMove (disparitySet_pos hv k) hm1) (le_of_isMove (disparitySet_pos hv k) hm2)
  omega

theorem entry_speed_face {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (U : ℝ) (g h : Fin 8)
    (hg : g≠k) (hh : h≠k) (hwg : InWay (reading v k g) U)
    (hm1 : IsMove (disparitySet v k) U (handoffOpening v k U g))
    (hwh : InWay (reading v k h) (handoffOpening v k U g)) :
    4*reading v k g*((advance (reading v k h) U (handoffOpening v k U g) : ℝ)-1/8-
      (reading v k h*U-(label (reading v k h*U) : ℝ))) < reading v k h := by
  have hd : 0 < reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  have he : 0 < reading v k h := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨h,hh,rfl⟩)
  have hcg := capture_at_label (reading v k g) U hwg
  have hx := (Fresh.NativeOpeningRetention.capture_advance _ U _ _ hd (handoff_identity hv k g U hg) hcg.1 hcg.2).2
  have hid := advance_identity (reading v k h) U (handoffOpening v k U g) he.le
    (le_of_isMove (disparitySet_pos hv k) hm1)
  have hidR : (label (reading v k h*handoffOpening v k U g) : ℝ)=(label (reading v k h*U) : ℝ)+
      (advance (reading v k h) U (handoffOpening v k U g) : ℝ) := by exact_mod_cast hid
  have hlo := (capture_at_label (reading v k h) (handoffOpening v k U g) hwh).1
  rw [hidR] at hlo
  have h1 := mul_lt_mul_of_pos_left hlo hd
  have h2 := mul_lt_mul_of_pos_left hx he
  nlinarith only [h1,h2]

theorem old_setter_return_late {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (U : ℝ) (g h : Fin 8)
    (hg : g≠k) (hh : h≠k) (hwg : InWay (reading v k g) U)
    (hm1 : IsMove (disparitySet v k) U (handoffOpening v k U g))
    (hwh : InWay (reading v k h) (handoffOpening v k U g))
    (hm2 : IsMove (disparitySet v k) (handoffOpening v k U g) (handoffOpening v k (handoffOpening v k U g) h))
    (ha : 0 < advance (reading v k g) (handoffOpening v k U g) (handoffOpening v k (handoffOpening v k U g) h)) :
    3*reading v k h < reading v k g ∧ advance (reading v k h) U (handoffOpening v k U g)=1 ∧
      (label (reading v k h*U) : ℝ)+19/24 < reading v k h*U := by
  have hd : 0 < reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  have he : 0 < reading v k h := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨h,hh,rfl⟩)
  have hcg := capture_at_label (reading v k g) U hwg
  have hch := capture_at_label (reading v k h) (handoffOpening v k U g) hwh
  have hx := Fresh.NativeOpeningRetention.capture_advance _ U _ _ hd (handoff_identity hv k g U hg) hcg.1 hcg.2
  have hy := Fresh.NativeOpeningRetention.capture_advance _ (handoffOpening v k U g) _ _ he
    (handoff_identity hv k h (handoffOpening v k U g) hh) hch.1 hch.2
  have hUV := le_of_isMove (disparitySet_pos hv k) hm1
  have hVW := le_of_isMove (disparitySet_pos hv k) hm2
  have hz := zero_from_opening_iff (reading v k g) (handoffOpening v k U g)
    (handoffOpening v k (handoffOpening v k U g) h) (label (reading v k g*U)) hd.le hVW
    (handoff_identity hv k g U hg)

  have hlarge : 3 < 4*reading v k g*(handoffOpening v k (handoffOpening v k U g) h-handoffOpening v k U g) := by
    apply lt_of_not_ge
    intro hhzero
    have hzero := hz.2 hhzero
    omega
  have hslow : 3*reading v k h < reading v k g := by
    by_contra hn
    have hhprod := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hy.1.le
    nlinarith only [hhprod,hy.2,hlarge]
  have hshort := mul_le_mul_of_nonneg_right hslow.le hx.1.le
  have hdelta : reading v k h*(handoffOpening v k U g-U) < 1/12 := by nlinarith only [hshort,hx.2]
  have hpos := captured_implies_return hv k U _ hm1 h hh hwh
  change 0 < advance (reading v k h) U (handoffOpening v k U g) at hpos
  have hid := advance_identity (reading v k h) U (handoffOpening v k U g) he.le hUV
  have hidR : (label (reading v k h*handoffOpening v k U g) : ℝ)=(label (reading v k h*U) : ℝ)+
      (advance (reading v k h) U (handoffOpening v k U g) : ℝ) := by exact_mod_cast hid
  have hlo := hch.1
  rw [hidR] at hlo
  have hu := ((entry_interval (reading v k h) U _).1 (label_entry (reading v k h) U)).2
  have hone : advance (reading v k h) U (handoffOpening v k U g)=1 := by
    by_contra hn
    have htwo : 2 ≤ advance (reading v k h) U (handoffOpening v k U g) := by omega
    have htwoR : (2 : ℝ) ≤ (advance (reading v k h) U (handoffOpening v k U g) : ℝ) := by exact_mod_cast htwo
    nlinarith only [hlo,hu,hdelta,htwoR]
  rw [hone] at hlo
  norm_num only [Nat.cast_one] at hlo
  exact ⟨hslow,hone,by nlinarith only [hlo,hdelta]⟩

theorem entry_phase_retains_old_setter {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (U : ℝ) (g h : Fin 8)
    (hg : g≠k) (hh : h≠k) (hwg : InWay (reading v k g) U)
    (hm1 : IsMove (disparitySet v k) U (handoffOpening v k U g))
    (hwh : InWay (reading v k h) (handoffOpening v k U g))
    (hm2 : IsMove (disparitySet v k) (handoffOpening v k U g) (handoffOpening v k (handoffOpening v k U g) h))
    (hearly : reading v k h*U ≤ (label (reading v k h*U) : ℝ)+19/24) :
    advance (reading v k g) (handoffOpening v k U g) (handoffOpening v k (handoffOpening v k U g) h)=0 := by
  by_contra hn
  have ha : 0 < advance (reading v k g) (handoffOpening v k U g) (handoffOpening v k (handoffOpening v k U g) h) := by omega
  exact not_lt_of_ge hearly (old_setter_return_late hv k U g h hg hh hwg hm1 hwh hm2 ha).2.2

theorem high_packet_compact {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P U : ℝ) (i g : Fin 8)
    (hprior : IsMove (disparitySet v k) P U) (hwi : InWay (reading v k i) U) (hwg : InWay (reading v k g) U)
    (hle : advance (reading v k i) P U ≤ advance (reading v k g) P U) (htwo : 2 ≤ advance (reading v k g) P U) :
    4*reading v k i < 9*reading v k g := by
  have hPU := le_of_isMove (disparitySet_pos hv k) hprior
  have hi := (displacement_bounds (reading v k i) P U (abs_nonneg _) hPU hwi).2
  have hg := (displacement_bounds (reading v k g) P U (abs_nonneg _) hPU hwg).1
  have hmR : (advance (reading v k i) P U : ℝ) ≤ (advance (reading v k g) P U : ℝ) := by exact_mod_cast hle
  have htwoR : (2 : ℝ) ≤ (advance (reading v k g) P U : ℝ) := by exact_mod_cast htwo
  by_contra hn
  have hx := mul_le_mul_of_nonneg_right (le_of_not_gt hn) (sub_nonneg.mpr hPU)
  nlinarith only [hi,hg,hmR,htwoR,hx]

theorem new_high_speed {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (U : ℝ) (g h : Fin 8)
    (hg : g≠k) (hh : h≠k) (hwg : InWay (reading v k g) U)
    (hm1 : IsMove (disparitySet v k) U (handoffOpening v k U g))
    (hwh : InWay (reading v k h) (handoffOpening v k U g))
    (htwo : 2 ≤ advance (reading v k h) U (handoffOpening v k U g)) : 4*reading v k g < reading v k h := by
  have hf := entry_speed_face hv k U g h hg hh hwg hm1 hwh
  have hu := ((entry_interval (reading v k h) U _).1 (label_entry (reading v k h) U)).2
  have hmR : (2 : ℝ) ≤ (advance (reading v k h) U (handoffOpening v k U g) : ℝ) := by exact_mod_cast htwo
  have hres : 1 ≤ (advance (reading v k h) U (handoffOpening v k U g) : ℝ)-1/8-
      (reading v k h*U-(label (reading v k h*U) : ℝ)) := by linarith only [hu,hmR]
  have hmul := mul_le_mul_of_nonneg_left hres (show 0 ≤ 4*reading v k g from mul_nonneg (by norm_num) (abs_nonneg _))
  nlinarith only [hf,hmul]

theorem double_high_old_zero {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P U : ℝ) (g h i : Fin 8)
    (hprior : IsMove (disparitySet v k) P U) (hg : g≠k) (hh : h≠k) (hi : i≠k)
    (hwg : InWay (reading v k g) U) (hwi : InWay (reading v k i) U)
    (hm1 : IsMove (disparitySet v k) U (handoffOpening v k U g))
    (hwh : InWay (reading v k h) (handoffOpening v k U g))
    (hm2 : IsMove (disparitySet v k) (handoffOpening v k U g) (handoffOpening v k (handoffOpening v k U g) h))
    (hle : advance (reading v k i) P U ≤ advance (reading v k g) P U)
    (hg2 : 2 ≤ advance (reading v k g) P U) (hh2 : 2 ≤ advance (reading v k h) U (handoffOpening v k U g)) :
    advance (reading v k i) U (handoffOpening v k (handoffOpening v k U g) h)=0 := by
  have hr := high_packet_compact hv k P U i g hprior hwi hwg hle hg2
  have hs := new_high_speed hv k U g h hg hh hwg hm1 hwh hh2
  have hmul := mul_le_mul_of_nonneg_right hr.le (show 0 ≤ reading v k g+reading v k h from add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hsg : 3*reading v k g ≤ reading v k h := by linarith only [hs,show 0 ≤ reading v k g from abs_nonneg _]
  have hscale := mul_le_mul_of_nonneg_left hsg (show 0 ≤ 3*reading v k g from mul_nonneg (by norm_num) (abs_nonneg _))
  apply two_setter_zero hv k U g h i hg hh hi hwg hm1 hwh hm2 hwi
  nlinarith only [hmul,hscale]

-- STANDING: DEFINITION
noncomputable def TwoSetterPartnerClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (U : ℝ) (g h : Fin 8), 0 < U ∧ g≠k ∧ h≠k ∧ InWay (reading v k g) U ∧
    IsMove (disparitySet v k) U (handoffOpening v k U g) ∧ InWay (reading v k h) (handoffOpening v k U g) ∧
    IsMove (disparitySet v k) (handoffOpening v k U g) (handoffOpening v k (handoffOpening v k U g) h) ∧
    (∀ i : Fin 8, i≠k → InWay (reading v k i) U → reading v k i*(reading v k g+reading v k h) ≤ 3*reading v k g*reading v k h) ∧
    (∀ i : Fin 8, i≠k → ¬InWay (reading v k i) U →
      (InWay (reading v k i) (handoffOpening v k U g) → reading v k i ≤ 3*reading v k h ∨ handoffOpening v k (handoffOpening v k U g) i=handoffOpening v k (handoffOpening v k U g) h) ∧
      (¬InWay (reading v k i) (handoffOpening v k U g) → handoffOpening v k (handoffOpening v k U g) h ≤ closing (reading v k i) (handoffOpening v k U g)))

theorem twoSetter_into_partner {v : Fin 8 → ℝ} {k : Fin 8} (h : TwoSetterPartnerClass v k) : PartnerClass v k := by
  obtain ⟨hv,U,g,j,hU,hg,hj,hwg,hm1,hwj,hm2,hfaces,houtside⟩ := h
  have hUV := le_of_isMove (disparitySet_pos hv k) hm1
  have hVW := le_of_isMove (disparitySet_pos hv k) hm2
  refine ⟨hv,handoffOpening v k U g,j,lt_of_lt_of_le hU hUV,hj,hwj,hm2,?_⟩
  intro i hi
  by_cases hwi : InWay (reading v k i) U
  · have hz := two_setter_zero_split hv k U g j i hg hj hi hwg hm1 hwj hm2 hwi (hfaces i hi hwi)
    have hclear := not_lt.mpr (nonreturning_clear hv k U _ hm1 i hi hz.1)
    refine ⟨fun hn=>(hclear hn).elim,fun _=>?_⟩
    have hp : 0 < reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
    have hu := (zero_iff_original_upper _ _ _ hp.le hVW).1 hz.2
    apply (le_div_iff₀ hp).2
    simpa only [closing,mul_comm] using hu
  · exact houtside i hi hwi

theorem twoSetter_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : TwoSetterPartnerClass v k) : Isolation v k :=
  partner_isolation (twoSetter_into_partner h)

-- STANDING: DEFINITION
noncomputable def DoubleHighRecoveryClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (P U : ℝ) (g h : Fin 8), 0 < P ∧ IsMove (disparitySet v k) P U ∧ g≠k ∧ h≠k ∧
    InWay (reading v k g) U ∧ IsMove (disparitySet v k) U (handoffOpening v k U g) ∧
    2 ≤ advance (reading v k g) P U ∧
    (∀ i : Fin 8, i≠k → InWay (reading v k i) U → advance (reading v k i) P U ≤ advance (reading v k g) P U) ∧
    InWay (reading v k h) (handoffOpening v k U g) ∧
    IsMove (disparitySet v k) (handoffOpening v k U g) (handoffOpening v k (handoffOpening v k U g) h) ∧
    2 ≤ advance (reading v k h) U (handoffOpening v k U g) ∧
    (∀ i : Fin 8, i≠k → ¬InWay (reading v k i) U →
      0 < advance (reading v k i) (handoffOpening v k U g) (handoffOpening v k (handoffOpening v k U g) h) →
      (¬InWay (reading v k i) (handoffOpening v k U g) ∨
        advance (reading v k h) U (handoffOpening v k U g) < advance (reading v k i) U (handoffOpening v k U g)) →
      reading v k h*((label (reading v k i*handoffOpening v k (handoffOpening v k U g) h) : ℝ)+1/8) ≤ 
        reading v k i*((label (reading v k h*handoffOpening v k U g) : ℝ)+1/8))

theorem doubleHigh_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : DoubleHighRecoveryClass v k) :
    Fresh.NativeCanonicalReturn.CanonicalReturnClass v k := by
  obtain ⟨hv,P,U,g,j,hP,hprior,hg,hj,hwg,hm1,hg2,hmax,hwj,hm2,hj2,hpassed⟩ := h
  have hPU := le_of_isMove (disparitySet_pos hv k) hprior
  have hUV := le_of_isMove (disparitySet_pos hv k) hm1
  have hVW := le_of_isMove (disparitySet_pos hv k) hm2
  have hc := capture_at_label (reading v k j) (handoffOpening v k U g) hwj
  refine ⟨hv,j,handoffOpening v k U g,label (reading v k j*handoffOpening v k U g),hj,
    lt_of_lt_of_le hP (le_trans hPU hUV),hc.1,hc.2,hm2,?_⟩
  intro i hi ha
  change 0 < advance (reading v k i) (handoffOpening v k U g) (handoffOpening v k (handoffOpening v k U g) j) at ha
  by_cases hold : InWay (reading v k i) U
  · have hz := double_high_old_zero hv k P U g j i hprior hg hj hi hwg hold hm1 hwj hm2 (hmax i hi hold) hg2 hj2
    have hadd := advance_add (reading v k i) U (handoffOpening v k U g) _ (abs_nonneg _) hUV hVW
    omega
  · apply hpassed i hi hold ha
    by_cases hnow : InWay (reading v k i) (handoffOpening v k U g)
    · apply Or.inr
      apply lt_of_not_ge
      intro hle
      have hz := ordered_guard_zero hv k U (handoffOpening v k U g) i j hm1 hi hj hnow hwj hle (Or.inl hj2) hm2
      omega
    · exact Or.inl hnow

theorem doubleHigh_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : DoubleHighRecoveryClass v k) : Isolation v k :=
  Fresh.NativeCanonicalReturn.canonical_isolation (doubleHigh_into_canonical h)

theorem cohort_phase_retains {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (U : ℝ) (g h : Fin 8)
    (hco : Cohort v k U g) (hh : h≠k) (hwh : InWay (reading v k h) (handoffOpening v k U g))
    (hm2 : IsMove (disparitySet v k) (handoffOpening v k U g) (handoffOpening v k (handoffOpening v k U g) h))
    (hearly : reading v k h*U≤(label (reading v k h*U) : ℝ)+19/24) :
    ∀ i : Fin 8, i≠k → InWay (reading v k i) U →
      advance (reading v k i) (handoffOpening v k U g) (handoffOpening v k (handoffOpening v k U g) h)=0 := by
  have hm1 := cohort_move hv k U g hco.1 hco.2.1 hco.2.2
  intro i hi hwi
  have htie := hco.2.2 i hi hwi
  have hmi : IsMove (disparitySet v k) U (handoffOpening v k U i) := by rw [htie]; exact hm1
  have hwi2 : InWay (reading v k h) (handoffOpening v k U i) := by rw [htie]; exact hwh
  have hmi2 : IsMove (disparitySet v k) (handoffOpening v k U i) (handoffOpening v k (handoffOpening v k U i) h) := by rw [htie]; exact hm2
  have hz := entry_phase_retains_old_setter hv k U i h hi hh hwi hmi hwi2 hmi2 hearly
  simpa only [htie] using hz

-- STANDING: DEFINITION
noncomputable def CohortPhaseRecoveryClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (U : ℝ) (g h : Fin 8), 0<U ∧ Cohort v k U g ∧ h≠k ∧
    InWay (reading v k h) (handoffOpening v k U g) ∧
    IsMove (disparitySet v k) (handoffOpening v k U g) (handoffOpening v k (handoffOpening v k U g) h) ∧
    reading v k h*U≤(label (reading v k h*U) : ℝ)+19/24 ∧
    (∀ i : Fin 8, i≠k → ¬InWay (reading v k i) U →
      0<advance (reading v k i) (handoffOpening v k U g) (handoffOpening v k (handoffOpening v k U g) h) →
      reading v k h*((label (reading v k i*handoffOpening v k (handoffOpening v k U g) h) : ℝ)+1/8)≤
        reading v k i*((label (reading v k h*handoffOpening v k U g) : ℝ)+1/8))

theorem cohortPhase_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : CohortPhaseRecoveryClass v k) :
    Fresh.NativeCanonicalReturn.CanonicalReturnClass v k := by
  obtain ⟨hv,U,g,j,hU,hco,hj,hwj,hm2,hearly,hpassed⟩ := h
  have hm1 := cohort_move hv k U g hco.1 hco.2.1 hco.2.2
  have hUV := le_of_isMove (disparitySet_pos hv k) hm1
  have hc := capture_at_label (reading v k j) (handoffOpening v k U g) hwj
  refine ⟨hv,j,handoffOpening v k U g,label (reading v k j*handoffOpening v k U g),hj,
    lt_of_lt_of_le hU hUV,hc.1,hc.2,hm2,?_⟩
  intro i hi ha
  change 0<advance (reading v k i) (handoffOpening v k U g) (handoffOpening v k (handoffOpening v k U g) j) at ha
  by_cases hold : InWay (reading v k i) U
  · have hz := cohort_phase_retains hv k U g j hco hj hwj hm2 hearly i hi hold
    omega
  · exact hpassed i hi hold ha

theorem cohortPhase_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : CohortPhaseRecoveryClass v k) : Isolation v k :=
  Fresh.NativeCanonicalReturn.canonical_isolation (cohortPhase_into_canonical h)

#print axioms cohort_phase_retains
#print axioms cohortPhase_into_canonical
#print axioms cohortPhase_isolation

noncomputable def twoExcess (d e s U V : ℝ) : ℝ :=
  s*(e*((label (d*U) : ℝ)+1/8-d*U)+d*((label (e*V) : ℝ)+1/8-e*V))-
    d*e*((label (s*U) : ℝ)+7/8-s*U)

theorem two_excess_identity (d e s U V W : ℝ)
    (hd : d*V=(label (d*U) : ℝ)+1/8) (he : e*W=(label (e*V) : ℝ)+1/8) :
    twoExcess d e s U V=d*e*(s*W-((label (s*U) : ℝ)+7/8)) := by
  have h1 : (label (d*U) : ℝ)+1/8-d*U=d*(V-U) := by nlinarith only [hd]
  have h2 : (label (e*V) : ℝ)+1/8-e*V=e*(W-V) := by nlinarith only [he]
  dsimp [twoExcess]
  rw [h1,h2]
  ring

theorem two_excess_zero_iff (d e s U V W : ℝ) (hd : 0<d) (he : 0<e) (hs : 0 ≤ s) (hUW : U≤W)
    (ho : d*V=(label (d*U) : ℝ)+1/8) (hp : e*W=(label (e*V) : ℝ)+1/8) :
    advance s U W=0 ↔ twoExcess d e s U V≤0 := by
  rw [zero_iff_original_upper s U W hs hUW,two_excess_identity d e s U V W ho hp]
  have hde := mul_pos hd he
  constructor
  · intro hh
    exact mul_nonpos_of_nonneg_of_nonpos hde.le (sub_nonpos.mpr hh)
  · intro hh
    by_contra hn
    exact not_lt_of_ge hh (mul_pos hde (sub_pos.mpr (lt_of_not_ge hn)))

theorem two_excess_capture_iff (d e s U V W : ℝ) (hd : 0<d) (he : 0<e) (hs : 0 ≤ s) (hUW : U≤W)
    (ho : d*V=(label (d*U) : ℝ)+1/8) (hp : e*W=(label (e*V) : ℝ)+1/8) :
    InWay s W ↔ twoExcess d e s U V<d*e*((advance s U W : ℝ)-3/4) := by
  have hid := advance_identity s U W hs hUW
  have hidR : (label (s*W) : ℝ)=(label (s*U) : ℝ)+(advance s U W : ℝ) := by exact_mod_cast hid
  rw [inWay_iff_lower_not_passed,hidR,two_excess_identity d e s U V W ho hp]
  have hde := mul_pos hd he
  constructor <;> intro hh <;> nlinarith only [hh,hde]

#print axioms two_excess_identity
#print axioms two_excess_zero_iff
#print axioms two_excess_capture_iff

#print axioms two_deficits_upper
#print axioms two_setter_zero
#print axioms two_setter_zero_split
#print axioms entry_speed_face
#print axioms old_setter_return_late
#print axioms entry_phase_retains_old_setter
#print axioms high_packet_compact
#print axioms new_high_speed
#print axioms double_high_old_zero
#print axioms twoSetter_into_partner
#print axioms twoSetter_isolation
#print axioms doubleHigh_into_canonical
#print axioms doubleHigh_isolation
end Fresh.NativeTwoSetterPacket
