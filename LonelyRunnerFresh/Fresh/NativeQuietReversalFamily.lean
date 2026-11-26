import Fresh.NativeOpeningLabelReversal
import Fresh.NativeOpeningReversalArrangement
import Fresh.ProvedTypesScale

/-! A parameterized reversal family with independent unbounded labels and
return advances, a whole closed partner-deviation interval, and independently
varying quiet outsiders. Their clear windows are derived from the arrangement
parameters, not assumed. Local endpoint inequalities are not history budgets. -/
namespace Fresh.NativeQuietReversalFamily
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels
  Fresh.NativeReturnHandoff Fresh.NativeReturnClosingOrder Fresh.NativeReturnSurvivors
  Fresh.NativeOpeningReversal Fresh.NativeOpeningReversalArrangement
  Fresh.NativeOneReaderDeformation Fresh.FastestCaptureRetention
  Fresh.NativeFixedPrefixArrangement

-- STANDING: DEFINITION
noncomputable def anchor (N : ℤ) : ℝ := (N : ℝ)+1/8
-- STANDING: DEFINITION
noncomputable def partner (M A N : ℤ) (x : ℝ) : ℝ :=
  ((M : ℝ)+1/8)*anchor N/((N : ℝ)+(A : ℝ)+x)
-- STANDING: DEFINITION
noncomputable def ending (A N : ℤ) : ℝ := ((N : ℝ)+(A : ℝ)+1/8)/anchor N

theorem anchor_positive (M A N : ℤ) (hM : 1 ≤ M) (hA : 1 ≤ A) (hN : 4*A*M ≤ N) :
    0 < anchor N ∧ 4*(A : ℝ) ≤ (N : ℝ) := by
  have hm : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have ha : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hn : 4*(A : ℝ)*(M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hp := mul_nonneg (show 0 ≤ (A : ℝ) by linarith) (show 0 ≤ (M : ℝ)-1 by linarith)
  constructor
  · dsimp [anchor]; nlinarith only [hn,hp,ha]
  · nlinarith only [hn,hp]

theorem partner_capture_bounds (M A N : ℤ) (x : ℝ)
    (hM : 1 ≤ M) (hA : 1 ≤ A) (hN : 4*A*M ≤ N)
    (hxlo : -(1/8 : ℝ) ≤ x) (hxhi : x ≤ 1/8) :
    (M : ℝ)-1/8 < partner M A N x ∧ partner M A N x < (M : ℝ)+1/8 := by
  have hm : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have ha : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hn : 4*(A : ℝ)*(M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hd := anchor_positive M A N hM hA hN
  have hden : 0 < (N : ℝ)+(A : ℝ)+x := by dsimp [anchor] at hd; linarith only [hd.2,ha,hxlo]
  have hp := mul_nonneg (show 0 ≤ (M : ℝ) by linarith) (show 0 ≤ (1/8 : ℝ)-x by linarith)
  dsimp [partner,anchor]
  constructor
  · apply (lt_div_iff₀ hden).2
    nlinarith only [hn,hp,ha,hxlo]
  · apply (div_lt_iff₀ hden).2
    have hprod := mul_pos (show 0 < (M : ℝ)+1/8 by linarith)
      (show 0 < (A : ℝ)+x-1/8 by linarith)
    nlinarith only [hprod]

theorem ending_bounds (M A N : ℤ) (hM : 1 ≤ M) (hA : 1 ≤ A) (hN : 4*A*M ≤ N) :
    1 < ending A N ∧ ending A N ≤ 5/4 := by
  have hd := anchor_positive M A N hM hA hN
  have ha : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  dsimp [ending]
  constructor
  · apply (lt_div_iff₀ hd.1).2
    dsimp [anchor]; linarith only [ha]
  · apply (div_le_iff₀ hd.1).2
    dsimp [anchor]; linarith only [hd.2]

theorem ending_step_face (M A N : ℤ) (hM : 1 ≤ M) (hA : 1 ≤ A) (hN : 4*A*M ≤ N) :
    4*(M : ℝ)*(ending A N-1) ≤ 1 := by
  have hd := (anchor_positive M A N hM hA hN).1
  have hn : 4*(A : ℝ)*(M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have he : ending A N-1=(A : ℝ)/anchor N := by
    dsimp [ending]
    field_simp [hd.ne']
    dsimp [anchor]
    ring
  rw [he,←mul_div_assoc]
  apply (div_le_iff₀ hd).2
  dsimp [anchor]
  nlinarith only [hn]

theorem residue_window (M A N J : ℤ) (q T : ℝ)
    (hM : 1 ≤ M) (hA : 1 ≤ A) (hN : 4*A*M ≤ N) (hJ : 0 ≤ J) (hJM : J < M)
    (hqlo : (J : ℝ)+1/8 ≤ q) (hqhi : q ≤ (J : ℝ)+1/2)
    (hTlo : 1 ≤ T) (hThi : T ≤ ending A N) : ¬InWay q T := by
  have hjr : (0 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
  have hjm : (J : ℝ)+1 ≤ (M : ℝ) := by exact_mod_cast hJM
  have hmr : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hqpos : 0 ≤ q := by linarith only [hjr,hqlo]
  have hqM : q ≤ (M : ℝ) := by linarith only [hqhi,hjm]
  have hTstep : T-1 ≤ ending A N-1 := by linarith only [hThi]
  have hp := mul_le_mul hqM hTstep (show 0 ≤ T-1 by linarith only [hTlo]) (by linarith : (0 : ℝ) ≤ (M : ℝ))
  have he := ending_step_face M A N hM hA hN
  have hlo := mul_le_mul_of_nonneg_left hTlo hqpos
  apply not_lt.mpr
  apply clear_of_window J
  · nlinarith only [hlo,hqlo]
  · nlinarith only [hqhi,hp,he]

theorem quiet_window (q T : ℝ) (hqlo : 1/8 ≤ q) (hqhi : q ≤ 3/8)
    (hTlo : 1 ≤ T) (hThi : T ≤ 5/4) : ¬InWay q T := by
  have hp : 0 ≤ q := by linarith only [hqlo]
  have htn : 0 ≤ T := by linarith only [hTlo]
  have hlo := mul_le_mul_of_nonneg_left hTlo hp
  have hhi := mul_le_mul hqhi hThi htn (by norm_num : (0 : ℝ) ≤ 3/8)
  apply not_lt.mpr
  apply clear_of_window 0 <;> norm_num at * <;> linarith only [hqlo,hlo,hhi]

theorem parameter_openings (M A N : ℤ) (x : ℝ)
    (hM : 1 ≤ M) (hA : 1 ≤ A) (hN : 4*A*M ≤ N)
    (hxlo : -(1/8 : ℝ) ≤ x) (hxhi : x ≤ 1/8) :
    let C := ((N : ℝ)+(A : ℝ)+x)/anchor N
    0 < partner M A N x ∧ 1 < C ∧ C ≤ ending A N ∧
      partner M A N x*C=(M : ℝ)+1/8 ∧ anchor N*C=(N : ℝ)+(A : ℝ)+x := by
  dsimp only
  have hd := anchor_positive M A N hM hA hN
  have hb := partner_capture_bounds M A N x hM hA hN hxlo hxhi
  have hm : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have ha : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hden : 0 < (N : ℝ)+(A : ℝ)+x := by linarith only [hd.2,ha,hxlo]
  refine ⟨by linarith only [hb.1,hm],?_,?_,?_,?_⟩
  · apply (lt_div_iff₀ hd.1).2
    dsimp [anchor]; linarith only [ha,hxlo]
  · exact div_le_div_of_nonneg_right (by linarith only [hxhi]) hd.1.le
  · dsimp [partner]
    field_simp [hd.1.ne',hden.ne']
  · field_simp [hd.1.ne',hden.ne']

theorem partner_entry (M A N : ℤ) (x : ℝ)
    (hM : 1 ≤ M) (hA : 1 ≤ A) (hN : 4*A*M ≤ N)
    (hxlo : -(1/8 : ℝ) ≤ x) (hxhi : x ≤ 1/8) :
    InWay (partner M A N x) 1 ∧ label (partner M A N x*1)=M := by
  have hb := partner_capture_bounds M A N x hM hA hN hxlo hxhi
  have hh : |partner M A N x*1-(M : ℝ)| < 1/8 := by
    rw [abs_lt]; constructor <;> nlinarith only [hb.1,hb.2]
  exact ⟨lt_of_le_of_lt (Fresh.Cascade.distInt_le _ _) hh,
    (entry_iff_label _ _ _).1 (Or.inr (by simpa only [mul_one] using hb))⟩

theorem partner_endpoint_bounds (M A N : ℤ) (x : ℝ)
    (hM : 1 ≤ M) (hA : 1 ≤ A) (hN : 4*A*M ≤ N)
    (hxlo : -(1/8 : ℝ) ≤ x) (hxhi : x ≤ 1/8) :
    1 < partnerEnd (anchor N) (partner M A N x) 1 ∧
      partnerEnd (anchor N) (partner M A N x) 1 ≤ ending A N := by
  let C := ((N : ℝ)+(A : ℝ)+x)/anchor N
  have hd := (anchor_positive M A N hM hA hN).1
  have he := partner_entry M A N x hM hA hN hxlo hxhi
  have hg := parameter_openings M A N x hM hA hN hxlo hxhi
  have hSC : partner M A N x*C=(M : ℝ)+1/8 := hg.2.2.2.1
  have hDC : anchor N*C=(N : ℝ)+(A : ℝ)+x := hg.2.2.2.2
  have hfirst : labelledOpening (partner M A N x) 1=C := by
    dsimp [labelledOpening,opening]
    rw [he.2]
    apply (div_eq_iff hg.1.ne').2
    nlinarith only [hSC]
  unfold partnerEnd
  rw [hfirst]
  by_cases hw : InWay (anchor N) C
  · rw [if_pos hw]
    have hstrict : ((N+A : ℤ) : ℝ)-1/8 < anchor N*C := by
      apply lt_of_not_ge
      intro hn
      have hleft : anchor N*C=(N : ℝ)+(A : ℝ)-1/8 := by push_cast at hn ⊢; linarith only [hn,hDC,hxlo]
      have hclear : ¬InWay (anchor N) C := by
        apply not_lt.mpr
        apply clear_of_window (N+A-1) <;> push_cast <;> linarith only [hleft]
      exact hclear hw
    have hlabel : label (anchor N*C)=N+A :=
      (entry_iff_label _ _ _).1 ((entry_interval _ _ _).2 ⟨hstrict,by push_cast; linarith only [hDC,hxhi]⟩)
    have hend : labelledOpening (anchor N) C=ending A N := by
      simp only [labelledOpening,opening,hlabel,ending,Int.cast_add]
    rw [hend]
    exact ⟨(ending_bounds M A N hM hA hN).1,le_rfl⟩
  · rw [if_neg hw]
    exact ⟨hg.2.1,hg.2.2.1⟩

theorem interior_partner_endpoint (M A N : ℤ) (x : ℝ)
    (hM : 1 ≤ M) (hA : 1 ≤ A) (hN : 4*A*M ≤ N)
    (hxlo : -(1/8 : ℝ) < x) (hxhi : x < 1/8) :
    partnerEnd (anchor N) (partner M A N x) 1=ending A N := by
  let C := ((N : ℝ)+(A : ℝ)+x)/anchor N
  have he := partner_entry M A N x hM hA hN hxlo.le hxhi.le
  have hg := parameter_openings M A N x hM hA hN hxlo.le hxhi.le
  have hSC : partner M A N x*C=(M : ℝ)+1/8 := hg.2.2.2.1
  have hDC : anchor N*C=(N : ℝ)+(A : ℝ)+x := hg.2.2.2.2
  have hfirst : labelledOpening (partner M A N x) 1=C := by
    dsimp [labelledOpening,opening]
    rw [he.2]
    apply (div_eq_iff hg.1.ne').2
    nlinarith only [hSC]
  have hb : ((N+A : ℤ) : ℝ)-1/8 < anchor N*C ∧
      anchor N*C < ((N+A : ℤ) : ℝ)+1/8 := by
    push_cast
    constructor <;> linarith only [hDC,hxlo,hxhi]
  have hlabel := (entry_iff_label (anchor N) C (N+A)).1 (Or.inr hb)
  have habs : |anchor N*C-((N+A : ℤ) : ℝ)| < 1/8 := by
    rw [abs_lt]; constructor <;> linarith only [hb.1,hb.2]
  have hw : InWay (anchor N) C := lt_of_le_of_lt (Fresh.Cascade.distInt_le _ _) habs
  unfold partnerEnd
  rw [hfirst,if_pos hw]
  simp only [labelledOpening,opening,hlabel,ending,Int.cast_add]

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (a b : Fin 8) (M A N : ℤ) (x : ℝ),
    a≠k ∧ b≠k ∧ a≠b ∧ 1≤M ∧ 1≤A ∧ 4*A*M≤N ∧ -(1/8 : ℝ)≤x ∧ x≤1/8 ∧
    reading v k a=anchor N ∧ reading v k b=partner M A N x ∧
    ∀ i : Fin 8, i≠k → i≠a → i≠b → ∃ J : ℤ, 0≤J ∧ J<M ∧
      (J : ℝ)+1/8≤reading v k i ∧ reading v k i≤(J : ℝ)+1/2

theorem class_into_recovery {v : Fin 8 → ℝ} {k : Fin 8}
    (h : Class v k) : PairRecoveryClass v k := by
  classical
  obtain ⟨hv,a,b,M,A,N,x,ha,hb,hab,hM,hA,hN,hxlo,hxhi,hda,hsb,hquiet⟩ := h
  refine ⟨hv,a,b,1,N,ha,hb,hab,by norm_num,?_,?_,?_⟩
  · rw [hda]; simp only [mul_one,anchor]
  · rw [hsb]; exact (partner_entry M A N x hM hA hN hxlo hxhi).1
  · intro d hd
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hd
    have him := Finset.mem_sdiff.mp hi
    have hik := (Finset.mem_erase.mp him.1).1
    have hia : i≠a := by intro he; apply him.2; simp [he]
    have hib : i≠b := by intro he; apply him.2; simp [he]
    obtain ⟨J,hJ,hJM,hqlo,hqhi⟩ := hquiet i hik hia hib
    rw [hda,hsb]
    exact residue_window M A N J _ _ hM hA hN hJ hJM hqlo hqhi
      (partner_endpoint_bounds M A N x hM hA hN hxlo hxhi).1.le
      (partner_endpoint_bounds M A N x hM hA hN hxlo hxhi).2

theorem low_band_into_class {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k a b : Fin 8) (M A N : ℤ) (x : ℝ) (ha : a≠k) (hb : b≠k) (hab : a≠b)
    (hM : 1 ≤ M) (hA : 1 ≤ A) (hN : 4*A*M ≤ N)
    (hxlo : -(1/8 : ℝ)≤x) (hxhi : x≤1/8)
    (hda : reading v k a=anchor N) (hsb : reading v k b=partner M A N x)
    (hquiet : ∀ i : Fin 8, i≠k → i≠a → i≠b → 1/8≤reading v k i ∧ reading v k i≤3/8) :
    Class v k := by
  refine ⟨hv,a,b,M,A,N,x,ha,hb,hab,hM,hA,hN,hxlo,hxhi,hda,hsb,?_⟩
  intro i hi hia hib
  have hq := hquiet i hi hia hib
  refine ⟨0,by omega,by omega,?_,?_⟩ <;> norm_num <;> linarith only [hq.1,hq.2]

theorem class_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : Isolation v k :=
  pairRecovery_isolation (class_into_recovery h)

-- STANDING: DEFINITION
noncomputable def ScaledClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ c : ℝ, 0<c ∧ Class (fun i=>c*v i) k

theorem scaled_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ScaledClass v k) : Isolation v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact Fresh.ProvedTypesScale.Isolation_smul_of hc (class_isolation hbase)

#print axioms interior_partner_endpoint
#print axioms ending_step_face
#print axioms residue_window
#print axioms low_band_into_class
#print axioms partner_entry
#print axioms partner_endpoint_bounds
#print axioms class_into_recovery
#print axioms class_isolation
#print axioms scaled_isolation

#print axioms anchor_positive
#print axioms partner_capture_bounds
#print axioms ending_bounds
#print axioms quiet_window
#print axioms parameter_openings
end Fresh.NativeQuietReversalFamily
