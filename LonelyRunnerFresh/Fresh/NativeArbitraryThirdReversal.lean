import Fresh.NativeSuppliedOpeningTriple
import Fresh.NativeQuietReversalFamily

/-! A parameterized pair with ONE arbitrary additional reading at or beyond
the native start, and four quiet physical readers. Explicit incoming opening
faces cover both closed partner edges. All outsider guards are derived. -/
namespace Fresh.NativeArbitraryThirdReversal
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeOpeningReversal Fresh.NativeOneReaderDeformation
  Fresh.NativeQuietReversalFamily Fresh.NativeFixedPrefixArrangement Fresh.NativeGroupEndpointRecovery
  Fresh.NativeCanonicalReturn Fresh.NativeRecapturedLabelReset Fresh.FastestCaptureRetention

-- STANDING: DEFINITION
noncomputable def firstTime (A N : ℤ) (x : ℝ) : ℝ := ((N : ℝ)+(A : ℝ)+x)/anchor N

theorem parameter_separation (M A N : ℤ) (x : ℝ)
    (hM : 1≤M) (hA : 1≤A) (hN : 4*A*M≤N)
    (hxlo : -(1/8 : ℝ)≤x) (hxhi : x≤1/8) :
    33/8≤anchor N ∧ 7/8<partner M A N x ∧ 3*partner M A N x<anchor N := by
  have hd := anchor_positive M A N hM hA hN
  have hp := partner_capture_bounds M A N x hM hA hN hxlo hxhi
  have hm : (1 : ℝ)≤(M : ℝ) := by exact_mod_cast hM
  have ha : (1 : ℝ)≤(A : ℝ) := by exact_mod_cast hA
  have hn : 4*(A : ℝ)*(M : ℝ)≤(N : ℝ) := by exact_mod_cast hN
  have ht := mul_nonneg (show 0≤(M : ℝ) by linarith) (show 0≤(A : ℝ)-1 by linarith)
  dsimp [anchor] at hd ⊢
  constructor
  · linarith only [hd.2,ha]
  · constructor <;> nlinarith only [hp.1,hp.2,hm,hn,ht]

theorem incoming_faces (M A N : ℤ) (x : ℝ)
    (hM : 1≤M) (hA : 1≤A) (hN : 4*A*M≤N)
    (hxlo : -(1/8 : ℝ)≤x) (hxhi : x≤1/8) :
    1<firstTime A N x ∧ firstTime A N x≤ending A N ∧
      partner M A N x*firstTime A N x=(M : ℝ)+1/8 ∧
      anchor N*ending A N=((N+A : ℤ) : ℝ)+1/8 ∧
      anchor N*(ending A N-firstTime A N x)≤1/4 := by
  have hg := parameter_openings M A N x hM hA hN hxlo hxhi
  have hd := (anchor_positive M A N hM hA hN).1
  have he : anchor N*ending A N=((N+A : ℤ) : ℝ)+1/8 := by
    dsimp [ending]
    push_cast
    field_simp [hd.ne']
  refine ⟨hg.2.1,hg.2.2.1,hg.2.2.2.1,he,?_⟩
  have hc : anchor N*firstTime A N x=(N : ℝ)+(A : ℝ)+x := hg.2.2.2.2
  push_cast at he
  nlinarith only [he,hc,hxlo]

theorem third_lower (c E : ℝ) (hc : 1/8≤c) (hElo : 1≤E) (hEhi : E≤5/4)
    (hw : InWay c E) : 7/10<c := by
  have hcp : 0≤c := by linarith only [hc]
  have hlo := mul_le_mul_of_nonneg_left hElo hcp
  have hlabel := capture_label_positive c E (by nlinarith only [hlo,hc]) hw
  have hr : (1 : ℝ)≤(label (c*E) : ℝ) := by exact_mod_cast hlabel
  have hcap := (capture_at_label c E hw).1
  by_contra hn
  have hm := mul_le_mul (le_of_not_gt hn) hEhi (show 0≤E by linarith only [hElo]) (by norm_num : (0 : ℝ)≤7/10)
  nlinarith only [hm,hr,hcap]

theorem quiet_before_closing (q T : ℝ) (hqlo : 1/8≤q) (hqhi : q≤3/8)
    (hTlo : 1≤T) (hThi : T≤7/3) : ¬InWay q T := by
  have hlo := mul_le_mul_of_nonneg_left hTlo (show 0≤q by linarith only [hqlo])
  have hhi := mul_le_mul hqhi hThi (show 0≤T by linarith only [hTlo]) (by norm_num : (0 : ℝ)≤3/8)
  apply not_lt.mpr
  apply clear_of_window 0 <;> norm_num at * <;> nlinarith only [hlo,hhi,hqlo]

theorem anchored_point_into_canonical {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k a : Fin 8) (E : ℝ) (L : ℤ) (ha : a≠k) (hL : 0<L)
    (ho : reading v k a*E=(L : ℝ)+1/8) (hpoint : IsolatedAt v k E) :
    CanonicalReturnClass v k := by
  have hd := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hdp : 0<reading v k a := hd
  let Q := (L : ℝ)/reading v k a
  have hlp : (0 : ℝ)<(L : ℝ) := by exact_mod_cast hL
  have hQ : 0<Q := div_pos hlp hdp
  have hphase : reading v k a*Q=(L : ℝ) := by dsimp [Q]; field_simp
  have habs : |reading v k a*Q-(L : ℝ)|<1/8 := by rw [hphase]; norm_num
  have hcap : InWay (reading v k a) Q := lt_of_le_of_lt (Fresh.Cascade.distInt_le _ _) habs
  have hn : nextOpening (reading v k a) Q=E := by
    rw [nextOpening_eq habs]
    apply (div_eq_iff hdp.ne').2
    nlinarith only [ho]
  have hQE : Q<E := by have hh := lt_nextOpening hdp hcap; rw [hn] at hh; exact hh
  have hm : IsMove (disparitySet v k) Q E := by
    refine Or.inr ⟨reading v k a,mem_disparitySet.mpr ⟨a,ha,rfl⟩,hcap,hn.symm,?_⟩
    intro d hd hwd
    exact nextOpening_le_of_lonely (disparitySet_pos hv k)
      ((isolatedAt_iff_lonelyAt v k E).1 hpoint) hQE.le hd hwd
  exact canonical_of_isolating_move hv k Q E hQ hQE hm hpoint

#print axioms parameter_separation
#print axioms incoming_faces
#print axioms third_lower
#print axioms quiet_before_closing
#print axioms anchored_point_into_canonical

theorem quiet_triple_point {v : Fin 8 → ℝ} (k a b c : Fin 8) (T : ℝ)
    (hquiet : ∀ i : Fin 8, i≠k → i≠a → i≠b → i≠c →
      1/8≤reading v k i ∧ reading v k i≤3/8)
    (hTlo : 1≤T) (hThi : T≤7/3)
    (htriple : LonelyAt ({reading v k a,reading v k b,reading v k c} : Finset ℝ) T) :
    IsolatedAt v k T := by
  apply (isolatedAt_iff_lonelyAt v k T).2
  intro d hd
  obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hd
  change 1/8≤distInt (reading v k i*T)
  by_cases hia : i=a
  · subst i; exact htriple _ (by simp)
  by_cases hib : i=b
  · subst i; exact htriple _ (by simp)
  by_cases hic : i=c
  · subst i; exact htriple _ (by simp)
  have hq := hquiet i hi hia hib hic
  exact not_lt.mp (quiet_before_closing _ T hq.1 hq.2 hTlo hThi)

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (a b c : Fin 8) (M A N : ℤ) (x : ℝ),
    a≠k ∧ b≠k ∧ c≠k ∧ a≠b ∧ a≠c ∧ b≠c ∧
    1≤M ∧ 1≤A ∧ 4*A*M≤N ∧ -(1/8 : ℝ)≤x ∧ x≤1/8 ∧
    reading v k a=anchor N ∧ reading v k b=partner M A N x ∧
    1/8≤reading v k c ∧
    ∀ i : Fin 8, i≠k → i≠a → i≠b → i≠c →
      1/8≤reading v k i ∧ reading v k i≤3/8

theorem class_into_canonical {v : Fin 8 → ℝ} {k : Fin 8}
    (h : Class v k) : CanonicalReturnClass v k := by
  classical
  obtain ⟨hv,a,b,c,M,A,N,x,ha,hb,hc,hab,hac,hbc,hM,hA,hN,hxlo,hxhi,hda,hsb,hclo,hquiet⟩ := h
  have hsep := parameter_separation M A N x hM hA hN hxlo hxhi
  have hf := incoming_faces M A N x hM hA hN hxlo hxhi
  have he := ending_bounds M A N hM hA hN
  have hpa : 0<reading v k a := by rw [hda]; linarith only [hsep.1]
  have hpb : 0<reading v k b := by rw [hsb]; linarith only [hsep.2.1]
  have hpc : 0<reading v k c := by linarith only [hclo]
  have hfast : 3*reading v k b<reading v k a := by rw [hda,hsb]; exact hsep.2.2
  have ho : reading v k b*firstTime A N x=(M : ℝ)+1/8 := by rw [hsb]; exact hf.2.2.1
  have hoa : reading v k a*ending A N=((N+A : ℤ) : ℝ)+1/8 := by rw [hda]; exact hf.2.2.2.1
  have hquarter : reading v k a*(ending A N-firstTime A N x)≤1/4 := by
    rw [hda]; exact hf.2.2.2.2
  by_cases hthird : InWay (reading v k c) (ending A N)
  · obtain ⟨H,U,hH,hCU,hUR,hm,hclear⟩ :=
      Fresh.NativeSuppliedOpeningTriple.forced_triple_resolution
        (reading v k a) (reading v k b) (reading v k c) (firstTime A N x) (ending A N)
        M (N+A) hpa hpb hpc hfast ho hf.2.1 hquarter hoa hthird
    have hend : Fresh.NativeSuppliedOpeningTriple.exitEnd
        (reading v k a) (reading v k b) (reading v k c) (ending A N)<7/3 :=
      Fresh.NativeSuppliedOpeningTriple.exit_before_quiet_closing _ _ _ _
        (by rw [hda]; exact hsep.1) (by rw [hsb]; exact hsep.2.1)
        (third_lower _ _ hclo he.1.le he.2 hthird) he.2 hthird
    have hpoint := quiet_triple_point k a b c _ hquiet
      (hf.1.le.trans (hCU.trans hUR.le)) hend.le hclear
    have hsub : H ⊆ disparitySet v k := by
      intro d hd
      have hx := hH hd
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl|rfl
      · exact mem_disparitySet.mpr ⟨a,ha,rfl⟩
      · exact mem_disparitySet.mpr ⟨b,hb,rfl⟩
      · exact mem_disparitySet.mpr ⟨c,hc,rfl⟩
    have hfullclear := (isolatedAt_iff_lonelyAt v k _).1 hpoint
    have hfull := endpoint_clear_preserves_move (ds:=H) (added:=disparitySet v k\H)
      (fun d hd=>disparitySet_pos hv k d (hsub hd))
      (fun d hd=>disparitySet_pos hv k d (Finset.mem_sdiff.mp hd).1) _ _ hm
      (fun d hd=>not_lt.mpr (hfullclear d (Finset.mem_sdiff.mp hd).1))
    rw [Finset.union_sdiff_of_subset hsub] at hfull
    exact canonical_of_isolating_move hv k _ _
      ((by linarith only [hf.1] : 0<firstTime A N x).trans_le hCU) hUR hfull hpoint
  · have hstep : 0≤ending A N-firstTime A N x := sub_nonneg.mpr hf.2.1
    have hba : reading v k b≤reading v k a := by linarith only [hfast,hpb]
    have hmult := mul_le_mul_of_nonneg_right hba hstep
    have hbclear : ¬InWay (reading v k b) (ending A N) := by
      apply not_lt.mpr
      apply clear_of_window M <;> nlinarith only [ho,hquarter,hmult,mul_nonneg hpb.le hstep]
    have haclear : ¬InWay (reading v k a) (ending A N) := by
      apply not_lt.mpr
      exact clear_of_window (N+A) hoa.ge (by linarith only [hoa])
    have htriple : LonelyAt ({reading v k a,reading v k b,reading v k c} : Finset ℝ) (ending A N) := by
      intro d hd
      simp only [Finset.mem_insert,Finset.mem_singleton] at hd
      rcases hd with rfl|rfl|rfl
      · exact not_lt.mp haclear
      · exact not_lt.mp hbclear
      · exact not_lt.mp hthird
    have hpoint := quiet_triple_point k a b c (ending A N) hquiet he.1.le
      (by linarith only [he.2]) htriple
    have hL : 0<N+A := by
      have hd := (anchor_positive M A N hM hA hN).2
      have har : (1 : ℝ)≤(A : ℝ) := by exact_mod_cast hA
      have hr : (0 : ℝ)<((N+A : ℤ) : ℝ) := by push_cast; linarith only [hd,har]
      exact_mod_cast hr
    exact anchored_point_into_canonical hv k a _ (N+A) ha hL hoa hpoint

theorem class_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : Isolation v k :=
  canonical_isolation (class_into_canonical h)

-- STANDING: DEFINITION
noncomputable def ScaledClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ c : ℝ, 0<c ∧ Class (fun i=>c*v i) k

theorem scaled_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ScaledClass v k) : Isolation v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact Fresh.ProvedTypesScale.Isolation_smul_of hc (class_isolation hbase)

#print axioms quiet_triple_point
#print axioms class_into_canonical
#print axioms class_isolation
#print axioms scaled_isolation

end Fresh.NativeArbitraryThirdReversal
