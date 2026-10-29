import Fresh.NativeCommonOpeningGridBands

/-! Exact native entry cells independent of the unbounded anchor heights.
The common-opening ratio is at most 81/71, attained at K=H=1. This derives
six nonempty nonnegative base-label bands, including closed upper edges;
actual grid lifts and physical labels remain independently unbounded. -/
namespace Fresh.NativeUniformOpeningCells
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeOneReaderDeformation
  Fresh.NativeCanonicalReturn Fresh.FastestCaptureRetention Fresh.NativeUpperGridPacket
  Fresh.NativeUpperGridHeightTransport

theorem numerator_ratio (K H : ℤ) (hK : 1 ≤ K) (hH : 1 ≤ H) :
    0<period K H ∧ 71*numerator K H ≤ 81*period K H := by
  have hm := mul_nonneg (show 0 ≤ H by omega) (show 0 ≤ K-1 by omega)
  dsimp [period,numerator]
  constructor <;> nlinarith only [hm,hH]

theorem opening_ratio_bound (d p V : ℝ) (K H : ℤ) (hd : 0<d) (hp : 0<p)
    (hV : 0<V) (hK : 1 ≤ K) (hH : 1 ≤ H) (hdV : d*V=(K : ℝ))
    (hpV : p*V=8*(H : ℝ)*(K : ℝ)+7/8) :
    71*labelledOpening p (V+1/(8*d)) ≤ 81*V := by
  have hh := numerator_ratio K H hK hH
  have hD : (0 : ℝ)<(period K H : ℝ) := by exact_mod_cast hh.1
  have hr : 71*(numerator K H : ℝ) ≤ 81*(period K H : ℝ) := by exact_mod_cast hh.2
  have hm := mul_le_mul_of_nonneg_right hr hV.le
  have he := opening_ratio d p V K H hd hp hK hdV hpV
  by_contra hn
  have hb := mul_pos hD (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith only [hm,he,hb]

-- STANDING: DEFINITION
noncomputable def Face (q V : ℝ) (J : ℤ) : Prop :=
  (J : ℝ)+1/8 ≤ q*V ∧ 81*(q*V) ≤ 71*((J : ℝ)+7/8)

theorem entry_window (d p q V : ℝ) (K H J : ℤ) (hd : 0<d) (hp : 0<p)
    (hV : 0<V) (hK : 1 ≤ K) (hH : 1 ≤ H) (hJ : 0 ≤ J)
    (hdV : d*V=(K : ℝ)) (hpV : p*V=8*(H : ℝ)*(K : ℝ)+7/8)
    (hface : Face q V J) :
    (J : ℝ)+1/8 ≤ q*labelledOpening p (V+1/(8*d)) ∧
      q*labelledOpening p (V+1/(8*d)) ≤ (J : ℝ)+7/8 := by
  have hJr : (0 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
  have hq : 0<q := by nlinarith only [hface.1,hJr,hV]
  have ht := Fresh.NativeCommonOpeningGridBands.first_displacement d p V K H hd hp hK hH hdV hpV
  have hlo := mul_nonneg hq.le ht.1.le
  have hu := opening_ratio_bound d p V K H hd hp hV hK hH hdV hpV
  have hhi := mul_le_mul_of_nonneg_left hu hq.le
  constructor <;> nlinarith only [hface.1,hface.2,hlo,hhi]

theorem nonempty_cells (J : ℤ) (_hJ : 0 ≤ J) :
    (∃ A : ℝ,(J : ℝ)+1/8 ≤ A ∧ 81*A ≤ 71*((J : ℝ)+7/8)) ↔ J ≤ 5 := by
  constructor
  · rintro ⟨A,hlo,hhi⟩
    have hr : (10 : ℝ)*(J : ℝ) ≤ 52 := by nlinarith only [hlo,hhi]
    have hz : 10*J ≤ 52 := by exact_mod_cast hr
    omega
  · intro h
    refine ⟨(J : ℝ)+1/8,le_rfl,?_⟩
    have hr : (J : ℝ) ≤ 5 := by exact_mod_cast h
    nlinarith only [hr]

theorem quiet_into_face (q V : ℝ) (hlo : 1/8 ≤ q*V) (hhi : q*V ≤ 3/4) : Face q V 0 := by
  constructor <;> norm_num at * <;> nlinarith only [hlo,hhi]

theorem coset_clear (d p q V : ℝ) (K H j : ℤ) (hd : 0<d) (hp : 0<p)
    (hV : 0<V) (hK : 1 ≤ K) (hH : 1 ≤ H)
    (hdV : d*V=(K : ℝ)) (hpV : p*V=8*(H : ℝ)*(K : ℝ)+7/8)
    (hq : q=p ∨ ∃ J : ℤ,0 ≤ J ∧ Face q V J) :
    1/8 ≤ distInt ((q+8*(j : ℝ)*(period K H : ℝ)*d)*labelledOpening p (V+1/(8*d))) := by
  rw [(height_shifts d p q V K H j hd hp hK hdV hpV).2.2,distInt_add_int]
  rcases hq with he|⟨J,hJ,hf⟩
  · rw [he]
    have ho := labelled_opening_identity p (V+1/(8*d)) hp
    exact clear_of_window _ ho.ge (by linarith only [ho])
  · have hw := entry_window d p q V K H J hd hp hV hK hH hJ hdV hpV hf
    exact clear_of_window J hw.1 hw.2

theorem coset_entry_clear (d p q V : ℝ) (K H j : ℤ) (hd : 0<d) (hp : 0<p)
    (hK : 1 ≤ K) (hdV : d*V=(K : ℝ)) (hpV : p*V=8*(H : ℝ)*(K : ℝ)+7/8)
    (hq : q=p ∨ ∃ J : ℤ,0 ≤ J ∧ Face q V J) :
    1/8 ≤ distInt ((q+8*(j : ℝ)*(period K H : ℝ)*d)*V) := by
  rw [(height_shifts d p q V K H j hd hp hK hdV hpV).1,distInt_add_int]
  rcases hq with he|⟨J,hJ,hf⟩
  · rw [he]
    apply clear_of_window (8*H*K) <;> push_cast <;> nlinarith only [hpV]
  · have hJr : (0 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
    apply clear_of_window J hf.1
    nlinarith only [hf.2,hJr]


-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (V : ℝ) (u a : Fin 8) (K H : ℤ),
    u≠k ∧ a≠k ∧ 1 ≤ K ∧ 1 ≤ H ∧
    reading v k u*V=(K : ℝ) ∧ reading v k a*V=8*(H : ℝ)*(K : ℝ)+7/8 ∧
    ∀ i : Fin 8,i≠k → reading v k i=reading v k u ∨ ∃ (q : ℝ) (j : ℤ),
      (q=reading v k a ∨ ∃ J : ℤ,0 ≤ J ∧ Face q V J) ∧
      reading v k i=q+8*(j : ℝ)*(period K H : ℝ)*reading v k u

theorem class_fragment {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) :
    ∃ V W Z : ℝ,0<V ∧ V<W ∧ W<Z ∧ IsMove (disparitySet v k) V W ∧
      IsMove (disparitySet v k) W Z ∧ IsolatedAt v k Z := by
  obtain ⟨hv,V,u,a,K,H,hu,ha,hK,hH,hdV,hpV,hread⟩ := h
  let d := reading v k u
  let p := reading v k a
  let W := V+1/(8*d)
  let Z := labelledOpening p W
  have hd : 0<d := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨u,hu,rfl⟩)
  have hp : 0<p := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hV : 0<V := by nlinarith only [hdV,hKr,hd]
  have ht := Fresh.NativeCommonOpeningGridBands.first_displacement d p V K H hd hp hK hH hdV hpV
  have hdW := Fresh.NativeDoubleGridRecovery.integer_step d V K hd hdV
  change d*W=(K : ℝ)+1/8 at hdW
  have hc := (upper_return d p V K H hd hK hdV hpV).2.2.1
  have hZW := (captured_labelled_advance p W hp hc).1
  have hlo := mul_le_mul_of_nonneg_left hZW.le hd.le
  have hdZ : (K : ℝ)+1/8 ≤ d*Z ∧ d*Z<(K : ℝ)+7/8 := by
    constructor <;> nlinarith only [hdW,hlo,hdV,ht.2]
  have hpoint : IsolatedAt v k Z := by
    apply (isolatedAt_iff_lonelyAt v k Z).2
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hx
    change 1/8 ≤ distInt (reading v k i*Z)
    rcases hread i hi with he|⟨q,j,hq,he⟩
    · rw [he]; exact clear_of_window K hdZ.1 hdZ.2.le
    · rw [he]; exact coset_clear d p q V K H j hd hp hV hK hH hdV hpV hq
  have hVW : V<W := by
    change V<V+1/(8*d)
    exact lt_add_of_pos_right V (by positivity)
  have hWZ : W<Z := by linarith only [hZW]
  have hdCap : InWay d V := by
    change distInt (d*V)<1/8
    rw [hdV,distInt_intCast]
    norm_num
  have hdNext : nextOpening d V=W := by
    rw [nextOpening_eq (show |d*V-(K : ℝ)|<1/8 by rw [hdV]; norm_num)]
    apply (div_eq_iff hd.ne').2
    nlinarith only [hdW]
  have hmoveVW : IsMove (disparitySet v k) V W := by
    refine Or.inr ⟨d,mem_disparitySet.mpr ⟨u,hu,rfl⟩,hdCap,hdNext.symm,?_⟩
    intro x hx hxc
    obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hx
    change nextOpening (reading v k i) V ≤ W
    rcases hread i hi with he|⟨q,j,hq,he⟩
    · rw [he]; exact hdNext.le
    · have hclear := coset_entry_clear d p q V K H j hd hp hK hdV hpV hq
      rw [←he] at hclear
      exact False.elim (not_lt.mpr hclear hxc)
  have hmoveWZ : IsMove (disparitySet v k) W Z := by
    refine Or.inr ⟨p,mem_disparitySet.mpr ⟨a,ha,rfl⟩,hc,?_,?_⟩
    · exact (captured_opening p W hc).symm
    · intro x hx hxc
      exact nextOpening_le_of_lonely (disparitySet_pos hv k)
        ((isolatedAt_iff_lonelyAt v k Z).1 hpoint) hWZ.le hx hxc
  exact ⟨V,W,Z,hV,hVW,hWZ,hmoveVW,hmoveWZ,hpoint⟩

theorem class_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) :
    CanonicalReturnClass v k := by
  obtain ⟨V,W,Z,hV,hVW,hWZ,_hmV,hmW,hpoint⟩ := class_fragment h
  exact Fresh.NativeFixedPrefixArrangement.canonical_of_isolating_move h.1 k W Z
    (hV.trans hVW) hWZ hmW hpoint

theorem class_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : Isolation v k :=
  canonical_isolation (class_into_canonical h)

-- STANDING: DEFINITION
noncomputable def ScaledClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ c : ℝ,0<c ∧ Class (fun i=>c*v i) k

theorem scaled_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ScaledClass v k) : Isolation v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact Fresh.ProvedTypesScale.Isolation_smul_of hc (class_isolation hbase)

theorem bands_into_cells {v : Fin 8 → ℝ} {k : Fin 8}
    (h : Fresh.NativeCommonOpeningGridBands.Class v k) : Class v k := by
  obtain ⟨hv,V,u,a,K,H,hu,ha,hK,hH,hdV,hpV,hread⟩ := h
  refine ⟨hv,V,u,a,K,H,hu,ha,hK,hH,hdV,hpV,?_⟩
  intro i hi
  rcases hread i hi with he|⟨q,j,hq,he⟩
  · exact Or.inl he
  · refine Or.inr ⟨q,j,?_,he⟩
    rcases hq with he|hq
    · exact Or.inl he
    · exact Or.inr ⟨0,le_rfl,quiet_into_face q V hq.1 hq.2⟩

theorem scaled_bands_into_cells {v : Fin 8 → ℝ} {k : Fin 8}
    (h : Fresh.NativeCommonOpeningGridBands.ScaledClass v k) : ScaledClass v k := by
  obtain ⟨hv,c,hc,hbase⟩ := h
  exact ⟨hv,c,hc,bands_into_cells hbase⟩

#print axioms numerator_ratio
#print axioms opening_ratio_bound
#print axioms entry_window
#print axioms nonempty_cells
#print axioms quiet_into_face
#print axioms coset_clear
#print axioms coset_entry_clear
#print axioms class_fragment
#print axioms class_into_canonical
#print axioms class_isolation
#print axioms scaled_isolation
#print axioms bands_into_cells
#print axioms scaled_bands_into_cells
end Fresh.NativeUniformOpeningCells
