import Fresh.NativeClearReboundCore
import Fresh.NativeFiveThirdsBoundary
import Fresh.NativeArbitraryThirdReversal
import Fresh.NativeClearWitnessArrangement

/-! Independent positive grid/residue lifts of a native returned core.
Outsiders need not preserve any of its earlier full-arrangement visits. -/
namespace Fresh.NativeReturnedGridArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeClearWindowWitness
  Fresh.NativeClearReboundCore Fresh.NativeCanonicalReturn Fresh.FastestCaptureRetention

-- STANDING: DEFINITION
noncomputable def Grid (q s : ℝ) (L : ℤ) : Prop :=
  ∃ (K a : ℤ), 0≤K ∧ (a=1 ∨ a=4 ∨ a=7) ∧
    q*(8*(L : ℝ)+1)=s*(8*(K : ℝ)+(a : ℝ))

theorem grid_clear (q s V : ℝ) (L : ℤ) (hs : 0<s)
    (ho : s*V=(L : ℝ)+1/8) (h : Grid q s L) : 1/8≤distInt (q*V) := by
  obtain ⟨K,a,_hK,ha,hr⟩ := h
  have h1 := congrArg (fun z : ℝ=>q*z) ho
  have he : q*V=(K : ℝ)+(a : ℝ)/8 := by
    have hc : s*(8*(q*V)-8*(K : ℝ)-(a : ℝ))=0 := by nlinarith only [h1,hr]
    have hz := (mul_eq_zero.mp hc).resolve_left hs.ne'
    linarith only [hz]
  apply clear_of_window K <;> rcases ha with rfl|rfl|rfl <;> norm_num at he ⊢ <;> linarith only [he]

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (P R : ℝ) (I : Finset (Fin 8)) (N : ℤ) (g j i : Fin 8),
    Witness v k P I N ∧ P≤R ∧ 0<R ∧ g∈I ∧ j∈I ∧ i∈I ∧
    InWay (reading v k g) R ∧ InWay (reading v k j) (handoffOpening v k R g) ∧
    InWay (reading v k i) R ∧ handoffOpening v k R i≤handoffOpening v k R g ∧
    InWay (reading v k i) (handoffOpening v k (handoffOpening v k R g) j) ∧
    ∀ q : Fin 8, q≠k → reading v k q∉({reading v k g,reading v k j,reading v k i} : Finset ℝ) →
      Grid (reading v k q) (reading v k i)
        (label (reading v k i*handoffOpening v k (handoffOpening v k R g) j)) ∨
      ∃ K : ℤ, Fresh.NativeClearWitnessArrangement.Face (reading v k q) (reading v k i)
        (reading v k j) (handoffOpening v k R g) K

theorem class_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : CanonicalReturnClass v k := by
  obtain ⟨hv,P,R,I,N,g,j,i,hwit,_hPR,hR,hg,hj,hi,hwg,hwj,hwi,horder,hret,houtside⟩ := h
  have hgk := (Finset.mem_erase.mp (hwit.2.1 hg)).1
  have hjk := (Finset.mem_erase.mp (hwit.2.1 hj)).1
  have hik := (Finset.mem_erase.mp (hwit.2.1 hi)).1
  have hgp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hgk,rfl⟩)
  have hjp : 0<reading v k j := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨j,hjk,rfl⟩)
  have hip : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hik,rfl⟩)
  have hcore := core_clear (reading v k g) (reading v k j) (reading v k i) R hgp hjp hip
    (pair_ratio hwit hi hg) (pair_ratio hwit hg hj) (pair_ratio hwit hj hg) hwg hwj hwi horder hret
  have hw := first_window (reading v k g) (reading v k i) R hgp hip (pair_ratio hwit hi hg) hwg hwi horder
  have hy := captured_labelled_advance (reading v k j) (handoffOpening v k R g) hjp hwj
  change 0 < handoffOpening v k (handoffOpening v k R g) j-handoffOpening v k R g ∧ _ at hy
  have hl := recapture_label_rises (reading v k i) (handoffOpening v k R g)
    (handoffOpening v k (handoffOpening v k R g) j) (label (reading v k i*R)) hip
    (by linarith only [hy.1]) hw.1 hret
  have hlabel0 := positive_entry_label (reading v k i) R hip hR
  have hL : 0<label (reading v k i*handoffOpening v k (handoffOpening v k R g) j) := by omega
  have ho := handoff_identity hv k i (handoffOpening v k (handoffOpening v k R g) j) hik
  apply Fresh.NativeArbitraryThirdReversal.anchored_point_into_canonical hv k i _ _ hik hL ho
  apply (isolatedAt_iff_lonelyAt v k _).2
  intro d hd
  obtain ⟨q,hq,rfl⟩ := mem_disparitySet.mp hd
  change 1/8≤distInt (reading v k q*_)
  by_cases hmem : reading v k q∈({reading v k g,reading v k j,reading v k i} : Finset ℝ)
  · exact hcore _ hmem
  rcases houtside q hq hmem with hgrid|⟨K,hface⟩
  · exact grid_clear _ _ _ _ hip ho hgrid
  · have hqp : 0<reading v k q := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨q,hq,rfl⟩)
    have ht := Fresh.NativeClearWitnessArrangement.retained_window (reading v k i) (reading v k j)
      (reading v k q) (handoffOpening v k R g) K hip hjp hqp hwj hret hface
    exact clear_of_window K ht.1 ht.2.le

theorem class_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : Isolation v k :=
  canonical_isolation (class_into_canonical h)

-- STANDING: DEFINITION
noncomputable def ScaledClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ c : ℝ, 0<c ∧ Class (fun i=>c*v i) k

theorem scaled_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ScaledClass v k) : Isolation v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact Fresh.ProvedTypesScale.Isolation_smul_of hc (class_isolation hbase)

#print axioms grid_clear
#print axioms class_into_canonical
#print axioms class_isolation
#print axioms scaled_isolation
end Fresh.NativeReturnedGridArrangement
