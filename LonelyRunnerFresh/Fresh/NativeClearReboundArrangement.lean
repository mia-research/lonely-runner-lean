import Fresh.NativeClearWindowRebound
import Fresh.NativeClearWitnessArrangement

/-! An old clear-window packet return forces a fast reader that clears its
selected predecessors. Compatible packet members and native entry faces
supply the remaining duties; terminal clearance is not a hypothesis. -/
namespace Fresh.NativeClearReboundArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeCanonicalReturn
  Fresh.NativeFixedPrefixArrangement Fresh.NativeClearWindowWitness Fresh.NativeClearWindowRebound
  Fresh.NativeOneReaderDeformation Fresh.FastestCaptureRetention Fresh.NativeTwoSetterPacket

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (P R : ℝ) (I : Finset (Fin 8)) (N : ℤ) (g j i : Fin 8),
    Witness v k P I N ∧ P ≤ R ∧ 0 < R ∧ g∈I ∧ j∈I ∧ i∈I ∧
    InWay (reading v k g) R ∧ IsMove (disparitySet v k) R (handoffOpening v k R g) ∧
    InWay (reading v k j) (handoffOpening v k R g) ∧
    IsMove (disparitySet v k) (handoffOpening v k R g) (handoffOpening v k (handoffOpening v k R g) j) ∧
    InWay (reading v k i) R ∧ InWay (reading v k i) (handoffOpening v k (handoffOpening v k R g) j) ∧
    IsMove (disparitySet v k) (handoffOpening v k (handoffOpening v k R g) j)
      (handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i) ∧
    ∀ s : Fin 8, s≠k → reading v k s∉({reading v k g,reading v k j,reading v k i} : Finset ℝ) →
      (InWay (reading v k s) (handoffOpening v k (handoffOpening v k R g) j) ∧
        (reading v k s ≤ 3*reading v k i ∨
          handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) s=
            handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i)) ∨
      (s∈I ∧ InWay (reading v k s) (handoffOpening v k R g) ∧ reading v k s ≤ reading v k i) ∨
      ∃ K : ℤ, Fresh.NativeClearWitnessArrangement.Face (reading v k s) (reading v k i)
        (reading v k j) (handoffOpening v k R g) K

theorem class_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : CanonicalReturnClass v k := by
  obtain ⟨hv,P,R,I,N,g,j,i,hwit,_hPR,hR,hg,hj,hi,hwg,hm1,hwj,hm2,hwi,hret,hm3,houtside⟩ := h
  have hgk := (Finset.mem_erase.mp (hwit.2.1 hg)).1
  have hjk := (Finset.mem_erase.mp (hwit.2.1 hj)).1
  have hik := (Finset.mem_erase.mp (hwit.2.1 hi)).1
  have hgp : 0 < reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hgk,rfl⟩)
  have hjp : 0 < reading v k j := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨j,hjk,rfl⟩)
  have hip : 0 < reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hik,rfl⟩)
  have hcore := returned_core_clear hv k P R I N hwit g j i hg hj hi hwg hm1 hwj hm2 hwi hret
  have hUpos : 0 < handoffOpening v k (handoffOpening v k R g) j :=
    (hR.trans_le (le_of_isMove (disparitySet_pos hv k) hm1)).trans_le
      (le_of_isMove (disparitySet_pos hv k) hm2)
  have hUV : handoffOpening v k (handoffOpening v k R g) j <
      handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i := by
    have ht := lt_nextOpening hip hret
    rw [next_at_label _ _ hret] at ht
    exact ht
  have hpoint : IsolatedAt v k (handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i) := by
    apply (isolatedAt_iff_lonelyAt v k _).2
    intro d hd
    obtain ⟨s,hs,rfl⟩ := mem_disparitySet.mp hd
    change 1/8 ≤ distInt (reading v k s*_)
    by_cases hmem : reading v k s∈({reading v k g,reading v k j,reading v k i} : Finset ℝ)
    · exact hcore _ hmem
    rcases houtside s hs hmem with ⟨hnow,hratio|htie⟩|⟨him,hold,hle⟩|⟨K,hface⟩
    · have hz := Fresh.NativeReturnLevelClearance.captured_ratio_zero hv k _ s i hs hik hnow hret hratio hm3
      exact nonreturning_clear hv k _ _ hm3 s hs hz
    · have hid := handoff_identity hv k s (handoffOpening v k (handoffOpening v k R g) j) hs
      rw [htie] at hid
      exact clear_of_window _ hid.ge (by linarith only [hid])
    · have hfit := rebound_packet_face hwit him hj hjp.le hip.le hle
      have hz := (two_setter_zero_split hv k (handoffOpening v k R g) j i s
        hjk hik hs hwj hm2 hret hm3 hold hfit).2
      exact nonreturning_clear hv k _ _ hm3 s hs hz
    · have hsp : 0 < reading v k s := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨s,hs,rfl⟩)
      have hw := Fresh.NativeClearWitnessArrangement.retained_window (reading v k i) (reading v k j)
        (reading v k s) (handoffOpening v k R g) K hip hjp hsp hwj hret hface
      exact clear_of_window K hw.1 hw.2.le
  exact canonical_of_isolating_move hv k _ _ hUpos hUV hm3 hpoint

theorem class_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : Isolation v k :=
  canonical_isolation (class_into_canonical h)

-- STANDING: DEFINITION
noncomputable def ScaledClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ c : ℝ, 0 < c ∧ Class (fun i=>c*v i) k

theorem scaled_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ScaledClass v k) : Isolation v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact Fresh.ProvedTypesScale.Isolation_smul_of hc (class_isolation hbase)

#print axioms class_into_canonical
#print axioms class_isolation
#print axioms scaled_isolation
end Fresh.NativeClearReboundArrangement
