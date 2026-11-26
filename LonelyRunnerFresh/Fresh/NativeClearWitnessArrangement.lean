import Fresh.NativeClearWindowWitness
import Fresh.NativeWatcherPacketReturn
import Fresh.NativeFixedPrefixArrangement
import Fresh.ProvedTypesScale

/-! A persistent clear-window packet resolves two actual selected openings.
Packet membership in the two captured entries discharges the packet; native
entry faces retain all other readers. No endpoint-clear guard is assumed. -/
namespace Fresh.NativeClearWitnessArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeCanonicalReturn
  Fresh.NativeFixedPrefixArrangement Fresh.NativeClearWindowWitness Fresh.FastestCaptureRetention
  Fresh.NativeOneReaderDeformation

-- STANDING: DEFINITION
noncomputable def Face (q d g R : ℝ) (K : ℤ) : Prop :=
  (K : ℝ)+1/8 ≤ q*R ∧ q*(d+g) ≤ 4*d*g*((K : ℝ)+7/8-q*R)

theorem retained_window (d g q R : ℝ) (K : ℤ) (hd : 0 < d) (hg : 0 < g) (hq : 0 < q)
    (hw : InWay g R) (hret : InWay d (labelledOpening g R)) (hf : Face q d g R K) :
    (K : ℝ)+1/8 ≤ q*Fresh.NativeWatcherPacketReturn.returnOpening d g R ∧
      q*Fresh.NativeWatcherPacketReturn.returnOpening d g R < (K : ℝ)+7/8 := by
  have ht := Fresh.NativeWatcherPacketReturn.two_opening_displacement d g R hd hg hw hret
  have hstep := mul_nonneg hq.le (sub_nonneg.mpr (ht.1.le.trans ht.2.1.le))
  have hs := mul_lt_mul_of_pos_left ht.2.2 (show 0 < 4*q by positivity)
  refine ⟨by nlinarith only [hf.1,hstep],?_⟩
  by_contra hn
  have hu := mul_nonneg (show 0 ≤ 4*d*g by positivity)
    (show 0 ≤ q*Fresh.NativeWatcherPacketReturn.returnOpening d g R-((K : ℝ)+7/8) by linarith only [hn])
  nlinarith only [hs,hf.2,hu]

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (P R : ℝ) (I : Finset (Fin 8)) (N : ℤ) (g j : Fin 8),
    Witness v k P I N ∧ 2 ≤ N ∧ 0 < R ∧ P ≤ R ∧ g∈I ∧ j∈I ∧
    InWay (reading v k g) R ∧ IsMove (disparitySet v k) R (handoffOpening v k R g) ∧
    InWay (reading v k j) (handoffOpening v k R g) ∧
    IsMove (disparitySet v k) (handoffOpening v k R g) (handoffOpening v k (handoffOpening v k R g) j) ∧
    ∀ i : Fin 8, i≠k →
      (i∈I ∧ (InWay (reading v k i) R ∨ InWay (reading v k i) (handoffOpening v k R g))) ∨
      ∃ K : ℤ, Face (reading v k i) (reading v k j) (reading v k g) R K

theorem class_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : CanonicalReturnClass v k := by
  obtain ⟨hv,P,R,I,N,g,j,hwit,hN,hR,_hPR,hg,hj,hwg,hm1,hwj,hm2,hmembers⟩ := h
  have hgk : g≠k := (Finset.mem_erase.mp (hwit.2.1 hg)).1
  have hjk : j≠k := (Finset.mem_erase.mp (hwit.2.1 hj)).1
  have hgp := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hgk,rfl⟩)
  have hjp := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨j,hjk,rfl⟩)
  have hTpos : 0 < handoffOpening v k R g := hR.trans_le (le_of_isMove (disparitySet_pos hv k) hm1)
  have hTU : handoffOpening v k R g < handoffOpening v k (handoffOpening v k R g) j := by
    change 0 < reading v k j at hjp
    have ht := lt_nextOpening hjp hwj
    rw [next_at_label _ _ hwj] at ht
    exact ht
  have hpoint : IsolatedAt v k (handoffOpening v k (handoffOpening v k R g) j) := by
    apply (isolatedAt_iff_lonelyAt v k _).2
    intro d hd
    obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hd
    change 1/8 ≤ distInt (reading v k i*_)
    rcases hmembers i hi with ⟨him,hold|hnow⟩|⟨K,hf⟩
    · apply not_lt.mp
      intro hafter
      exact (two_capture_fresh hv k P R I N hwit hN g j i hg hj him hwg hm1 hwj hm2 hafter).1 hold
    · exact not_lt.mp (member_clear hv k P _ I N hwit j hj hwj hm2 i him hnow)
    · have hip := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
      have hw := retained_window (reading v k j) (reading v k g) (reading v k i) R K hjp hgp hip hwg hwj hf
      exact clear_of_window K hw.1 hw.2.le
  exact canonical_of_isolating_move hv k _ _ hTpos hTU hm2 hpoint

theorem class_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : Isolation v k :=
  canonical_isolation (class_into_canonical h)

-- STANDING: DEFINITION
noncomputable def ScaledClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ c : ℝ, 0 < c ∧ Class (fun i=>c*v i) k

theorem scaled_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ScaledClass v k) : Isolation v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact Fresh.ProvedTypesScale.Isolation_smul_of hc (class_isolation hbase)

#print axioms retained_window
#print axioms class_into_canonical
#print axioms class_isolation
#print axioms scaled_isolation
end Fresh.NativeClearWitnessArrangement
