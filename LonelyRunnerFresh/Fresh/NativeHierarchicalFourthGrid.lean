import Fresh.NativeHierarchicalFourthArrangement

/-! An unbounded three-reader upper grid and an arbitrary fourth reading.
One integer height separation forces the fast-third premise. No fourth
phase, fourth capture, seven-three face or terminal guard is supplied. -/
namespace Fresh.NativeHierarchicalFourthGrid
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeUpperGridPacket
  Fresh.FastestCaptureRetention

theorem height_fast (q r V : ℝ) (K A B : ℤ) (hV : 0<V) (hK : 1 ≤ K)
    (hqV : q*V=8*(A : ℝ)*(K : ℝ)+7/8) (hrV : r*V=8*(B : ℝ)*(K : ℝ)+7/8)
    (hB : 3*A+1 ≤ B) : 3*q<r := by
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hBr : 3*(A : ℝ)+1 ≤ (B : ℝ) := by exact_mod_cast hB
  have hh := mul_nonneg (show 0 ≤ (K : ℝ) by linarith only [hKr])
    (show 0 ≤ (B : ℝ)-3*(A : ℝ)-1 by linarith only [hBr])
  by_contra hn
  have hb := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hV.le
  nlinarith only [hb,hqV,hrV,hh,hKr]

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (V : ℝ) (u a b c e : Fin 8) (K H A B : ℤ),
    u≠k ∧ a≠k ∧ b≠k ∧ c≠k ∧ e≠k ∧ 1 ≤ K ∧ 1 ≤ H ∧ H ≤ A ∧ 3*A+1 ≤ B ∧
    reading v k u*V=(K : ℝ) ∧ reading v k a*V=8*(H : ℝ)*(K : ℝ)+7/8 ∧
    reading v k b*V=8*(A : ℝ)*(K : ℝ)+7/8 ∧ reading v k c*V=8*(B : ℝ)*(K : ℝ)+7/8 ∧
    reading v k a ≤ reading v k e ∧
    let W := V+1/(8*reading v k u)
    let Z := labelledOpening (reading v k a) W
    let Y := labelledOpening (reading v k b) Z
    InWay (reading v k b) Z ∧ InWay (reading v k c) Y ∧
    ∀ i : Fin 8,i≠k → reading v k i∉({reading v k u,reading v k a,reading v k b,reading v k c,reading v k e} : Finset ℝ) →
      2*reading v k i ≤ reading v k u ∧ ∃ J : ℤ,(J : ℝ)+1/8 ≤ reading v k i*V ∧ reading v k i*V ≤ (J : ℝ)+3/4

theorem class_into_hierarchical {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) :
    Fresh.NativeHierarchicalFourthArrangement.Class v k := by
  obtain ⟨hv,V,u,a,b,c,e,K,H,A,B,hu,ha,hb,hc,he,hK,hH,hHA,hB,hdV,hpV,hqV,hrV,hps,hframe⟩ := h
  have hd : 0<reading v k u := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨u,hu,rfl⟩)
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hV : 0<V := by nlinarith only [hdV,hKr,hd]
  have hfast := upper_fast (reading v k u) (reading v k a) V K H hd hK hH hdV hpV
  have hHAr : (H : ℝ) ≤ (A : ℝ) := by exact_mod_cast hHA
  have hmult := mul_le_mul_of_nonneg_right hHAr (show 0 ≤ (K : ℝ) by linarith only [hKr])
  have hpq : reading v k a ≤ reading v k b := by nlinarith only [hmult,hpV,hqV,hV]
  have hqr := height_fast (reading v k b) (reading v k c) V K A B hV hK hqV hrV hB
  have ht : 0<7/(64*(K : ℝ)) := by positivity
  have ht' : 7/(64*(K : ℝ))<1/4 := by
    apply (div_lt_iff₀ (by positivity : 0<64*(K : ℝ))).2
    linarith only [hKr]
  have hpW := (upper_return (reading v k u) (reading v k a) V K H hd hK hdV hpV).1
  have hqW := (upper_return (reading v k u) (reading v k b) V K A hd hK hdV hqV).1
  obtain ⟨hqc,hrc,hslow⟩ := hframe
  exact ⟨hv,V,7/(64*(K : ℝ)),u,a,b,c,e,K,8*H*K+H+1,8*A*K+A+1,
    hu,ha,hb,hc,he,hK,ht,ht',hdV,hfast,hpq,hps,hqr,hpW,hqW,hqc,hrc,hslow⟩

theorem class_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : Isolation v k :=
  Fresh.NativeHierarchicalFourthArrangement.class_isolation (class_into_hierarchical h)

-- STANDING: DEFINITION
noncomputable def ScaledClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ c : ℝ,0<c ∧ Class (fun i=>c*v i) k

theorem scaled_into_hierarchical {v : Fin 8 → ℝ} {k : Fin 8} (h : ScaledClass v k) :
    Fresh.NativeHierarchicalFourthArrangement.ScaledClass v k := by
  obtain ⟨hv,c,hc,hbase⟩ := h
  exact ⟨hv,c,hc,class_into_hierarchical hbase⟩

theorem scaled_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ScaledClass v k) : Isolation v k :=
  Fresh.NativeHierarchicalFourthArrangement.scaled_isolation (scaled_into_hierarchical h)

#print axioms height_fast
#print axioms class_into_hierarchical
#print axioms class_isolation
#print axioms scaled_into_hierarchical
#print axioms scaled_isolation
end Fresh.NativeHierarchicalFourthGrid
