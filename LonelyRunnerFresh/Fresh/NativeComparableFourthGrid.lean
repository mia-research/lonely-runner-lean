import Fresh.NativeComparableFourthArrangement

/-! Unbounded integer height comparisons force comparable current
readings. A fourth reading lies anywhere between the minimum and both
comparable readings; no terminal clearance or fixed advance is supplied. -/
namespace Fresh.NativeComparableFourthGrid
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeUpperGridPacket
  Fresh.FastestCaptureRetention

theorem height_comparable (q r V : ℝ) (K A B : ℤ) (hV : 0<V) (hK : 1 ≤ K)
    (hqV : q*V=8*(A : ℝ)*(K : ℝ)+7/8) (hrV : r*V=8*(B : ℝ)*(K : ℝ)+7/8)
    (hA : A ≤ 3*B) (hB : B ≤ 3*A) : q ≤ 3*r ∧ r ≤ 3*q := by
  have hKr : (0 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (show 0 ≤ K by omega)
  have hAr : (A : ℝ) ≤ 3*(B : ℝ) := by exact_mod_cast hA
  have hBr : (B : ℝ) ≤ 3*(A : ℝ) := by exact_mod_cast hB
  have h1 := mul_le_mul_of_nonneg_right hAr hKr
  have h2 := mul_le_mul_of_nonneg_right hBr hKr
  constructor
  · by_contra hn
    have hh := mul_pos (sub_pos.mpr (lt_of_not_ge hn)) hV
    nlinarith only [hh,hqV,hrV,h1]
  · by_contra hn
    have hh := mul_pos (sub_pos.mpr (lt_of_not_ge hn)) hV
    nlinarith only [hh,hqV,hrV,h2]

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (V : ℝ) (u a b c e : Fin 8) (K H A B : ℤ),
    u≠k ∧ a≠k ∧ b≠k ∧ c≠k ∧ e≠k ∧ 1 ≤ K ∧ 1 ≤ H ∧ H ≤ A ∧ A ≤ 3*B ∧ B ≤ 3*A ∧
    reading v k u*V=(K : ℝ) ∧ reading v k a*V=8*(H : ℝ)*(K : ℝ)+7/8 ∧
    reading v k b*V=8*(A : ℝ)*(K : ℝ)+7/8 ∧ reading v k c*V=8*(B : ℝ)*(K : ℝ)+7/8 ∧
    reading v k a ≤ reading v k e ∧ reading v k e ≤ reading v k b ∧ reading v k e ≤ reading v k c ∧
    let W := V+1/(8*reading v k u)
    let Z := labelledOpening (reading v k a) W
    let Y := labelledOpening (reading v k b) Z
    InWay (reading v k b) Z ∧ InWay (reading v k c) Y ∧
    ∀ i : Fin 8,i≠k → reading v k i∉({reading v k u,reading v k a,reading v k b,reading v k c,reading v k e} : Finset ℝ) →
      2*reading v k i ≤ reading v k u ∧ ∃ J : ℤ,(J : ℝ)+1/8 ≤ reading v k i*V ∧ reading v k i*V ≤ (J : ℝ)+3/4

theorem class_into_comparable {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) :
    Fresh.NativeComparableFourthArrangement.Class v k := by
  obtain ⟨hv,V,u,a,b,c,e,K,H,A,B,hu,ha,hb,hc,he,hK,hH,hHA,hA,hB,hdV,hpV,hqV,hrV,hps,hsq,hsr,hframe⟩ := h
  have hd : 0<reading v k u := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨u,hu,rfl⟩)
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hV : 0<V := by nlinarith only [hdV,hKr,hd]
  have hfast := upper_fast (reading v k u) (reading v k a) V K H hd hK hH hdV hpV
  have hHAr : (H : ℝ) ≤ (A : ℝ) := by exact_mod_cast hHA
  have hmult := mul_le_mul_of_nonneg_right hHAr (show 0 ≤ (K : ℝ) by linarith only [hKr])
  have hpq : reading v k a ≤ reading v k b := by nlinarith only [hmult,hpV,hqV,hV]
  have hcomp := height_comparable (reading v k b) (reading v k c) V K A B hV hK hqV hrV hA hB
  have ht : 0<7/(64*(K : ℝ)) := by positivity
  have ht' : 7/(64*(K : ℝ))<1/4 := by
    apply (div_lt_iff₀ (by positivity : 0<64*(K : ℝ))).2
    linarith only [hKr]
  have hpW := (upper_return (reading v k u) (reading v k a) V K H hd hK hdV hpV).1
  have hqW := (upper_return (reading v k u) (reading v k b) V K A hd hK hdV hqV).1
  obtain ⟨hqc,hrc,hslow⟩ := hframe
  exact ⟨hv,V,7/(64*(K : ℝ)),u,a,b,c,e,K,8*H*K+H+1,8*A*K+A+1,
    hu,ha,hb,hc,he,hK,ht,ht',hdV,hfast,hpq,hps,hcomp.1,hcomp.2,hsq,hsr,hpW,hqW,hqc,hrc,hslow⟩

theorem class_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : Isolation v k :=
  Fresh.NativeComparableFourthArrangement.class_isolation (class_into_comparable h)

-- STANDING: DEFINITION
noncomputable def ScaledClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ c : ℝ,0<c ∧ Class (fun i=>c*v i) k

theorem scaled_into_comparable {v : Fin 8 → ℝ} {k : Fin 8} (h : ScaledClass v k) :
    Fresh.NativeComparableFourthArrangement.ScaledClass v k := by
  obtain ⟨hv,c,hc,hbase⟩ := h
  exact ⟨hv,c,hc,class_into_comparable hbase⟩

theorem scaled_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ScaledClass v k) : Isolation v k :=
  Fresh.NativeComparableFourthArrangement.scaled_isolation (scaled_into_comparable h)

#print axioms height_comparable
#print axioms class_into_comparable
#print axioms class_isolation
#print axioms scaled_into_comparable
#print axioms scaled_isolation
end Fresh.NativeComparableFourthGrid
