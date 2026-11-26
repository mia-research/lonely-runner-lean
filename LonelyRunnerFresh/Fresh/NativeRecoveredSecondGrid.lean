import Fresh.NativeRecoveredSecondArrangement

/-! Unbounded integer upper heights force the recovered-second entry
speed faces. The fourth-return capture geometry stays native; terminal
clearance is derived by the physical arrangement theorem. -/
namespace Fresh.NativeRecoveredSecondGrid
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeUpperGridPacket
  Fresh.FastestCaptureRetention

theorem height_speed_faces (q r s V : ℝ) (K A B C : ℤ) (hV : 0<V) (hK : 1 ≤ K)
    (hqV : q*V=8*(A : ℝ)*(K : ℝ)+7/8) (hrV : r*V=8*(B : ℝ)*(K : ℝ)+7/8)
    (hsV : s*V=8*(C : ℝ)*(K : ℝ)+7/8) (hB : 3*A+1 ≤ B) (hC : 3*A ≤ 7*C) :
    3*q<r ∧ 3*q ≤ 7*s := by
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hBcast : 3*(A : ℝ)+1 ≤ (B : ℝ) := by exact_mod_cast hB
  have hBr : (1 : ℝ) ≤ (B : ℝ)-3*(A : ℝ) := by linarith only [hBcast]
  have hCcast : 3*(A : ℝ) ≤ 7*(C : ℝ) := by exact_mod_cast hC
  have hCr : (0 : ℝ) ≤ 7*(C : ℝ)-3*(A : ℝ) := by linarith only [hCcast]
  have h1 := mul_le_mul_of_nonneg_left hBr (show 0 ≤ (K : ℝ) by linarith only [hKr])
  have h2 := mul_nonneg (show 0 ≤ (K : ℝ) by linarith only [hKr]) hCr
  constructor
  · by_contra hn
    have hh := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hV.le
    nlinarith only [hh,hqV,hrV,h1,hKr]
  · by_contra hn
    have hh := mul_pos (sub_pos.mpr (lt_of_not_ge hn)) hV
    nlinarith only [hh,hqV,hsV,h2]

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (V : ℝ) (u a b c e : Fin 8) (K H A B C : ℤ),
    u≠k ∧ a≠k ∧ b≠k ∧ c≠k ∧ e≠k ∧ 1 ≤ K ∧ 1 ≤ H ∧ H ≤ A ∧ H ≤ C ∧
    3*A+1 ≤ B ∧ 3*A ≤ 7*C ∧ reading v k u*V=(K : ℝ) ∧
    reading v k a*V=8*(H : ℝ)*(K : ℝ)+7/8 ∧ reading v k b*V=8*(A : ℝ)*(K : ℝ)+7/8 ∧
    reading v k c*V=8*(B : ℝ)*(K : ℝ)+7/8 ∧ reading v k e*V=8*(C : ℝ)*(K : ℝ)+7/8 ∧
    let W := V+1/(8*reading v k u)
    let Z := labelledOpening (reading v k a) W
    let Y := labelledOpening (reading v k b) Z
    let T := labelledOpening (reading v k c) Y
    let G := labelledOpening (reading v k e) T
    InWay (reading v k b) Z ∧ InWay (reading v k c) Y ∧ InWay (reading v k e) T ∧ InWay (reading v k c) G ∧
    ∀ i : Fin 8,i≠k → reading v k i∉({reading v k u,reading v k a,reading v k b,reading v k c,reading v k e} : Finset ℝ) →
      2*reading v k i ≤ reading v k u ∧ ∃ J : ℤ,(J : ℝ)+1/8 ≤ reading v k i*V ∧ reading v k i*V ≤ (J : ℝ)+3/4

theorem class_into_recovered {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) :
    Fresh.NativeRecoveredSecondArrangement.Class v k := by
  obtain ⟨hv,V,u,a,b,c,e,K,H,A,B,C,hu,ha,hb,hc,he,hK,hH,hHA,hHC,hB,hC,hdV,hpV,hqV,hrV,hsV,hframe⟩ := h
  have hd : 0<reading v k u := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨u,hu,rfl⟩)
  have hr : 0<reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc,rfl⟩)
  have hs : 0<reading v k e := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨e,he,rfl⟩)
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hV : 0<V := by nlinarith only [hdV,hKr,hd]
  have hfast := upper_fast (reading v k u) (reading v k a) V K H hd hK hH hdV hpV
  have hHAr : (H : ℝ) ≤ (A : ℝ) := by exact_mod_cast hHA
  have hHCr : (H : ℝ) ≤ (C : ℝ) := by exact_mod_cast hHC
  have h1 := mul_le_mul_of_nonneg_right hHAr (show 0 ≤ (K : ℝ) by linarith only [hKr])
  have h2 := mul_le_mul_of_nonneg_right hHCr (show 0 ≤ (K : ℝ) by linarith only [hKr])
  have hpq : reading v k a ≤ reading v k b := by nlinarith only [h1,hpV,hqV,hV]
  have hps : reading v k a ≤ reading v k e := by nlinarith only [h2,hpV,hsV,hV]
  have hfaces := height_speed_faces (reading v k b) (reading v k c) (reading v k e) V K A B C hV hK hqV hrV hsV hB hC
  have hfit := simple_seven_three_fit (reading v k c) (reading v k b) (reading v k e) hr hs hfaces.1 hfaces.2
  have ht : 0<7/(64*(K : ℝ)) := by positivity
  have ht' : 7/(64*(K : ℝ))<1/4 := by
    apply (div_lt_iff₀ (by positivity : 0<64*(K : ℝ))).2
    linarith only [hKr]
  have hpW := (upper_return (reading v k u) (reading v k a) V K H hd hK hdV hpV).1
  have hqW := (upper_return (reading v k u) (reading v k b) V K A hd hK hdV hqV).1
  obtain ⟨hqc,hrc,hsc,hret,hslow⟩ := hframe
  exact ⟨hv,V,7/(64*(K : ℝ)),u,a,b,c,e,K,8*H*K+H+1,8*A*K+A+1,
    hu,ha,hb,hc,he,hK,ht,ht',hdV,hfast,hpq,hps,hfit,hpW,hqW,hqc,hrc,hsc,hret,hslow⟩

theorem class_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : Isolation v k :=
  Fresh.NativeRecoveredSecondArrangement.class_isolation (class_into_recovered h)

-- STANDING: DEFINITION
noncomputable def ScaledClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ c : ℝ,0<c ∧ Class (fun i=>c*v i) k

theorem scaled_into_recovered {v : Fin 8 → ℝ} {k : Fin 8} (h : ScaledClass v k) :
    Fresh.NativeRecoveredSecondArrangement.ScaledClass v k := by
  obtain ⟨hv,c,hc,hbase⟩ := h
  exact ⟨hv,c,hc,class_into_recovered hbase⟩

theorem scaled_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ScaledClass v k) : Isolation v k :=
  Fresh.NativeRecoveredSecondArrangement.scaled_isolation (scaled_into_recovered h)

#print axioms height_speed_faces
#print axioms class_into_recovered
#print axioms class_isolation
#print axioms scaled_into_recovered
#print axioms scaled_isolation
end Fresh.NativeRecoveredSecondGrid
