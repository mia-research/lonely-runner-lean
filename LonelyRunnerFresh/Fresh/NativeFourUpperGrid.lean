import Fresh.NativeFourUpperArrangement

/-! Four independent unbounded positive grid heights, in arbitrary order.
Selecting a minimum reading is a finite relabelling of this supplied core;
no global arrangement classification or recurrence inference is made. -/
namespace Fresh.NativeFourUpperGrid
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeUpperGridPacket
  Fresh.FastestCaptureRetention

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (V : ℝ) (u a b c e : Fin 8) (K H A B C : ℤ),
    u≠k ∧ a≠k ∧ b≠k ∧ c≠k ∧ e≠k ∧ 1 ≤ K ∧ 1 ≤ H ∧ 1 ≤ A ∧ 1 ≤ B ∧ 1 ≤ C ∧
    reading v k u*V=(K : ℝ) ∧ reading v k a*V=8*(H : ℝ)*(K : ℝ)+7/8 ∧
    reading v k b*V=8*(A : ℝ)*(K : ℝ)+7/8 ∧ reading v k c*V=8*(B : ℝ)*(K : ℝ)+7/8 ∧
    reading v k e*V=8*(C : ℝ)*(K : ℝ)+7/8 ∧
    ∀ i : Fin 8,i≠k → reading v k i∉({reading v k u,reading v k a,reading v k b,reading v k c,reading v k e} : Finset ℝ) →
      2*reading v k i ≤ reading v k u ∧ ∃ J : ℤ,(J : ℝ)+1/8 ≤ reading v k i*V ∧ reading v k i*V ≤ (J : ℝ)+3/4

theorem class_into_four {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) :
    Fresh.NativeFourUpperArrangement.Class v k := by
  classical
  obtain ⟨hv,V,u,a,b,c,e,K,H,A,B,C,hu,ha,hb,hc,he,hK,hH,hA,hB,hC,hdV,hpV,hqV,hrV,hsV,hslow⟩ := h
  let d := reading v k u
  let p := reading v k a
  let q := reading v k b
  let r := reading v k c
  let s := reading v k e
  have hd : 0<d := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨u,hu,rfl⟩)
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hfP := upper_fast d p V K H hd hK hH hdV hpV
  have hfQ := upper_fast d q V K A hd hK hA hdV hqV
  have hfR := upper_fast d r V K B hd hK hB hdV hrV
  have hfS := upper_fast d s V K C hd hK hC hdV hsV
  have ht : 0<7/(64*(K : ℝ)) := by positivity
  have ht' : 7/(64*(K : ℝ))<1/4 := by
    apply (div_lt_iff₀ (by positivity : 0<64*(K : ℝ))).2
    linarith only [hKr]
  have hpW := (upper_return d p V K H hd hK hdV hpV).1
  have hqW := (upper_return d q V K A hd hK hdV hqV).1
  have hrW := (upper_return d r V K B hd hK hdV hrV).1
  have hsW := (upper_return d s V K C hd hK hdV hsV).1
  let I : Finset ℝ := {p,q,r,s}
  have hI : I.Nonempty := by exact ⟨p,by simp [I]⟩
  let m := I.min' hI
  have hm : m∈I := Finset.min'_mem I hI
  have hbound (x : ℝ) (hx : x∈I) : m ≤ x := Finset.min'_le I x hx
  have hp := hbound p (by simp [I])
  have hq := hbound q (by simp [I])
  have hr := hbound r (by simp [I])
  have hs := hbound s (by simp [I])
  simp only [I,Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with hm|hm|hm|hm
  · rw [hm] at hp hq hr hs
    exact ⟨hv,V,7/(64*(K : ℝ)),u,a,b,c,e,K,8*H*K+H+1,8*A*K+A+1,8*B*K+B+1,8*C*K+C+1,
      hu,ha,hb,hc,he,hK,ht,ht',hdV,hfP,hq,hr,hs,hpW,hqW,hrW,hsW,hslow⟩
  · rw [hm] at hp hq hr hs
    refine ⟨hv,V,7/(64*(K : ℝ)),u,b,a,c,e,K,8*A*K+A+1,8*H*K+H+1,8*B*K+B+1,8*C*K+C+1,
      hu,hb,ha,hc,he,hK,ht,ht',hdV,hfQ,hp,hr,hs,hqW,hpW,hrW,hsW,?_⟩
    intro i hi hm'
    apply hslow i hi
    simpa only [Finset.mem_insert,Finset.mem_singleton,or_comm,or_left_comm,or_assoc] using hm'
  · rw [hm] at hp hq hr hs
    refine ⟨hv,V,7/(64*(K : ℝ)),u,c,a,b,e,K,8*B*K+B+1,8*H*K+H+1,8*A*K+A+1,8*C*K+C+1,
      hu,hc,ha,hb,he,hK,ht,ht',hdV,hfR,hp,hq,hs,hrW,hpW,hqW,hsW,?_⟩
    intro i hi hm'
    apply hslow i hi
    simpa only [Finset.mem_insert,Finset.mem_singleton,or_comm,or_left_comm,or_assoc] using hm'
  · rw [hm] at hp hq hr hs
    refine ⟨hv,V,7/(64*(K : ℝ)),u,e,a,b,c,K,8*C*K+C+1,8*H*K+H+1,8*A*K+A+1,8*B*K+B+1,
      hu,he,ha,hb,hc,hK,ht,ht',hdV,hfS,hp,hq,hr,hsW,hpW,hqW,hrW,?_⟩
    intro i hi hm'
    apply hslow i hi
    simpa only [Finset.mem_insert,Finset.mem_singleton,or_comm,or_left_comm,or_assoc] using hm'

theorem class_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : Isolation v k :=
  Fresh.NativeFourUpperArrangement.class_isolation (class_into_four h)

-- STANDING: DEFINITION
noncomputable def ScaledClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ c : ℝ,0<c ∧ Class (fun i=>c*v i) k

theorem scaled_into_four {v : Fin 8 → ℝ} {k : Fin 8} (h : ScaledClass v k) :
    Fresh.NativeFourUpperArrangement.ScaledClass v k := by
  obtain ⟨hv,c,hc,hbase⟩ := h
  exact ⟨hv,c,hc,class_into_four hbase⟩

theorem scaled_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ScaledClass v k) : Isolation v k :=
  Fresh.NativeFourUpperArrangement.scaled_isolation (scaled_into_four h)

#print axioms class_into_four
#print axioms class_isolation
#print axioms scaled_into_four
#print axioms scaled_isolation
end Fresh.NativeFourUpperGrid
