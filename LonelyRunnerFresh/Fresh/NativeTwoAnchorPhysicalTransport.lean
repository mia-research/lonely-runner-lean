import Fresh.NativeTwoAnchorGridTransport

/-! Integer grid shifts preserve a supplied isolated point of moving
physical arrangements. Other runner disparities stay fixed; changed
coordinates and all physical admissibility conditions remain explicit.
This transports native witnesses, without preserving earlier full visits. -/
namespace Fresh.NativeTwoAnchorPhysicalTransport
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeCanonicalReturn Fresh.FastestCaptureRetention

theorem integer_positions {v w : Fin 8 → ℝ} (_hv : IsArrangement v) (_hw : IsArrangement w)
    (k : Fin 8) (F : ℝ) (hbase : IsolatedAt w k F)
    (hshift : ∀ i : Fin 8,i≠k → ∃ z : ℤ,reading v k i*F=reading w k i*F+z) :
    IsolatedAt v k F := by
  apply (isolatedAt_iff_lonelyAt v k F).2
  intro x hx
  obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hx
  obtain ⟨z,hz⟩ := hshift i hi
  change 1/8 ≤ distInt (reading v k i*F)
  rw [hz,distInt_add_int]
  exact (isolatedAt_iff_lonelyAt w k F).1 hbase _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)

theorem single_reading {v w : Fin 8 → ℝ} (hv : IsArrangement v) (hw : IsArrangement w)
    (k u : Fin 8) (F delta : ℝ) (z : ℤ) (hbase : IsolatedAt w k F)
    (hother : ∀ i : Fin 8,i≠k → i≠u → reading v k i=reading w k i)
    (hchange : reading v k u=reading w k u+delta) (hdelta : delta*F=(z : ℝ)) :
    IsolatedAt v k F := by
  apply integer_positions hv hw k F hbase
  intro i hi
  by_cases he : i=u
  · subst i
    refine ⟨z,?_⟩
    rw [hchange,add_mul,hdelta]
  · exact ⟨0,by rw [hother i hi he]; simp⟩

theorem two_anchor_point {v w : Fin 8 → ℝ} (hv : IsArrangement v) (hw : IsArrangement w)
    (k u : Fin 8) (d a b V E F : ℝ) (K P Q R S L M j : ℤ)
    (hd : 0<d) (hdV : d*V=(K : ℝ))
    (haV : (Q : ℝ)*(a*V)=(P : ℝ)) (hbV : (S : ℝ)*(b*V)=(R : ℝ))
    (haE : a*E=(L : ℝ)+1/8) (hbF : b*F=(M : ℝ)+1/8)
    (hbase : IsolatedAt w k F)
    (hother : ∀ i : Fin 8,i≠k → i≠u → reading v k i=reading w k i)
    (hchange : reading v k u=reading w k u+8*(j : ℝ)*(P : ℝ)*(R : ℝ)*d) :
    IsolatedAt v k F := by
  have hh := Fresh.NativeTwoAnchorGridTransport.two_anchor_shifts d a b (reading w k u) V E F
    K P Q R S L M j hd hdV haV hbV haE hbF
  apply single_reading hv hw k u F (8*(j : ℝ)*(P : ℝ)*(R : ℝ)*d)
    (j*P*S*K*(8*M+1)) hbase hother hchange
  nlinarith only [hh.2.2.2]

theorem two_anchor_isolation {v w : Fin 8 → ℝ} (hv : IsArrangement v) (hw : IsArrangement w)
    (k u : Fin 8) (d a b V E F : ℝ) (K P Q R S L M j : ℤ)
    (hd : 0<d) (hF : 0<F) (hdV : d*V=(K : ℝ))
    (haV : (Q : ℝ)*(a*V)=(P : ℝ)) (hbV : (S : ℝ)*(b*V)=(R : ℝ))
    (haE : a*E=(L : ℝ)+1/8) (hbF : b*F=(M : ℝ)+1/8)
    (hbase : IsolatedAt w k F)
    (hother : ∀ i : Fin 8,i≠k → i≠u → reading v k i=reading w k i)
    (hchange : reading v k u=reading w k u+8*(j : ℝ)*(P : ℝ)*(R : ℝ)*d) :
    Isolation v k :=
  ⟨F,hF,two_anchor_point hv hw k u d a b V E F K P Q R S L M j hd hdV haV hbV haE hbF hbase hother hchange⟩

theorem independent_points {v w : Fin 8 → ℝ} (hv : IsArrangement v) (hw : IsArrangement w)
    (k : Fin 8) (d a b V E F : ℝ) (K P Q R S L M : ℤ)
    (hd : 0<d) (hdV : d*V=(K : ℝ))
    (haV : (Q : ℝ)*(a*V)=(P : ℝ)) (hbV : (S : ℝ)*(b*V)=(R : ℝ))
    (haE : a*E=(L : ℝ)+1/8) (hbF : b*F=(M : ℝ)+1/8)
    (hbase : IsolatedAt w k F)
    (hchanges : ∀ i : Fin 8,i≠k → ∃ j : ℤ,
      reading v k i=reading w k i+8*(j : ℝ)*(P : ℝ)*(R : ℝ)*d) :
    IsolatedAt v k F := by
  apply integer_positions hv hw k F hbase
  intro i hi
  obtain ⟨j,hj⟩ := hchanges i hi
  have hh := Fresh.NativeTwoAnchorGridTransport.two_anchor_shifts d a b (reading w k i) V E F
    K P Q R S L M j hd hdV haV hbV haE hbF
  exact ⟨j*P*S*K*(8*M+1),by rw [hj]; exact hh.2.2.2⟩

theorem independent_isolation {v w : Fin 8 → ℝ} (hv : IsArrangement v) (hw : IsArrangement w)
    (k : Fin 8) (d a b V E F : ℝ) (K P Q R S L M : ℤ)
    (hd : 0<d) (hF : 0<F) (hdV : d*V=(K : ℝ))
    (haV : (Q : ℝ)*(a*V)=(P : ℝ)) (hbV : (S : ℝ)*(b*V)=(R : ℝ))
    (haE : a*E=(L : ℝ)+1/8) (hbF : b*F=(M : ℝ)+1/8)
    (hbase : IsolatedAt w k F)
    (hchanges : ∀ i : Fin 8,i≠k → ∃ j : ℤ,
      reading v k i=reading w k i+8*(j : ℝ)*(P : ℝ)*(R : ℝ)*d) :
    Isolation v k :=
  ⟨F,hF,independent_points hv hw k d a b V E F K P Q R S L M hd hdV haV hbV haE hbF hbase hchanges⟩

#print axioms independent_points
#print axioms independent_isolation

#print axioms integer_positions
#print axioms single_reading
#print axioms two_anchor_point
#print axioms two_anchor_isolation
end Fresh.NativeTwoAnchorPhysicalTransport
