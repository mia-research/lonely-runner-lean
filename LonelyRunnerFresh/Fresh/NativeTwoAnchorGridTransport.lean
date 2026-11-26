import Fresh.NativeFourUpperGrid

/-! Native AP/grid height transport at two explicitly supplied own openings.
Rational anchor numerators determine a parameter-dependent period. Integer
labels and their shifts are unbounded; signed algebra alone is not a claim
of physical admissibility. This source is outside the V80 root/audit. -/
namespace Fresh.NativeTwoAnchorGridTransport
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeUpperGridPacket
  Fresh.NativeCoalescedCaptureRelay Fresh.FastestCaptureRetention

theorem own_ratio (a V E : ℝ) (P Q L : ℤ)
    (hr : (Q : ℝ)*(a*V)=(P : ℝ)) (ho : a*E=(L : ℝ)+1/8) :
    8*(P : ℝ)*E=(Q : ℝ)*(8*(L : ℝ)+1)*V := by
  calc
    _ = 8*((Q : ℝ)*(a*V))*E := by rw [hr]
    _ = (Q : ℝ)*(8*(a*E))*V := by ring
    _ = _ := by rw [ho]; ring

theorem two_anchor_shifts (d a b q V E F : ℝ) (K P Q R S L M k : ℤ)
    (hd : 0<d) (hdV : d*V=(K : ℝ))
    (haV : (Q : ℝ)*(a*V)=(P : ℝ)) (hbV : (S : ℝ)*(b*V)=(R : ℝ))
    (haE : a*E=(L : ℝ)+1/8) (hbF : b*F=(M : ℝ)+1/8) :
    (q+8*(k : ℝ)*(P : ℝ)*(R : ℝ)*d)*V=q*V+(8*k*P*R*K : ℤ) ∧
    (q+8*(k : ℝ)*(P : ℝ)*(R : ℝ)*d)*(V+1/(8*d))=
      q*(V+1/(8*d))+(k*P*R*(8*K+1) : ℤ) ∧
    (q+8*(k : ℝ)*(P : ℝ)*(R : ℝ)*d)*E=q*E+(k*R*Q*K*(8*L+1) : ℤ) ∧
    (q+8*(k : ℝ)*(P : ℝ)*(R : ℝ)*d)*F=q*F+(k*P*S*K*(8*M+1) : ℤ) := by
  have hW := Fresh.NativeDoubleGridRecovery.integer_step d V K hd hdV
  have hE := own_ratio a V E P Q L haV haE
  have hF := own_ratio b V F R S M hbV hbF
  have hDE : 8*(P : ℝ)*(d*E)=(Q : ℝ)*(8*(L : ℝ)+1)*(K : ℝ) := by
    have hh := congrArg (fun x : ℝ=>d*x) hE
    calc
      _ = d*(8*(P : ℝ)*E) := by ring
      _ = d*((Q : ℝ)*(8*(L : ℝ)+1)*V) := hh
      _ = (Q : ℝ)*(8*(L : ℝ)+1)*(d*V) := by ring
      _ = _ := by rw [hdV]
  have hDF : 8*(R : ℝ)*(d*F)=(S : ℝ)*(8*(M : ℝ)+1)*(K : ℝ) := by
    have hh := congrArg (fun x : ℝ=>d*x) hF
    calc
      _ = d*(8*(R : ℝ)*F) := by ring
      _ = d*((S : ℝ)*(8*(M : ℝ)+1)*V) := hh
      _ = (S : ℝ)*(8*(M : ℝ)+1)*(d*V) := by ring
      _ = _ := by rw [hdV]
  constructor
  · calc
      _ = q*V+8*(k : ℝ)*(P : ℝ)*(R : ℝ)*(d*V) := by ring
      _ = _ := by rw [hdV]; push_cast; ring
  constructor
  · calc
      _ = q*(V+1/(8*d))+8*(k : ℝ)*(P : ℝ)*(R : ℝ)*(d*(V+1/(8*d))) := by ring
      _ = _ := by rw [hW]; push_cast; ring
  constructor
  · calc
      _ = q*E+(k : ℝ)*(R : ℝ)*(8*(P : ℝ)*(d*E)) := by ring
      _ = _ := by rw [hDE]; push_cast; ring
  · calc
      _ = q*F+(k : ℝ)*(P : ℝ)*(8*(R : ℝ)*(d*F)) := by ring
      _ = _ := by rw [hDF]; push_cast; ring

theorem two_anchor_labels (d a b q V E F : ℝ) (K P Q R S L M k : ℤ)
    (hd : 0<d) (hdV : d*V=(K : ℝ))
    (haV : (Q : ℝ)*(a*V)=(P : ℝ)) (hbV : (S : ℝ)*(b*V)=(R : ℝ))
    (haE : a*E=(L : ℝ)+1/8) (hbF : b*F=(M : ℝ)+1/8) :
    label ((q+8*(k : ℝ)*(P : ℝ)*(R : ℝ)*d)*V)=label (q*V)+8*k*P*R*K ∧
    label ((q+8*(k : ℝ)*(P : ℝ)*(R : ℝ)*d)*(V+1/(8*d)))=
      label (q*(V+1/(8*d)))+k*P*R*(8*K+1) ∧
    label ((q+8*(k : ℝ)*(P : ℝ)*(R : ℝ)*d)*E)=label (q*E)+k*R*Q*K*(8*L+1) ∧
    label ((q+8*(k : ℝ)*(P : ℝ)*(R : ℝ)*d)*F)=label (q*F)+k*P*S*K*(8*M+1) := by
  have hh := two_anchor_shifts d a b q V E F K P Q R S L M k hd hdV haV hbV haE hbF
  rw [hh.1,hh.2.1,hh.2.2.1,hh.2.2.2]
  exact ⟨label_add_int _ _,label_add_int _ _,label_add_int _ _,label_add_int _ _⟩

theorem return_difference (d a b q V E F : ℝ) (K P Q R S L M k : ℤ)
    (hd : 0<d) (hdV : d*V=(K : ℝ))
    (haV : (Q : ℝ)*(a*V)=(P : ℝ)) (hbV : (S : ℝ)*(b*V)=(R : ℝ))
    (haE : a*E=(L : ℝ)+1/8) (hbF : b*F=(M : ℝ)+1/8) :
    label ((q+8*(k : ℝ)*(P : ℝ)*(R : ℝ)*d)*F)-
      label ((q+8*(k : ℝ)*(P : ℝ)*(R : ℝ)*d)*E)=
    label (q*F)-label (q*E)+k*K*(P*S*(8*M+1)-R*Q*(8*L+1)) := by
  have hh := two_anchor_labels d a b q V E F K P Q R S L M k hd hdV haV hbV haE hbF
  rw [hh.2.2.1,hh.2.2.2]
  ring

#print axioms own_ratio
#print axioms two_anchor_shifts
#print axioms two_anchor_labels
#print axioms return_difference
end Fresh.NativeTwoAnchorGridTransport
