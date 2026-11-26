import Fresh.NativeUpperGridPacket

/-! Exact AP/grid transport of an independently unbounded upper-reader
height at three supplied native boundaries. Its integer period depends on
unbounded entry parameters; it is not a global finite classification. -/
namespace Fresh.NativeUpperGridHeightTransport
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeUpperGridPacket
  Fresh.NativeCoalescedCaptureRelay Fresh.FastestCaptureRetention

def period (K H : ℤ) : ℤ := 64*H*K+7
def numerator (K H : ℤ) : ℤ := 8*H*(8*K+1)+9

theorem opening_ratio (d p V : ℝ) (K H : ℤ) (hd : 0<d) (hp : 0<p)
    (hK : 1 ≤ K) (hdV : d*V=(K : ℝ)) (hpV : p*V=8*(H : ℝ)*(K : ℝ)+7/8) :
    (period K H : ℝ)*labelledOpening p (V+1/(8*d))=(numerator K H : ℝ)*V := by
  have hr := upper_return d p V K H hd hK hdV hpV
  have ho := labelled_opening_identity p (V+1/(8*d)) hp
  rw [hr.2.1] at ho
  have hD : 8*p*V=(period K H : ℝ) := by dsimp [period]; push_cast; nlinarith only [hpV]
  have hB : 8*p*labelledOpening p (V+1/(8*d))=(numerator K H : ℝ) := by
    dsimp [numerator]
    push_cast at ho ⊢
    nlinarith only [ho]
  have h1 := congrArg (fun z : ℝ=>z*labelledOpening p (V+1/(8*d))) hD
  have h2 := congrArg (fun z : ℝ=>z*V) hB
  nlinarith only [h1,h2]

theorem height_shifts (d p q V : ℝ) (K H k : ℤ) (hd : 0<d) (hp : 0<p)
    (hK : 1 ≤ K) (hdV : d*V=(K : ℝ)) (hpV : p*V=8*(H : ℝ)*(K : ℝ)+7/8) :
    (q+8*(k : ℝ)*(period K H : ℝ)*d)*V=q*V+(8*k*K*period K H : ℤ) ∧
    (q+8*(k : ℝ)*(period K H : ℝ)*d)*(V+1/(8*d))=
      q*(V+1/(8*d))+(k*period K H*(8*K+1) : ℤ) ∧
    (q+8*(k : ℝ)*(period K H : ℝ)*d)*labelledOpening p (V+1/(8*d))=
      q*labelledOpening p (V+1/(8*d))+(8*k*K*numerator K H : ℤ) := by
  have hW := Fresh.NativeDoubleGridRecovery.integer_step d V K hd hdV
  have hR := opening_ratio d p V K H hd hp hK hdV hpV
  have hDZ : (period K H : ℝ)*(d*labelledOpening p (V+1/(8*d)))=
      (numerator K H : ℝ)*(K : ℝ) := by
    have h1 := congrArg (fun z : ℝ=>d*z) hR
    have h2 := congrArg (fun z : ℝ=>(numerator K H : ℝ)*z) hdV
    nlinarith only [h1,h2]
  constructor
  · calc
      _ = q*V+8*(k : ℝ)*(period K H : ℝ)*(d*V) := by ring
      _ = _ := by rw [hdV]; push_cast; ring
  constructor
  · calc
      _ = q*(V+1/(8*d))+8*(k : ℝ)*(period K H : ℝ)*(d*(V+1/(8*d))) := by ring
      _ = _ := by rw [hW]; push_cast; ring
  · calc
      _ = q*labelledOpening p (V+1/(8*d))+8*(k : ℝ)*
          ((period K H : ℝ)*(d*labelledOpening p (V+1/(8*d)))) := by ring
      _ = _ := by rw [hDZ]; push_cast; ring

theorem height_labels (d p q V : ℝ) (K H k : ℤ) (hd : 0<d) (hp : 0<p)
    (hK : 1 ≤ K) (hdV : d*V=(K : ℝ)) (hpV : p*V=8*(H : ℝ)*(K : ℝ)+7/8) :
    label ((q+8*(k : ℝ)*(period K H : ℝ)*d)*V)=label (q*V)+8*k*K*period K H ∧
    label ((q+8*(k : ℝ)*(period K H : ℝ)*d)*(V+1/(8*d)))=
      label (q*(V+1/(8*d)))+k*period K H*(8*K+1) ∧
    label ((q+8*(k : ℝ)*(period K H : ℝ)*d)*labelledOpening p (V+1/(8*d)))=
      label (q*labelledOpening p (V+1/(8*d)))+8*k*K*numerator K H := by
  have hh := height_shifts d p q V K H k hd hp hK hdV hpV
  rw [hh.1,hh.2.1,hh.2.2]
  exact ⟨label_add_int _ _,label_add_int _ _,label_add_int _ _⟩

theorem return_difference (d p q V : ℝ) (K H k : ℤ) (hd : 0<d) (hp : 0<p)
    (hK : 1 ≤ K) (hdV : d*V=(K : ℝ)) (hpV : p*V=8*(H : ℝ)*(K : ℝ)+7/8) :
    label ((q+8*(k : ℝ)*(period K H : ℝ)*d)*labelledOpening p (V+1/(8*d)))-
      label ((q+8*(k : ℝ)*(period K H : ℝ)*d)*(V+1/(8*d)))=
    label (q*labelledOpening p (V+1/(8*d)))-label (q*(V+1/(8*d)))+k*(16*K-7) := by
  have hh := height_labels d p q V K H k hd hp hK hdV hpV
  rw [hh.2.1,hh.2.2]
  dsimp [period,numerator]
  ring

#print axioms opening_ratio
#print axioms height_shifts
#print axioms height_labels
#print axioms return_difference
end Fresh.NativeUpperGridHeightTransport
