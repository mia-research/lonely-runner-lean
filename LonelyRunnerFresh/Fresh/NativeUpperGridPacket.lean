import Fresh.NativeDoubleGridRecovery
import Fresh.NativeCoalescedCaptureRelay

/-! Upper-grid returners have equal capture deficits with independent
labels and different own openings. Their slowest reading selects a native
packet opening. All estimates concern this supplied fragment only. -/
namespace Fresh.NativeUpperGridPacket
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeDoubleGridRecovery
  Fresh.NativeCoalescedCaptureRelay Fresh.FastestCaptureRetention

theorem phase_capture_label (q W t : ℝ) (N : ℤ) (ht : 0<t) (ht' : t<1/4)
    (he : q*W=(N : ℝ)-1/8+t) : label (q*W)=N ∧ InWay q W := by
  have hc : (N : ℝ)-1/8<q*W ∧ q*W<(N : ℝ)+1/8 := by
    constructor <;> linarith only [he,ht,ht']
  refine ⟨(entry_iff_label q W N).1 (Or.inr hc),?_⟩
  exact lt_of_le_of_lt (Fresh.Cascade.distInt_le (q*W) N)
    (abs_lt.mpr ⟨by linarith only [hc.1],by linarith only [hc.2]⟩)

theorem upper_return (d q V : ℝ) (K H : ℤ) (hd : 0<d) (hK : 1 ≤ K)
    (hdV : d*V=(K : ℝ)) (hqV : q*V=8*(H : ℝ)*(K : ℝ)+7/8) :
    q*(V+1/(8*d))=(8*H*K+H+1 : ℤ)-1/8+7/(64*(K : ℝ)) ∧
    label (q*(V+1/(8*d)))=8*H*K+H+1 ∧ InWay q (V+1/(8*d)) ∧
    advance q V (V+1/(8*d))=(H+1).toNat := by
  have he := recovery_identity d q V K H 7 hd hK hdV hqV
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have ht : 0<7/(64*(K : ℝ)) := by positivity
  have ht' : 7/(64*(K : ℝ))<1/4 := by
    apply (div_lt_iff₀ (by positivity : 0<64*(K : ℝ))).2
    linarith only [hKr]
  have hp : q*(V+1/(8*d))=(8*H*K+H+1 : ℤ)-1/8+7/(64*(K : ℝ)) := by
    push_cast at he ⊢
    linarith only [he]
  have hh := phase_capture_label q _ _ (8*H*K+H+1) ht ht' hp
  have hentry : label (q*V)=8*H*K := by
    apply (entry_iff_label q V _).1
    apply Or.inl
    push_cast
    constructor <;> linarith only [hqV]
  refine ⟨hp,hh.1,hh.2,?_⟩
  simp only [advance,hentry,hh.1]
  congr 1
  ring

theorem upper_fast (d q V : ℝ) (K H : ℤ) (hd : 0<d) (hK : 1 ≤ K) (hH : 1 ≤ H)
    (hdV : d*V=(K : ℝ)) (hqV : q*V=8*(H : ℝ)*(K : ℝ)+7/8) : 8*d ≤ q := by
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hHr : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hV : 0<V := by nlinarith only [hdV,hd,hKr]
  have hm := mul_le_mul_of_nonneg_right hHr (show 0 ≤ (K : ℝ) by linarith only [hKr])
  nlinarith only [hm,hdV,hqV,hV]

theorem phase_opening (q W t : ℝ) (N : ℤ) (hq : 0<q) (ht : 0<t) (ht' : t<1/4)
    (he : q*W=(N : ℝ)-1/8+t) : labelledOpening q W=W+(1/4-t)/q := by
  have hl := (phase_capture_label q W t N ht ht' he).1
  have ho := labelled_opening_identity q W hq
  rw [hl] at ho
  have hh : labelledOpening q W-W=(1/4-t)/q := by
    apply (eq_div_iff hq.ne').2
    nlinarith only [ho,he]
  linarith only [hh]

theorem packet_order (p q W t : ℝ) (M N : ℤ) (hp : 0<p) (hq : 0<q)
    (ht : 0<t) (ht' : t<1/4) (hpw : p*W=(M : ℝ)-1/8+t)
    (hqw : q*W=(N : ℝ)-1/8+t) (hmin : p ≤ q) :
    labelledOpening q W ≤ labelledOpening p W := by
  rw [phase_opening p W t M hp ht ht' hpw,phase_opening q W t N hq ht ht' hqw]
  have hh : (1/4-t)/q ≤ (1/4-t)/p := div_le_div_of_nonneg_left (by linarith only [ht']) hp hmin
  linarith only [hh]

theorem packet_window (p q W t : ℝ) (M N : ℤ) (hp : 0<p)
    (ht : 0<t) (ht' : t<1/4) (hpw : p*W=(M : ℝ)-1/8+t)
    (hqw : q*W=(N : ℝ)-1/8+t) (hmin : p ≤ q) (hmax : q ≤ 4*p) :
    (N : ℝ)+1/8 ≤ q*labelledOpening p W ∧ q*labelledOpening p W<(N : ℝ)+7/8 := by
  have hcap := (phase_capture_label p W t M ht ht' hpw).2
  have ho := labelled_opening_identity p W hp
  rw [(phase_capture_label p W t M ht ht' hpw).1] at ho
  have hd := (captured_labelled_advance p W hp hcap).1
  have h1 := mul_le_mul_of_nonneg_right hmin hd.le
  have h2 := mul_le_mul_of_nonneg_right hmax hd.le
  constructor <;> nlinarith only [ho,hpw,hqw,h1,h2,ht]

theorem packet_move {ds : Finset ℝ} (hpos : ∀ q∈ds,0<q) (p W t : ℝ)
    (hp : p∈ds) (ht : 0<t) (ht' : t<1/4)
    (hphase : ∀ q∈ds,∃ N : ℤ,q*W=(N : ℝ)-1/8+t)
    (hmin : ∀ q∈ds,p ≤ q) : IsMove ds W (labelledOpening p W) := by
  obtain ⟨M,hpw⟩ := hphase p hp
  have hpp := hpos p hp
  have hc := (phase_capture_label p W t M ht ht' hpw).2
  apply move_of_opening_record hpos W _ (by
    have hh := (captured_labelled_advance p W hpp hc).1
    linarith only [hh])
  · intro q hq
    obtain ⟨N,hqw⟩ := hphase q hq
    exact packet_order p q W t M N hpp (hpos q hq) ht ht' hpw hqw (hmin q hq)
  · exact ⟨p,hp,rfl⟩

-- The two displacements derive the old core's retained clear window.
theorem slow_margin (d p q V : ℝ) (K J : ℤ) (hd : 0<d) (hp : 0<p) (hq : 0 ≤ q)
    (ho : d*V=(K : ℝ)) (hfast : 8*d ≤ p) (hslow : 2*q ≤ d)
    (hcap : InWay p (V+1/(8*d)))
    (hlo : (J : ℝ)+1/8 ≤ q*V) (hhi : q*V ≤ (J : ℝ)+19/24) :
    (J : ℝ)+1/8 ≤ q*labelledOpening p (V+1/(8*d)) ∧
      q*labelledOpening p (V+1/(8*d))<(J : ℝ)+7/8 := by
  have hfirst := integer_step d V K hd ho
  have hlast := captured_labelled_advance p (V+1/(8*d)) hp hcap
  have h1 := mul_le_mul_of_nonneg_right hfast hlast.1.le
  have ht0 : 0<1/(8*d) := by positivity
  have htotal : 0 ≤ labelledOpening p (V+1/(8*d))-V := by linarith only [hlast.1,ht0]
  have h2 := mul_le_mul_of_nonneg_right hslow htotal
  have h3 := mul_nonneg hq htotal
  have hfirst' : d*(1/(8*d))=1/8 := by field_simp
  constructor <;> nlinarith only [h1,hlast.2,h2,h3,hfirst',hlo,hhi]

#print axioms phase_capture_label
#print axioms upper_return
#print axioms upper_fast
#print axioms phase_opening
#print axioms packet_order
#print axioms packet_window
#print axioms packet_move
#print axioms slow_margin
end Fresh.NativeUpperGridPacket
