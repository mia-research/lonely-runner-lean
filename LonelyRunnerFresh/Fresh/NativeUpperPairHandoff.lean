import Fresh.NativeUpperGridPacket

/-! An arbitrary second upper reader can cross arbitrarily many labels.
Recapture forces a faster local handoff; the slow duties are derived from
its actual next boundary, with no budget on a full cascade. -/
namespace Fresh.NativeUpperPairHandoff
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeUpperGridPacket
  Fresh.NativeCoalescedCaptureRelay Fresh.FastestCaptureRetention

theorem recapture_fast (p q W t : ℝ) (M N : ℤ) (hp : 0<p)
    (ht : 0<t) (ht' : t<1/4) (hpw : p*W=(M : ℝ)-1/8+t)
    (hqw : q*W=(N : ℝ)-1/8+t) (hmin : p ≤ q)
    (hcap : InWay q (labelledOpening p W)) : 4*p<q := by
  apply lt_of_not_ge
  intro hmax
  have hw := packet_window p q W t M N hp ht ht' hpw hqw hmin hmax
  exact not_lt_of_ge (clear_of_window N hw.1 hw.2.le) hcap

theorem slow_recap_window (d p q s V : ℝ) (J : ℤ)
    (hd : 0<d) (hp : 0<p) (hq : 0<q) (hs : 0 ≤ s)
    (hfirst : 8*d ≤ p) (hsecond : 32*d ≤ q) (hslow : 2*s ≤ d)
    (hpcap : InWay p (V+1/(8*d)))
    (hqcap : InWay q (labelledOpening p (V+1/(8*d))))
    (hlo : (J : ℝ)+1/8 ≤ s*V) (hhi : s*V ≤ (J : ℝ)+19/24) :
    (J : ℝ)+1/8 ≤ s*labelledOpening q (labelledOpening p (V+1/(8*d))) ∧
      s*labelledOpening q (labelledOpening p (V+1/(8*d)))<(J : ℝ)+7/8 := by
  have h1 := captured_labelled_advance p (V+1/(8*d)) hp hpcap
  have h2 := captured_labelled_advance q (labelledOpening p (V+1/(8*d))) hq hqcap
  have h3 := mul_le_mul_of_nonneg_right hfirst h1.1.le
  have h4 := mul_le_mul_of_nonneg_right hsecond h2.1.le
  have ht0 : 0<1/(8*d) := by positivity
  have htotal : 0 ≤ labelledOpening q (labelledOpening p (V+1/(8*d)))-V := by
    linarith only [h1.1,h2.1,ht0]
  have h5 := mul_le_mul_of_nonneg_right hslow htotal
  have h6 := mul_nonneg hs htotal
  have h0 : d*(1/(8*d))=1/8 := by field_simp
  constructor <;> nlinarith only [h3,h4,h5,h6,h0,h1.2,h2.2,hlo,hhi]

-- The already processed p and the integer setter both retain at q's next
-- opening. No assertion about the number of intervening labels is needed.
theorem processed_clear (d p q V : ℝ) (K : ℤ) (hd : 0<d) (hp : 0<p) (hq : 0<q)
    (ho : d*V=(K : ℝ)) (hfirst : 8*d ≤ p) (hsecond : 4*p<q)
    (hpcap : InWay p (V+1/(8*d)))
    (hqcap : InWay q (labelledOpening p (V+1/(8*d)))) :
    LonelyAt ({d,p,q} : Finset ℝ) (labelledOpening q (labelledOpening p (V+1/(8*d)))) := by
  have hdW := Fresh.NativeDoubleGridRecovery.integer_step d V K hd ho
  have hpZ := labelled_opening_identity p (V+1/(8*d)) hp
  have hqY := labelled_opening_identity q (labelledOpening p (V+1/(8*d))) hq
  have hfit : d*(p+q) ≤ 3*p*q := by
    have hdp : d ≤ p := by linarith only [hfirst,hd]
    have hdq : d ≤ q := by linarith only [hfirst,hsecond,hd]
    have h1 := mul_le_mul_of_nonneg_right hdp hq.le
    have h2 := mul_le_mul_of_nonneg_right hdq hp.le
    nlinarith only [h1,h2,mul_pos hp hq]
  have hdclear := Fresh.NativeClearWindowRebound.own_two_window p q d (V+1/(8*d)) K
    hp hq hd hdW hpcap hqcap hfit
  have hpclear := own_opening_retained q p (labelledOpening p (V+1/(8*d)))
    (labelledOpening q (labelledOpening p (V+1/(8*d))))
    (label (q*labelledOpening p (V+1/(8*d)))) (label (p*(V+1/(8*d))))
    hq hp.le (by linarith only [hsecond,hq]) hpZ hqcap hqY rfl
  intro s hs
  simp only [Finset.mem_insert,Finset.mem_singleton] at hs
  rcases hs with rfl|rfl|rfl
  · exact clear_of_window _ hdclear.1 hdclear.2.le
  · exact clear_of_window _ hpclear.1 hpclear.2.le
  · exact clear_of_window _ hqY.ge (by linarith only [hqY])

#print axioms recapture_fast
#print axioms slow_recap_window
#print axioms processed_clear
end Fresh.NativeUpperPairHandoff
