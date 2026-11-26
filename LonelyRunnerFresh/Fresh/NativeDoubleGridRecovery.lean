import Fresh.NativeClearReboundCore
import Fresh.NativeArbitraryThirdReversal

/-! Recovery at a native integer-grid handoff. The two grid labels and
observer return H are independent and unbounded. Core clearance margins
are derived from the supplied captured-opening fragment, not supplied as
terminal guards or a bound on a whole cascade. -/
namespace Fresh.NativeDoubleGridRecovery
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeClearReboundCore
  Fresh.NativeClearWindowRebound Fresh.FastestCaptureRetention Fresh.NativeCoalescedCaptureRelay

-- The next boundary of an integer-phase captured reader.
theorem integer_step (d V : ℝ) (K : ℤ) (hd : 0<d) (ho : d*V=(K : ℝ)) :
    d*(V+1/(8*d))=(K : ℝ)+1/8 := by
  field_simp
  nlinarith only [ho]

-- This is the displacement identity behind independent changed labels.
theorem recovery_identity (d q V : ℝ) (K H : ℤ) (a : ℝ) (hd : 0<d)
    (hK : 1 ≤ K) (hdV : d*V=(K : ℝ))
    (hqV : q*V=8*(H : ℝ)*(K : ℝ)+a/8) :
    q*(V+1/(8*d))=(8*H*K+H : ℤ)+a/8+a/(64*(K : ℝ)) := by
  have hKr : (0 : ℝ)<(K : ℝ) := by exact_mod_cast (show 0<K by omega)
  have hV : V=(K : ℝ)/d := (eq_div_iff hd.ne').2 (by nlinarith only [hdV])
  have hq : q=(8*(H : ℝ)*(K : ℝ)+a/8)*d/(K : ℝ) := by
    apply (eq_div_iff hKr.ne').2
    have hm := congrArg (fun z : ℝ=>d*z) hqV
    have hn := congrArg (fun z : ℝ=>q*z) hdV
    nlinarith only [hm,hn]
  rw [hq,hV]
  push_cast
  field_simp
  ring

theorem recovery_window (d q V : ℝ) (K H : ℤ) (a : ℝ) (hd : 0<d)
    (hK : 1 ≤ K) (hdV : d*V=(K : ℝ)) (ha : 1 ≤ a) (ha' : a ≤ 56/9)
    (hqV : q*V=8*(H : ℝ)*(K : ℝ)+a/8) :
    (8*H*K+H : ℤ)+1/8  ≤  q*(V+1/(8*d)) ∧
      q*(V+1/(8*d))  ≤  (8*H*K+H : ℤ)+7/8 := by
  have he := recovery_identity d q V K H a hd hK hdV hqV
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hden : 0<64*(K : ℝ) := by linarith only [hKr]
  have hdiv0 : 0 ≤ a/(64*(K : ℝ)) := div_nonneg (by linarith only [ha]) hden.le
  have hdiv : a/(64*(K : ℝ)) ≤ a/64 := by
    apply (div_le_iff₀ hden).2
    have hm := mul_le_mul_of_nonneg_left hKr (show 0 ≤ a by linarith only [ha])
    nlinarith only [hm]
  constructor <;> linarith only [he,ha,ha',hdiv0,hdiv]

theorem recovery_labels (d q V : ℝ) (K H : ℤ) (a : ℝ) (hd : 0<d)
    (hK : 1 ≤ K) (hdV : d*V=(K : ℝ)) (ha : 1 ≤ a) (ha' : a ≤ 56/9)
    (hqV : q*V=8*(H : ℝ)*(K : ℝ)+a/8) :
    label (q*V)=8*H*K ∧ label (q*(V+1/(8*d)))=8*H*K+H ∧
      advance q V (V+1/(8*d))=H.toNat := by
  have hw := recovery_window d q V K H a hd hK hdV ha ha' hqV
  have hentry : (8*H*K : ℤ)+1/8  ≤  q*V ∧ q*V ≤ (8*H*K : ℤ)+7/8 := by
    push_cast
    constructor <;> linarith only [hqV,ha,ha']
  have hl1 := (entry_iff_label q V (8*H*K)).1 (Or.inl hentry)
  have hl2 := (entry_iff_label q (V+1/(8*d)) (8*H*K+H)).1 (Or.inl hw)
  refine ⟨hl1,hl2,?_⟩
  simp only [advance,hl1,hl2]
  congr 1
  ring

-- The processed core is earlier in its clear windows than the general
-- endpoint theorem alone records. This margin comes from its two deficits.
theorem core_margin (g j s R : ℝ) (hg : 0<g) (hj : 0<j) (hs : 0<s)
    (hsg : 3*s ≤ 5*g) (hgj : 3*g ≤ 5*j) (hjg : 3*j ≤ 5*g)
    (hwg : InWay g R) (hwj : InWay j (labelledOpening g R)) (hws : InWay s R)
    (horder : labelledOpening s R ≤ labelledOpening g R)
    (hret : InWay s (labelledOpening j (labelledOpening g R))) :
    ∀ q∈({g,j,s} : Finset ℝ), q ≤ s ∧ ∃ J : ℤ,
      (J : ℝ)+1/8 ≤ q*labelledOpening s (labelledOpening j (labelledOpening g R)) ∧
      q*labelledOpening s (labelledOpening j (labelledOpening g R)) ≤ (J : ℝ)+19/24 := by
  have hf := recapture_fast g j s R hg hj hs hsg hgj hjg hwg hwj hws horder hret
  have hy := captured_labelled_advance j (labelledOpening g R) hj hwj
  have hz := captured_labelled_advance s (labelledOpening j (labelledOpening g R)) hs hret
  have h1 := mul_le_mul_of_nonneg_right hgj hy.1.le
  have h2 := mul_le_mul_of_nonneg_right hf.1.le hz.1.le
  have h3 := mul_le_mul_of_nonneg_right hf.2.le hz.1.le
  have hgo := labelled_opening_identity g R hg
  have hjo := labelled_opening_identity j (labelledOpening g R) hj
  have hso := labelled_opening_identity s (labelledOpening j (labelledOpening g R)) hs
  have hfit : g*(j+s) ≤ 3*j*s := by
    have ha := mul_le_mul_of_nonneg_right hgj hs.le
    have hb := mul_le_mul_of_nonneg_right hf.1.le hj.le
    nlinarith only [ha,hb,mul_pos hj hs]
  have hgw := own_two_window j s g (labelledOpening g R) (label (g*R)) hj hs hg hgo hwj hret hfit
  have hjw := own_opening_retained s j (labelledOpening j (labelledOpening g R))
    (labelledOpening s (labelledOpening j (labelledOpening g R)))
    (label (s*labelledOpening j (labelledOpening g R))) (label (j*labelledOpening g R))
    hs hj.le (by linarith only [hf.2,hs]) hjo hret hso rfl
  intro q hq
  simp only [Finset.mem_insert,Finset.mem_singleton] at hq
  rcases hq with hq|hq|hq
  · subst q
    exact ⟨hf.1.le,label (g*R),hgw.1,by nlinarith only [hgo,h1,h2,hy.2,hz.2]⟩
  · subst q
    exact ⟨hf.2.le,label (j*labelledOpening g R),hjw.1,by nlinarith only [hjo,h3,hz.2]⟩
  · subst q
    exact ⟨le_rfl,label (s*labelledOpening j (labelledOpening g R)),hso.ge,by linarith only [hso]⟩

-- A forced ratio and the already-derived native margin discharge the
-- integer setter's core duties; no closing/clearance guard is supplied.
theorem margin_retained (d q V : ℝ) (K J : ℤ) (hd : 0<d) (hq : 0 ≤ q)
    (ho : d*V=(K : ℝ)) (hr : 2*q ≤ d)
    (hlo : (J : ℝ)+1/8 ≤ q*V) (hhi : q*V ≤ (J : ℝ)+19/24) :
    (J : ℝ)+1/8 ≤ q*(V+1/(8*d)) ∧ q*(V+1/(8*d)) ≤ (J : ℝ)+7/8 := by
  have hstep := integer_step d V K hd ho
  have hclose : q*((K : ℝ)+1/8-d*V) ≤ d*((J : ℝ)+7/8-q*V) := by
    have hm := mul_le_mul_of_nonneg_left hhi hd.le
    rw [ho]
    nlinarith only [hm,hr,hd]
  exact Fresh.NativeOpeningRetention.weighted_window d q V (V+1/(8*d)) K J hd hq
    (le_add_of_nonneg_right (by positivity)) hstep hlo hclose

theorem quiet_window (d q V : ℝ) (K : ℤ) (hd : 0<d) (hV : 0<V)
    (hK : 1 ≤ K) (ho : d*V=(K : ℝ)) (hlo : 1/8 ≤ q*V) (hhi : q*V ≤ 1/2) :
    1/8 ≤ q*(V+1/(8*d)) ∧ q*(V+1/(8*d)) ≤ 7/8 := by
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hqp : 0 ≤ q := by nlinarith only [hlo,hV]
  have hr : 2*q ≤ d := by nlinarith only [hhi,ho,hKr,hV]
  simpa using margin_retained d q V K 0 hd hqp ho hr (by simpa using hlo) (by norm_num; linarith only [hhi])

#print axioms integer_step
#print axioms recovery_identity
#print axioms recovery_window
#print axioms recovery_labels
#print axioms core_margin
#print axioms margin_retained
#print axioms quiet_window
end Fresh.NativeDoubleGridRecovery
