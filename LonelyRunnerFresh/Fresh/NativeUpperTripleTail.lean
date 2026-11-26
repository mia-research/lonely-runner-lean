import Fresh.NativeTightReboundCore
import Fresh.NativeSuppliedOpeningTriple

/-! Three upper readings reuse the native composed-fit triple. The
remaining reader can return more slowly than the second setter. Only this
actual fragment's displacement is used to retain a tighter slow core. -/
namespace Fresh.NativeUpperTripleTail
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.FastestCaptureRetention

theorem slow_tail_window (d p q r s V : ℝ) (J : ℤ)
    (hd : 0 < d) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : 0   ≤   s)
    (hfirst : 8*d   ≤   p) (hsecond : 32*d   ≤   q) (hthird : 8*d   ≤   r) (hslow : 2*s   ≤   d)
    (hpcap : InWay p (V+1/(8*d)))
    (hqcap : InWay q (labelledOpening p (V+1/(8*d))))
    (hrcap : InWay r (labelledOpening q (labelledOpening p (V+1/(8*d)))))
    (hlo : (J : ℝ)+1/8   ≤   s*V) (hhi : s*V   ≤   (J : ℝ)+55/72) :
    (J : ℝ)+1/8   ≤   s*thirdEnd q r (labelledOpening p (V+1/(8*d))) ∧
      s*thirdEnd q r (labelledOpening p (V+1/(8*d))) < (J : ℝ)+7/8 := by
  classical
  let W := V+1/(8*d)
  let Z := labelledOpening p W
  let Y := labelledOpening q Z
  let F := partnerEnd q r Y
  have h1 := captured_labelled_advance p W hp hpcap
  have h2 := captured_labelled_advance q Z hq hqcap
  have h3 := Fresh.NativeSuppliedOpeningTriple.pair_displacement q r Y hq hr hrcap
  have hafter := pair_end_after q r Y hq hr _ (labelled_opening_identity q Z hq) hrcap
  have hiq : d/(4*q)   ≤   1/128 := by
    apply (div_le_iff₀ (by positivity : 0 < 4*q)).2
    nlinarith only [hsecond]
  have hir : d/(4*r)   ≤   1/32 := by
    apply (div_le_iff₀ (by positivity : 0 < 4*r)).2
    nlinarith only [hthird]
  have hscaled := mul_lt_mul_of_pos_left h3 hd
  have htail : d*(F-Y) < 5/128 := by
    have he : d*(1/(4*q)+1/(4*r))=d/(4*q)+d/(4*r) := by ring
    change d*(F-Y) < _ at hscaled
    rw [he] at hscaled
    linarith only [hscaled,hiq,hir]
  have hpstep := mul_le_mul_of_nonneg_right hfirst h1.1.le
  have hqstep := mul_le_mul_of_nonneg_right hsecond h2.1.le
  have h0 : d*(1/(8*d))=1/8 := by field_simp
  have ht0 : 0 < 1/(8*d) := by positivity
  have hFV : 0   ≤   F-V := by
    change Y < F at hafter
    change 0 < Z-W ∧ p*(Z-W) < 1/4 at h1
    change 0 < Y-Z ∧ q*(Y-Z) < 1/4 at h2
    dsimp [W] at h1
    linarith only [hafter,h1.1,h2.1,ht0]
  have hsl := mul_le_mul_of_nonneg_right hslow hFV
  have hnon := mul_nonneg hs hFV
  change (J : ℝ)+1/8   ≤   s*F ∧ s*F < (J : ℝ)+7/8
  change 0 < Z-W ∧ p*(Z-W) < 1/4 at h1
  change 0 < Y-Z ∧ q*(Y-Z) < 1/4 at h2
  change 8*d*(Z-W)   ≤   p*(Z-W) at hpstep
  change 32*d*(Y-Z)   ≤   q*(Y-Z) at hqstep
  dsimp [W] at h1 hpstep
  constructor  <;> nlinarith only [hlo,hhi,hsl,hnon,htail,h0,h1.2,h2.2,hpstep,hqstep]

theorem processed_triple (p q r Z : ℝ) (M : ℤ) (hp : 0<p) (hq : 0<q) (hr : 0<r)
    (hminq : p  ≤  q) (hminr : p  ≤  r) (hown : p*Z=(M : ℝ)+1/8)
    (hcap : InWay q Z) (hreturn : InWay r (labelledOpening q Z)) :
    LonelyAt ({p,q,r} : Finset ℝ) (thirdEnd q r Z) := by
  have hfit := Fresh.NativeThirdReaderRebound.small_old_fit q p r hq hr hminq hminr
  have hclear := triple_clear q p r Z M hq hp hr hown hcap hreturn hfit
  intro s hs
  apply hclear s
  simp only [Finset.mem_insert,Finset.mem_singleton] at hs ⊢
  tauto

theorem integer_tail_window (d p q r V : ℝ) (K : ℤ)
    (hd : 0<d) (hp : 0<p) (hq : 0<q) (hr : 0<r)
    (hfirst : 8*d  ≤  p) (hsecond : 32*d  ≤  q) (hthird : 8*d  ≤  r)
    (hdV : d*V=(K : ℝ)) (hpcap : InWay p (V+1/(8*d)))
    (hqcap : InWay q (labelledOpening p (V+1/(8*d))))
    (hrcap : InWay r (labelledOpening q (labelledOpening p (V+1/(8*d))))) :
    (K : ℝ)+1/8  ≤  d*thirdEnd q r (labelledOpening p (V+1/(8*d))) ∧
      d*thirdEnd q r (labelledOpening p (V+1/(8*d)))<(K : ℝ)+7/8 := by
  classical
  let W := V+1/(8*d)
  let Z := labelledOpening p W
  let Y := labelledOpening q Z
  let F := partnerEnd q r Y
  have h1 := captured_labelled_advance p W hp hpcap
  have h2 := captured_labelled_advance q Z hq hqcap
  have h3 := Fresh.NativeSuppliedOpeningTriple.pair_displacement q r Y hq hr hrcap
  have hafter := pair_end_after q r Y hq hr _ (labelled_opening_identity q Z hq) hrcap
  have hiq : d/(4*q)  ≤  1/128 := by
    apply (div_le_iff₀ (by positivity : 0<4*q)).2
    nlinarith only [hsecond]
  have hir : d/(4*r)  ≤  1/32 := by
    apply (div_le_iff₀ (by positivity : 0<4*r)).2
    nlinarith only [hthird]
  have hscaled := mul_lt_mul_of_pos_left h3 hd
  have htail : d*(F-Y)<5/128 := by
    have he : d*(1/(4*q)+1/(4*r))=d/(4*q)+d/(4*r) := by ring
    change d*(F-Y)<_ at hscaled
    rw [he] at hscaled
    linarith only [hscaled,hiq,hir]
  have hpstep := mul_le_mul_of_nonneg_right hfirst h1.1.le
  have hqstep := mul_le_mul_of_nonneg_right hsecond h2.1.le
  have hown := Fresh.NativeDoubleGridRecovery.integer_step d V K hd hdV
  have hlo := mul_nonneg hd.le (show 0  ≤  F-W by linarith only [hafter,h1.1,h2.1])
  change (K : ℝ)+1/8  ≤  d*F ∧ d*F<(K : ℝ)+7/8
  change d*W=(K : ℝ)+1/8 at hown
  change 0<Z-W ∧ p*(Z-W)<1/4 at h1
  change 0<Y-Z ∧ q*(Y-Z)<1/4 at h2
  change 8*d*(Z-W)  ≤  p*(Z-W) at hpstep
  change 32*d*(Y-Z)  ≤  q*(Y-Z) at hqstep
  constructor <;> nlinarith only [hown,hlo,htail,h1.2,h2.2,hpstep,hqstep]

theorem second_resolution (d p q r V t : ℝ) (K M N : ℤ)
    (hd : 0<d) (hp : 0<p) (hq : 0<q) (hr : 0<r)
    (hfast : 8*d  ≤  p) (hpq : p  ≤  q) (hpr : p  ≤  r) (ht : 0<t) (ht' : t<1/4)
    (hdV : d*V=(K : ℝ))
    (hpW : p*(V+1/(8*d))=(M : ℝ)-1/8+t)
    (hqW : q*(V+1/(8*d))=(N : ℝ)-1/8+t)
    (hcap : InWay q (labelledOpening p (V+1/(8*d)))) :
    ∃ (F z : ℝ) (L : ℤ), z∈({p,q,r} : Finset ℝ) ∧ V<F ∧ z*F=(L : ℝ)+1/8 ∧
      LonelyAt ({d,p,q,r} : Finset ℝ) F ∧
      ∀ (s : ℝ) (J : ℤ),0  ≤  s → 2*s  ≤  d → (J : ℝ)+1/8  ≤  s*V → s*V  ≤  (J : ℝ)+55/72 →
        (J : ℝ)+1/8  ≤  s*F ∧ s*F<(J : ℝ)+7/8 := by
  classical
  let W := V+1/(8*d)
  let Z := labelledOpening p W
  let Y := labelledOpening q Z
  have hphase := Fresh.NativeUpperGridPacket.phase_capture_label p W t M ht ht' hpW
  have hpcap := hphase.2
  have hlarge := Fresh.NativeUpperPairHandoff.recapture_fast p q W t M N hp ht ht' hpW hqW hpq hcap
  have hqfast : 32*d  ≤  q := by linarith only [hfast,hlarge]
  have hrfast : 8*d  ≤  r := hfast.trans hpr
  have hZ := captured_labelled_advance p W hp hpcap
  have hY := captured_labelled_advance q Z hq hcap
  have hWV : 0<1/(8*d) := by positivity
  have hVY : V<Y := by
    change 0<Z-W ∧ _ at hZ
    change 0<Y-Z ∧ _ at hY
    dsimp [W] at hZ
    linarith only [hZ.1,hY.1,hWV]
  by_cases hreturn : InWay r Y
  · let F := thirdEnd q r Z
    have hFafter : Y<F := pair_end_after q r Y hq hr _ (labelled_opening_identity q Z hq) hreturn
    have hprocessed := processed_triple p q r Z (label (p*W)) hp hq hr hpq hpr
      (labelled_opening_identity p W hp) hcap hreturn
    have hint := integer_tail_window d p q r V K hd hp hq hr hfast hqfast hrfast hdV hpcap hcap hreturn
    have hcore : LonelyAt ({d,p,q,r} : Finset ℝ) F := by
      intro s hs
      rcases Finset.mem_insert.mp hs with he|hs
      · subst s; exact clear_of_window K hint.1 hint.2.le
      · exact hprocessed s hs
    have hslow : ∀ (s : ℝ) (J : ℤ),0  ≤  s → 2*s  ≤  d → (J : ℝ)+1/8  ≤  s*V → s*V  ≤  (J : ℝ)+55/72 →
        (J : ℝ)+1/8  ≤  s*F ∧ s*F<(J : ℝ)+7/8 := by
      intro s J hs hsd hlo hhi
      exact slow_tail_window d p q r s V J hd hp hq hr hs hfast hqfast hrfast hsd hpcap hcap hreturn hlo hhi
    by_cases hlast : InWay q (labelledOpening r Y)
    · have he : F=labelledOpening q (labelledOpening r Y) := by
        change (if InWay q (labelledOpening r Y) then _ else _)=_
        rw [if_pos hlast]
      exact ⟨F,q,label (q*labelledOpening r Y),by simp,hVY.trans hFafter,
        he ▸ labelled_opening_identity q (labelledOpening r Y) hq,hcore,hslow⟩
    · have he : F=labelledOpening r Y := by
        change (if InWay q (labelledOpening r Y) then _ else _)=_
        rw [if_neg hlast]
      exact ⟨F,r,label (r*Y),by simp,hVY.trans hFafter,
        he ▸ labelled_opening_identity r Y hr,hcore,hslow⟩
  · have hprocessed := Fresh.NativeUpperPairHandoff.processed_clear d p q V K hd hp hq hdV hfast hlarge hpcap hcap
    refine ⟨Y,q,label (q*Z),by simp,hVY,labelled_opening_identity q Z hq,?_,?_⟩
    · intro s hs
      simp only [Finset.mem_insert,Finset.mem_singleton] at hs
      rcases hs with he|he|he|he
      · subst s; exact hprocessed _ (by simp)
      · subst s; exact hprocessed _ (by simp)
      · subst s; exact hprocessed _ (by simp)
      · subst s; exact not_lt.mp hreturn
    · intro s J hs hsd hlo hhi
      exact Fresh.NativeUpperPairHandoff.slow_recap_window d p q s V J hd hp hq hs hfast hqfast hsd
        hpcap hcap hlo (by linarith only [hhi])

theorem three_resolution (d p q r V t : ℝ) (K M N P : ℤ)
    (hd : 0<d) (hp : 0<p) (hq : 0<q) (hr : 0<r)
    (hfast : 8*d ≤ p) (hpq : p ≤ q) (hpr : p ≤ r) (ht : 0<t) (ht' : t<1/4)
    (hdV : d*V=(K : ℝ))
    (hpW : p*(V+1/(8*d))=(M : ℝ)-1/8+t)
    (hqW : q*(V+1/(8*d))=(N : ℝ)-1/8+t)
    (hrW : r*(V+1/(8*d))=(P : ℝ)-1/8+t) :
    ∃ (F z : ℝ) (L : ℤ), z∈({p,q,r} : Finset ℝ) ∧ V<F ∧ z*F=(L : ℝ)+1/8 ∧
      LonelyAt ({d,p,q,r} : Finset ℝ) F ∧
      ∀ (s : ℝ) (J : ℤ),0 ≤ s → 2*s ≤ d → (J : ℝ)+1/8 ≤ s*V → s*V ≤ (J : ℝ)+55/72 →
        (J : ℝ)+1/8 ≤ s*F ∧ s*F<(J : ℝ)+7/8 := by
  classical
  let W := V+1/(8*d)
  let Z := labelledOpening p W
  by_cases hqcap : InWay q Z
  · exact second_resolution d p q r V t K M N hd hp hq hr hfast hpq hpr ht ht' hdV hpW hqW hqcap
  by_cases hrcap : InWay r Z
  · obtain ⟨F,z,L,hz,hVF,ho,hcore,hslow⟩ := second_resolution d p r q V t K M P hd hp hr hq hfast hpr hpq ht ht' hdV hpW hrW hrcap
    refine ⟨F,z,L,?_,hVF,ho,?_,hslow⟩
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hz ⊢
      tauto
    · intro s hs
      apply hcore s
      simp only [Finset.mem_insert,Finset.mem_singleton] at hs ⊢
      tauto
  have hphase := Fresh.NativeUpperGridPacket.phase_capture_label p W t M ht ht' hpW
  have hpcap := hphase.2
  have hpown := labelled_opening_identity p W hp
  have hstep := captured_labelled_advance p W hp hpcap
  have hWV : 0<1/(8*d) := by positivity
  have hVZ : V<Z := by
    change 0<Z-W ∧ _ at hstep
    dsimp [W] at hstep
    linarith only [hstep.1,hWV]
  refine ⟨Z,p,label (p*W),by simp,hVZ,hpown,?_,?_⟩
  · have hdW := Fresh.NativeDoubleGridRecovery.integer_step d V K hd hdV
    have hdclear := own_opening_retained p d W Z (label (p*W)) K hp hd.le
      (by linarith only [hfast,hp]) hdW hpcap hpown rfl
    intro s hs
    simp only [Finset.mem_insert,Finset.mem_singleton] at hs
    rcases hs with he|he|he|he
    · subst s; exact clear_of_window K hdclear.1 hdclear.2.le
    · subst s; exact clear_of_window _ hpown.ge (by linarith only [hpown])
    · subst s; exact not_lt.mp hqcap
    · subst s; exact not_lt.mp hrcap
  · intro s J hs hsd hlo hhi
    exact Fresh.NativeUpperGridPacket.slow_margin d p s V K J hd hp hs hdV hfast hsd hpcap hlo
      (by linarith only [hhi])

#print axioms three_resolution
#print axioms second_resolution
#print axioms processed_triple
#print axioms integer_tail_window
#print axioms slow_tail_window
end Fresh.NativeUpperTripleTail
