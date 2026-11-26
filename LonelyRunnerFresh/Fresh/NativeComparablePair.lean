import Fresh.NativeHierarchicalFourthGrid

/-! Current comparable captures resolve by their native ordered openings.
A previously clear partner is tested again before its opening is formed.
No common labels, shared own opening or global advance bound is assumed. -/
namespace Fresh.NativeComparablePair
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.FastestCaptureRetention

theorem captured_at_selected (a b G : ℝ) (ha : 0<a) (hb : 0<b)
    (hac : InWay a G) (hbc : InWay b G) (hba : b ≤ 3*a)
    (horder : labelledOpening b G ≤ labelledOpening a G) :
    (label (b*G) : ℝ)+1/8 ≤ b*labelledOpening a G ∧
      b*labelledOpening a G<(label (b*G) : ℝ)+7/8 := by
  have hoA := labelled_opening_identity a G ha
  have hoB := labelled_opening_identity b G hb
  have h1 := congrArg (fun x : ℝ=>a*x) hoB
  have h2 := congrArg (fun x : ℝ=>b*x) hoA
  have hm := mul_le_mul_of_nonneg_left horder (mul_pos ha hb).le
  have hc := capture_at_label a G hac
  exact Fresh.NativeRelativeCapture.captured_window a b G _ _ _ ha hba hoA hc.1 hc.2
    (capture_at_label b G hbc).2 (by nlinarith only [h1,h2,hm])

theorem selected_move (a b G : ℝ) (hac : InWay a G)
    (hmax : InWay b G → labelledOpening b G ≤ labelledOpening a G) :
    IsMove ({a,b} : Finset ℝ) G (labelledOpening a G) := by
  refine Or.inr ⟨a,by simp,hac,(captured_opening a G hac).symm,?_⟩
  intro x hx hxc
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with hx|hx
  · subst x; rw [captured_opening a G hac]
  · subst x; rw [captured_opening b G hxc]; exact hmax hxc

theorem selected_resolution (a b G : ℝ) (ha : 0<a) (hb : 0<b)
    (hab : a ≤ 3*b) (hac : InWay a G)
    (hmax : InWay b G → labelledOpening b G ≤ labelledOpening a G) :
    ∃ F : ℝ,G<F ∧ LonelyAt ({a,b} : Finset ℝ) F ∧ F-G<1/(4*a)+1/(4*b) ∧
      (∃ U,G ≤ U ∧ U<F ∧ IsMove ({a,b} : Finset ℝ) U F) ∧
      ∀ (s : ℝ) (J : ℤ),0<s → s ≤ a → s ≤ b → s*G=(J : ℝ)+1/8 →
        (J : ℝ)+1/8 ≤ s*F ∧ s*F<(J : ℝ)+7/8 := by
  let H := labelledOpening a G
  have hH := labelled_opening_identity a G ha
  have h1 := captured_labelled_advance a G ha hac
  have ht1 := Fresh.NativeSuppliedOpeningTriple.opening_displacement a G ha hac
  have hi : 0<1/(4*b) := by positivity
  by_cases hret : InWay b H
  · have h2 := captured_labelled_advance b H hb hret
    have ht2 := Fresh.NativeSuppliedOpeningTriple.opening_displacement b H hb hret
    have hF := labelled_opening_identity b H hb
    have haF := own_opening_retained b a H (labelledOpening b H) (label (b*H)) (label (a*G)) hb ha.le hab hH hret hF rfl
    have hcore : LonelyAt ({a,b} : Finset ℝ) (labelledOpening b H) := by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with hx|hx
      · subst x; exact clear_of_window _ haF.1 haF.2.le
      · subst x; exact clear_of_window _ hF.ge (by linarith only [hF])
    have hm := pair_first_move a b H (label (a*G)) ha hb hH hret
    refine ⟨labelledOpening b H,by linarith only [h1.1,h2.1],hcore,by linarith only [ht1,ht2],⟨H,by linarith only [h1.1],by linarith only [h2.1],hm⟩,?_⟩
    intro s J hs hsa hsb ho
    have hfit : s*(a+b) ≤ 3*a*b := by
      have hf1 := mul_le_mul_of_nonneg_right hsa hb.le
      have hf2 := mul_le_mul_of_nonneg_right hsb ha.le
      nlinarith only [hf1,hf2,mul_pos ha hb]
    exact Fresh.NativeClearWindowRebound.own_two_window a b s G J ha hb hs ho hac hret hfit
  · have hcore : LonelyAt ({a,b} : Finset ℝ) H := by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with hx|hx
      · subst x; exact clear_of_window _ hH.ge (by linarith only [hH])
      · subst x; exact not_lt.mp hret
    refine ⟨H,by linarith only [h1.1],hcore,by linarith only [ht1,hi],⟨G,le_rfl,by linarith only [h1.1],selected_move a b G hac hmax⟩,?_⟩
    intro s J hs hsa hsb ho
    exact own_opening_retained a s G H (label (a*G)) J ha hs.le
      (by linarith only [hsa,ha]) ho hac hH rfl

-- In the two-capture branch the selected order rules out the fresh-return
-- branch; the general selected lemma also retains all initially-clear cases.
theorem resolution (a b G : ℝ) (ha : 0<a) (hb : 0<b) (hab : a ≤ 3*b) (hba : b ≤ 3*a) :
    ∃ F : ℝ,G ≤ F ∧ LonelyAt ({a,b} : Finset ℝ) F ∧ F-G<1/(4*a)+1/(4*b) ∧
      (F=G ∨ ∃ U,G ≤ U ∧ U<F ∧ IsMove ({a,b} : Finset ℝ) U F) ∧
      ∀ (s : ℝ) (J : ℤ),0<s → s ≤ a → s ≤ b → s*G=(J : ℝ)+1/8 →
        (J : ℝ)+1/8 ≤ s*F ∧ s*F<(J : ℝ)+7/8 := by
  classical
  by_cases hac : InWay a G
  · by_cases hbc : InWay b G
    · by_cases ho : labelledOpening b G ≤ labelledOpening a G
      · obtain ⟨F,hGF,hc,hd,hm,hs⟩ := selected_resolution a b G ha hb hab hac (fun _=>ho)
        exact ⟨F,hGF.le,hc,hd,Or.inr hm,hs⟩
      · obtain ⟨F,hGF,hc,hd,hm,hs⟩ := selected_resolution b a G hb ha hba hbc (fun _=>(lt_of_not_ge ho).le)
        refine ⟨F,hGF.le,?_,by linarith only [hd],?_,?_⟩
        · simpa only [Finset.pair_comm] using hc
        · exact Or.inr (by simpa only [Finset.pair_comm] using hm)
        · intro s J hp hsa hsb hsG; exact hs s J hp hsb hsa hsG
    · obtain ⟨F,hGF,hc,hd,hm,hs⟩ := selected_resolution a b G ha hb hab hac (fun hw=>(hbc hw).elim)
      exact ⟨F,hGF.le,hc,hd,Or.inr hm,hs⟩
  · by_cases hbc : InWay b G
    · obtain ⟨F,hGF,hc,hd,hm,hs⟩ := selected_resolution b a G hb ha hba hbc (fun hw=>(hac hw).elim)
      refine ⟨F,hGF.le,?_,by linarith only [hd],?_,?_⟩
      · simpa only [Finset.pair_comm] using hc
      · exact Or.inr (by simpa only [Finset.pair_comm] using hm)
      · intro s J hp hsa hsb hsG; exact hs s J hp hsb hsa hsG
    · have haI : 0<(1 : ℝ)/(4*a) := by positivity
      have hbI : 0<(1 : ℝ)/(4*b) := by positivity
      refine ⟨G,le_rfl,?_,by linarith only [haI,hbI],Or.inl rfl,?_⟩
      · intro x hx
        simp only [Finset.mem_insert,Finset.mem_singleton] at hx
        rcases hx with hx|hx
        · subst x; exact not_lt.mp hac
        · subst x; exact not_lt.mp hbc
      · intro s J hp hsa hsb hsG
        exact ⟨hsG.ge,by linarith only [hsG]⟩

#print axioms captured_at_selected
#print axioms selected_move
#print axioms selected_resolution
#print axioms resolution
end Fresh.NativeComparablePair
