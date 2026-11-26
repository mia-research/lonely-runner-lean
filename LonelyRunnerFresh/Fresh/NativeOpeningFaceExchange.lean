import Fresh.NativeExcursionEntryInvariance

/-! Two competing native openings exchange their setter across an exact
speed-deformation face. Equality is a common residue-one opening at an
arbitrary positive scale; all other physical readings remain explicit. -/
namespace Fresh.NativeOpeningFaceExchange
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnHandoffArrangement Fresh.FastestCaptureRetention

theorem order_iff_opening_le {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (g : Fin 8) (hg : g≠k) :
    OpeningOrder v k P R g ↔ ∀ i : Fin 8, Survivor v k P R i → handoffOpening v k R i ≤ handoffOpening v k R g := by
  have hgp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  constructor
  · intro ho i hi
    have hip : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi.1,rfl⟩)
    dsimp [handoffOpening,opening]
    apply (div_le_div_iff₀ hip hgp).2
    simpa only [mul_comm] using ho i hi
  · intro ho i hi
    have hip : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi.1,rfl⟩)
    have hh := ho i hi
    dsimp [handoffOpening,opening] at hh
    simpa only [mul_comm] using (div_le_div_iff₀ hip hgp).1 hh

theorem two_candidate_move {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (g h : Fin 8)
    (hg : Survivor v k P R g) (hh : Survivor v k P R h)
    (hrest : ∀ i : Fin 8, Survivor v k P R i → i≠g → i≠h →
      handoffOpening v k R i ≤ max (handoffOpening v k R g) (handoffOpening v k R h)) :
    R < max (handoffOpening v k R g) (handoffOpening v k R h) ∧
      IsMove (disparitySet v k) R (max (handoffOpening v k R g) (handoffOpening v k R h)) := by
  by_cases hgh : handoffOpening v k R g ≤ handoffOpening v k R h
  · rw [max_eq_right hgh]
    apply forced_handoff hv k P R hm h hh
    apply (order_iff_opening_le hv k P R h hh.1).2
    intro i hi
    by_cases hig : i=g
    · subst i; exact hgh
    by_cases hih : i=h
    · subst i; exact le_rfl
    simpa only [max_eq_right hgh] using hrest i hi hig hih
  · have hhg := le_of_lt (lt_of_not_ge hgh)
    rw [max_eq_left hhg]
    apply forced_handoff hv k P R hm g hg
    apply (order_iff_opening_le hv k P R g hg.1).2
    intro i hi
    by_cases hig : i=g
    · subst i; exact le_rfl
    by_cases hih : i=h
    · subst i; exact hhg
    simpa only [max_eq_left hhg] using hrest i hi hig hih

theorem tie_residue_cross (d s T : ℝ) (N K : ℤ)
    (hd : d*T=(N : ℝ)+1/8) (hs : s*T=(K : ℝ)+1/8) :
    d*(8*(K : ℝ)+1)=s*(8*(N : ℝ)+1) := by
  have hh := congrArg (fun x : ℝ=>d*x) hs
  have hh' := congrArg (fun x : ℝ=>s*x) hd
  nlinarith only [hh,hh']

theorem opening_scale (s T : ℝ) (K : ℤ) (hT : 0<T) (hs : s*T=(K : ℝ)+1/8) :
    s=(1/(8*T))*(8*(K : ℝ)+1) := by
  apply (mul_right_cancel₀ hT.ne')
  field_simp
  nlinarith only [hs]

theorem face_order_iff (d T ε : ℝ) (N : ℤ) (hd : 0<d)
    (hface : d*T=(N : ℝ)+1/8+ε) : opening d N ≤ T ↔ 0 ≤ ε := by
  dsimp [opening]
  rw [div_le_iff₀ hd]
  constructor <;> intro hh <;> nlinarith only [hface,hh]

theorem face_order_strict_iff (d T ε : ℝ) (N : ℤ) (hd : 0<d)
    (hface : d*T=(N : ℝ)+1/8+ε) : opening d N<T ↔ 0<ε := by
  dsimp [opening]
  rw [div_lt_iff₀ hd]
  constructor <;> intro hh <;> nlinarith only [hface,hh]

theorem face_order_reverse_iff (d T ε : ℝ) (N : ℤ) (hd : 0<d)
    (hface : d*T=(N : ℝ)+1/8+ε) : T<opening d N ↔ ε<0 := by
  have hh := face_order_iff d T ε N hd hface
  constructor
  · intro h
    by_contra hn
    exact not_lt_of_ge (hh.2 (le_of_not_gt hn)) h
  · intro h
    by_contra hn
    exact not_lt_of_ge (hh.1 (le_of_not_gt hn)) h

#print axioms order_iff_opening_le
#print axioms two_candidate_move
#print axioms tie_residue_cross
#print axioms opening_scale
#print axioms face_order_iff
#print axioms face_order_strict_iff
#print axioms face_order_reverse_iff
end Fresh.NativeOpeningFaceExchange
