import Fresh.NativeReturnClosingOrder

/-! One returned disparity group either recovers or forces its common
opening. At that relay, only outsiders can return, and their ORIGINAL
closing order still applies. There is no bound on later reappearances. -/
namespace Fresh.NativeSingleReturnRelay
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnHandoffArrangement Fresh.NativeReturnClosingOrder

noncomputable def SingleReturn (v : Fin 8 → ℝ) (k : Fin 8) (P R : ℝ) (c : Fin 8) : Prop :=
  c≠k ∧ 0 < advance (reading v k c) P R ∧
    ∀ i : Fin 8, i≠k → 0 < advance (reading v k i) P R → reading v k i=reading v k c

noncomputable def SingleClosingEntry (v : Fin 8 → ℝ) (k : Fin 8) (P R : ℝ) (c : Fin 8) : Prop :=
  c≠k ∧ closing (reading v k c) P<R ∧
    ∀ i : Fin 8, i≠k → reading v k i≠reading v k c → R≤closing (reading v k i) P

noncomputable def OriginalFits (v : Fin 8 → ℝ) (k : Fin 8) (P R : ℝ) (c : Fin 8) : Prop :=
  ∀ i : Fin 8, i≠k → reading v k i≠reading v k c →
    handoffOpening v k R c≤closing (reading v k i) P

theorem entry_iff_single {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hPR : P≤R) (c : Fin 8) : SingleClosingEntry v k P R c ↔ SingleReturn v k P R c := by
  constructor
  · intro he
    have hcpos : 0 < reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,he.1,rfl⟩)
    refine ⟨he.1,(positive_iff_closing_passed _ P R hcpos hPR).2 he.2.1,?_⟩
    intro i hi ha
    by_contra hneq
    have hipos : 0 < reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
    exact not_lt_of_ge (he.2.2 i hi hneq) ((positive_iff_closing_passed _ P R hipos hPR).1 ha)
  · intro hs
    have hcpos : 0 < reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hs.1,rfl⟩)
    refine ⟨hs.1,(positive_iff_closing_passed _ P R hcpos hPR).1 hs.2.1,?_⟩
    intro i hi hneq
    have hipos : 0 < reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
    by_contra hn
    exact hneq (hs.2.2 i hi ((positive_iff_closing_passed _ P R hipos hPR).2 (lt_of_not_ge hn)))

theorem outsider_zero {v : Fin 8 → ℝ} (k : Fin 8) (P R : ℝ) (c : Fin 8)
    (hs : SingleReturn v k P R c) (i : Fin 8) (hi : i≠k) (hneq : reading v k i≠reading v k c) :
    advance (reading v k i) P R=0 := by
  by_contra hn
  exact hneq (hs.2.2 i hi (by omega))

theorem outsider_label {v : Fin 8 → ℝ} (k : Fin 8) (P R : ℝ) (hPR : P≤R) (c : Fin 8)
    (hs : SingleReturn v k P R c) (i : Fin 8) (hi : i≠k) (hneq : reading v k i≠reading v k c) :
    label (reading v k i*R)=label (reading v k i*P) := by
  have hid := advance_identity (reading v k i) P R (abs_nonneg _) hPR
  simpa only [outsider_zero k P R c hs i hi hneq,Nat.cast_zero,add_zero] using hid

theorem single_survivors {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hs : SingleReturn v k P R c) (i : Fin 8) :
    Survivor v k P R i ↔ i≠k ∧ reading v k i=reading v k c ∧ InWay (reading v k c) R := by
  constructor
  · intro h
    have he := hs.2.2 i h.1 h.2.1
    exact ⟨h.1,he,by simpa only [he] using ((survivor_iff hv k P R hm i).1 h).2⟩
  · intro h
    apply (survivor_iff hv k P R hm i).2
    exact ⟨h.1,by simpa only [h.2.1] using h.2.2⟩

theorem single_clear_iff_isolated {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hs : SingleReturn v k P R c) :
    ¬InWay (reading v k c) R ↔ IsolatedAt v k R := by
  constructor
  · intro hc i hi
    rw [←Fresh.Localisation.distInt_abs_mul]
    change (1/8 : ℝ) ≤ distInt (reading v k i*R)
    by_cases hsame : reading v k i=reading v k c
    · rw [hsame]
      exact not_lt.mp hc
    · exact nonreturning_clear hv k P R hm i hi (outsider_zero k P R c hs i hi hsame)
  · intro hiso hw
    have hclear := hiso c hs.1
    rw [←Fresh.Localisation.distInt_abs_mul] at hclear
    exact not_lt_of_ge hclear hw

theorem single_relay {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hs : SingleReturn v k P R c)
    (hc : InWay (reading v k c) R) :
    R<handoffOpening v k R c ∧ IsMove (disparitySet v k) R (handoffOpening v k R c) := by
  have hsur : Survivor v k P R c := (survivor_iff hv k P R hm c).2 ⟨hs.1,hc⟩
  exact equal_readings_handoff hv k P R hm c hsur (fun i hi=>hs.2.2 i hi.1 hi.2.1)

theorem single_dichotomy {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hs : SingleReturn v k P R c) :
    IsolatedAt v k R ∨
      (InWay (reading v k c) R ∧ R<handoffOpening v k R c ∧
        IsMove (disparitySet v k) R (handoffOpening v k R c)) := by
  by_cases hc : InWay (reading v k c) R
  · exact Or.inr ⟨hc,single_relay hv k P R hm c hs hc⟩
  · exact Or.inl ((single_clear_iff_isolated hv k P R hm c hs).1 hc)

theorem relay_return_iff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hs : SingleReturn v k P R c)
    (hc : InWay (reading v k c) R) (i : Fin 8) (hi : i≠k) :
    0 < advance (reading v k i) R (handoffOpening v k R c) ↔
      reading v k i≠reading v k c ∧ closing (reading v k i) P<handoffOpening v k R c := by
  have ht := single_relay hv k P R hm c hs hc
  have hsur : Survivor v k P R c := (survivor_iff hv k P R hm c).2 ⟨hs.1,hc⟩
  have hz := handoff_selected_zero hv k P R hm c hsur
  by_cases he : reading v k i=reading v k c
  · rw [he]
    constructor
    · intro ha
      omega
    · intro h
      exact (h.1 rfl).elim
  · have hPR := le_of_isMove (disparitySet_pos hv k) hm
    have hl := outsider_label k P R hPR c hs i hi he
    have hipos : 0 < reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
    rw [positive_iff_closing_passed _ R _ hipos ht.1.le]
    simp only [closing,hl]
    exact ⟨fun h=>⟨he,h⟩,fun h=>h.2⟩

theorem relay_zero_iff_fits {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hs : SingleReturn v k P R c)
    (hc : InWay (reading v k c) R) :
    NoReturnSecond v k R c ↔ OriginalFits v k P R c := by
  constructor
  · intro hz i hi hneq
    by_contra hn
    have ha := (relay_return_iff hv k P R hm c hs hc i hi).2 ⟨hneq,lt_of_not_ge hn⟩
    have he := hz i hi
    omega
  · intro hfit i hi
    by_contra hn
    have ha : 0 < advance (reading v k i) R (handoffOpening v k R c) := by omega
    have hr := (relay_return_iff hv k P R hm c hs hc i hi).1 ha
    exact not_lt_of_ge (hfit i hi hr.1) hr.2

theorem relay_fits_isolated {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hs : SingleReturn v k P R c)
    (hc : InWay (reading v k c) R) (hfit : OriginalFits v k P R c) :
    IsolatedAt v k (handoffOpening v k R c) :=
  zero_returns_isolated hv k R _ (single_relay hv k P R hm c hs hc).2
    ((relay_zero_iff_fits hv k P R hm c hs hc).2 hfit)

#print axioms entry_iff_single
#print axioms outsider_zero
#print axioms outsider_label
#print axioms single_survivors
#print axioms single_clear_iff_isolated
#print axioms single_relay
#print axioms single_dichotomy
#print axioms relay_return_iff
#print axioms relay_zero_iff_fits
#print axioms relay_fits_isolated
end Fresh.NativeSingleReturnRelay
