import Fresh.NativeRepeatedReturnLabels

/-! Exact displacement past a supplied current closing boundary.
The excursion keeps arbitrary independent integer advances. Its narrow
lower-face part is capture; the remaining part is recovery. -/
namespace Fresh.NativeReturnExcursion
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnHandoffArrangement Fresh.NativeReturnClosingOrder

noncomputable def excursion (d s R : ℝ) (N K : ℤ) : ℝ :=
  s*((N : ℝ)+1/8-d*R)-d*((K : ℝ)+7/8-s*R)

theorem excursion_identity (d s R T : ℝ) (N K : ℤ)
    (ho : d*T=(N : ℝ)+1/8) :
    excursion d s R N K=d*(s*T-((K : ℝ)+7/8)) := by
  unfold excursion
  have hh := congrArg (fun x : ℝ=>s*x) ho
  nlinarith only [hh]

theorem advance_exact_iff (d s R T : ℝ) (N : ℤ) (a : ℕ)
    (hd : 0<d) (hs : 0 ≤ s) (hRT : R ≤ T) (ho : d*T=(N : ℝ)+1/8) :
    advance s R T=a ↔
      d*((a : ℝ)-1)<excursion d s R N (label (s*R)) ∧
      excursion d s R N (label (s*R)) ≤ d*(a : ℝ) := by
  have hid := advance_identity s R T hs hRT
  have hcast : ((label (s*R)+(a : ℤ) : ℤ) : ℝ)=(label (s*R) : ℝ)+(a : ℝ) := by push_cast; rfl
  have hx := excursion_identity d s R T N (label (s*R)) ho
  constructor
  · intro ha
    rw [ha] at hid
    have hb := (entry_interval s T _).1 (label_entry s T)
    rw [hid,hcast] at hb
    have hl := mul_lt_mul_of_pos_left hb.1 hd
    have hu := mul_le_mul_of_nonneg_left hb.2 hd.le
    constructor <;> nlinarith only [hx,hl,hu]
  · intro hh
    have hb : Fresh.NativeReturnCapture.EntryWindow s T (label (s*R)+(a : ℤ)) := by
      apply (entry_interval _ _ _).2
      rw [hcast]
      constructor <;> nlinarith only [hx,hh.1,hh.2,hd]
    have hl := (entry_iff_label _ _ _).1 hb
    omega

theorem capture_iff_excursion (d s R T : ℝ) (N : ℤ) (a : ℕ)
    (hd : 0<d) (hs : 0 ≤ s) (hRT : R ≤ T) (ho : d*T=(N : ℝ)+1/8)
    (ha : advance s R T=a) :
    InWay s T ↔ excursion d s R N (label (s*R))<d*((a : ℝ)-3/4) := by
  have hid := advance_identity s R T hs hRT
  rw [ha] at hid
  have hx := excursion_identity d s R T N (label (s*R)) ho
  rw [inWay_iff_lower_not_passed,hid]
  push_cast
  constructor <;> intro hh <;> nlinarith only [hx,hh,hd]

theorem clear_iff_excursion (d s R T : ℝ) (N : ℤ) (a : ℕ)
    (hd : 0<d) (hs : 0 ≤ s) (hRT : R ≤ T) (ho : d*T=(N : ℝ)+1/8)
    (ha : advance s R T=a) :
    (1/8 : ℝ) ≤ distInt (s*T) ↔ d*((a : ℝ)-3/4) ≤ excursion d s R N (label (s*R)) := by
  have hh := capture_iff_excursion d s R T N a hd hs hRT ho ha
  exact ⟨fun hc=>le_of_not_gt (fun h=>not_lt_of_ge hc (hh.2 h)),
    fun he=>not_lt.mp (fun h=>not_lt_of_ge he (hh.1 h))⟩

theorem handoff_capture_band {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c) (i : Fin 8) (hi : i≠k) (a : ℕ)
    (ha : advance (reading v k i) R (handoffOpening v k R c)=a) :
    InWay (reading v k i) (handoffOpening v k R c) ↔
      reading v k c*((a : ℝ)-1)<excursion (reading v k c) (reading v k i) R
        (label (reading v k c*R)) (label (reading v k i*R)) ∧
      excursion (reading v k c) (reading v k i) R (label (reading v k c*R)) (label (reading v k i*R))<
        reading v k c*((a : ℝ)-3/4) := by
  have ht := forced_handoff hv k P R hm c hc ho
  have hd : 0<reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc.1,rfl⟩)
  have hs : 0 ≤ reading v k i := abs_nonneg _
  have hopen := handoff_identity hv k c R hc.1
  have hb := (advance_exact_iff _ _ R _ _ a hd hs ht.1.le hopen).1 ha
  have hcap := capture_iff_excursion _ _ R _ _ a hd hs ht.1.le hopen ha
  exact ⟨fun hw=>⟨hb.1,hcap.1 hw⟩,fun hh=>hcap.2 hh.2⟩

#print axioms excursion_identity
#print axioms advance_exact_iff
#print axioms capture_iff_excursion
#print axioms clear_iff_excursion
#print axioms handoff_capture_band
end Fresh.NativeReturnExcursion
