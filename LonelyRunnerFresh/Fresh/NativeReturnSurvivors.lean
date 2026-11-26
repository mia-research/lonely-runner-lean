import Fresh.NativeEntryLabels

/-! Unconditional local cascade law: a reading can remain captured after an
actual move only if its canonical entry label advanced. The surviving
capture is exactly a returned reading whose new lower opening is not yet
passed. This describes a move, not a global stopping argument. -/
namespace Fresh.NativeReturnSurvivors
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnCapture

theorem nonreturning_clear {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Q P : ℝ)
    (hm : IsMove (disparitySet v k) Q P) (i : Fin 8) (hi : i≠k)
    (ha : advance |v i-v k| Q P=0) : (1/8 : ℝ) ≤ distInt (|v i-v k| * P) := by
  have hmem : |v i-v k| ∈ disparitySet v k := mem_disparitySet.mpr ⟨i,hi,rfl⟩
  have hs := disparitySet_pos hv k _ hmem
  have hQP := le_of_isMove (disparitySet_pos hv k) hm
  have hlabel := advance_identity |v i-v k| Q P hs.le hQP
  simp only [ha,Nat.cast_zero,add_zero] at hlabel
  have heQ := label_entry |v i-v k| Q
  have heP := label_entry |v i-v k| P
  rw [hlabel] at heP
  have hupper := ((entry_interval _ _ _).1 heP).2
  apply clear_of_window (label (|v i-v k| * Q))
  · rcases heQ with hret|hcap
    · have hinc := mul_le_mul_of_nonneg_left hQP hs.le
      linarith only [hret.1,hinc]
    · have hn : abs (|v i-v k| * Q-(label (|v i-v k| * Q) : ℝ)) < 1/8 := by
        rw [abs_lt]
        constructor <;> linarith only [hcap.1,hcap.2]
      have hw : InWay |v i-v k| Q := lt_of_le_of_lt (Fresh.Cascade.distInt_le _ _) hn
      have ht : nextOpening |v i-v k| Q ≤ P := by
        rcases hm with hfixed|⟨d,hd,hwd,hP,hmax⟩
        · exact (hfixed.1 _ hmem hw).elim
        · exact hmax _ hmem hw
      have he : |v i-v k| * nextOpening |v i-v k| Q=(label (|v i-v k| * Q) : ℝ)+1/8 := by
        rw [nextOpening_eq hn]
        field_simp
      have hh := mul_le_mul_of_nonneg_left ht hs.le
      linarith only [hh,he]
  · exact hupper

theorem captured_implies_return {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Q P : ℝ)
    (hm : IsMove (disparitySet v k) Q P) (i : Fin 8) (hi : i≠k)
    (hw : InWay |v i-v k| P) : 0 < advance |v i-v k| Q P := by
  by_contra hn
  have hz : advance |v i-v k| Q P=0 := by omega
  exact (not_lt.mpr (nonreturning_clear hv k Q P hm i hi hz)) hw

theorem inWay_iff_lower_not_passed (s P : ℝ) :
    InWay s P ↔ s*P < (label (s*P) : ℝ)+1/8 := by
  have he := label_entry s P
  constructor
  · intro hw
    by_contra hn
    have hl : (label (s*P) : ℝ)+1/8 ≤ s*P := le_of_not_gt hn
    have hh := ((entry_interval _ _ _).1 he).2
    exact (not_lt.mpr (clear_of_window _ hl hh)) hw
  · intro hh
    have hl := ((entry_interval _ _ _).1 he).1
    have hn : abs (s*P-(label (s*P) : ℝ)) < 1/8 := by rw [abs_lt]; constructor <;> linarith only [hl,hh]
    exact lt_of_le_of_lt (Fresh.Cascade.distInt_le _ _) hn

theorem capture_iff_returned_lower {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Q P : ℝ)
    (hm : IsMove (disparitySet v k) Q P) (i : Fin 8) (hi : i≠k) :
    InWay |v i-v k| P ↔ 0 < advance |v i-v k| Q P ∧
      |v i-v k| * P < (label (|v i-v k| * P) : ℝ)+1/8 := by
  exact ⟨fun hw=>⟨captured_implies_return hv k Q P hm i hi hw,(inWay_iff_lower_not_passed _ _).1 hw⟩,
    fun h=>(inWay_iff_lower_not_passed _ _).2 h.2⟩

theorem zero_returns_isolated {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Q P : ℝ)
    (hm : IsMove (disparitySet v k) Q P)
    (hz : ∀ i : Fin 8, i≠k → advance |v i-v k| Q P=0) : IsolatedAt v k P := by
  intro i hi
  rw [←Fresh.Localisation.distInt_abs_mul]
  exact nonreturning_clear hv k Q P hm i hi (hz i hi)

theorem crossproduct_capture {v : Fin 8 → ℝ} (hv : IsArrangement v) (k u : Fin 8) (hu : u≠k)
    (Q P : ℝ) (N : ℤ) (hm : IsMove (disparitySet v k) Q P)
    (hopen : |v u-v k| * P=(N : ℝ)+1/8) (i : Fin 8) (hi : i≠k) :
    InWay |v i-v k| P ↔ 0 < advance |v i-v k| Q P ∧
      |v i-v k| * ((N : ℝ)+1/8) < |v u-v k| * ((label (|v i-v k| * P) : ℝ)+1/8) := by
  rw [capture_iff_returned_lower hv k Q P hm i hi]
  have hd : 0 < |v u-v k| := abs_pos.mpr (sub_ne_zero.mpr (fun he=>hu (hv.2 he)))
  have hs := congrArg (fun x : ℝ => |v i-v k| * x) hopen
  constructor
  · intro h
    refine ⟨h.1,?_⟩
    have hh := mul_lt_mul_of_pos_left h.2 hd
    nlinarith only [hh,hs]
  · intro h
    refine ⟨h.1,?_⟩
    nlinarith only [h.2,hs,hd]

#print axioms nonreturning_clear
#print axioms captured_implies_return
#print axioms inWay_iff_lower_not_passed
#print axioms capture_iff_returned_lower
#print axioms zero_returns_isolated
#print axioms crossproduct_capture
end Fresh.NativeReturnSurvivors
