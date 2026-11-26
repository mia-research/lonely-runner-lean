import Fresh.NativeSuppliedOpeningGroup

/-! An entry-window face derives retained clearance from the supplied native
3/7 phase law. No terminal clear/closing guard or global time bound is used. -/
namespace Fresh.NativeSuppliedRetainedWindow
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeOneReaderDeformation Fresh.FastestCaptureRetention

-- STANDING: DEFINITION
noncomputable def Face (q c E : ℝ) (J : ℤ) : Prop :=
  (J : ℝ)+1/8 ≤ q*E ∧ 3*q ≤ 7*c*((J : ℝ)+7/8-q*E)

theorem retained_window (q c E F : ℝ) (J : ℤ) (hq : 0 < q) (hc : 0 < c)
    (hEF : E ≤ F) (hphase : c*(F-E) < 3/7) (hface : Face q c E J) :
    (J : ℝ)+1/8 ≤ q*F ∧ q*F < (J : ℝ)+7/8 := by
  have hlo := mul_nonneg hq.le (sub_nonneg.mpr hEF)
  have ht := mul_lt_mul_of_pos_left hphase (show 0 < 7*q by positivity)
  refine ⟨by nlinarith only [hlo,hface.1],?_⟩
  by_contra hn
  have hu := mul_nonneg (show 0 ≤ 7*c by positivity)
    (show 0 ≤ q*F-((J : ℝ)+7/8) by linarith only [hn])
  nlinarith only [ht,hface.2,hu]

theorem retained_segment (q c E F U : ℝ) (J : ℤ) (hq : 0 < q) (hc : 0 < c)
    (hEU : E ≤ U) (hUF : U ≤ F) (hphase : c*(F-E) < 3/7) (hface : Face q c E J) :
    ¬InWay q U ∧ label (q*U)=J := by
  have hw := retained_window q c E F J hq hc (hEU.trans hUF) hphase hface
  have hlo := mul_le_mul_of_nonneg_left hEU hq.le
  have hhi := mul_le_mul_of_nonneg_left hUF hq.le
  have hb : (J : ℝ)+1/8 ≤ q*U ∧ q*U < (J : ℝ)+7/8 := by
    constructor <;> linarith only [hlo,hhi,hface.1,hw.2]
  exact ⟨not_lt.mpr (clear_of_window J hb.1 hb.2.le),
    (entry_iff_label q U J).1 (Or.inl ⟨hb.1,hb.2.le⟩)⟩

theorem retained_zero (q c E F : ℝ) (J : ℤ) (hq : 0 < q) (hc : 0 < c)
    (hEF : E ≤ F) (hphase : c*(F-E) < 3/7) (hface : Face q c E J) :
    advance q E F=0 := by
  have he := (retained_segment q c E F E J hq hc le_rfl hEF hphase hface).2
  have hf := (retained_segment q c E F F J hq hc hEF le_rfl hphase hface).2
  simp only [advance,he,hf,sub_self,Int.toNat_zero]

theorem face_upper_iff (q c E : ℝ) (J : ℤ) (hc : 0 < c) (hE : 0 < E) :
    3*q ≤ 7*c*((J : ℝ)+7/8-q*E) ↔ q ≤ 7*c*((J : ℝ)+7/8)/(3+7*c*E) := by
  have hp : 0 < 3+7*c*E := by positivity
  rw [le_div_iff₀ hp]
  constructor <;> intro h <;> nlinarith only [h]

theorem face_exists_iff (c E : ℝ) (J : ℤ) (hc : 0 < c) (hE : 0 < E) (hJ : 0 ≤ J) :
    (∃ q : ℝ, 0 < q ∧ Face q c E J) ↔ (J : ℝ) ≤ 7*c*E/4-1/8 := by
  have hj : (0 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
  constructor
  · rintro ⟨q,hq,hf⟩
    have h1 := mul_le_mul_of_nonneg_left hf.2 hE.le
    have h2 := mul_le_mul_of_nonneg_left hf.1 (show 0 ≤ 3+7*c*E by positivity)
    nlinarith only [h1,h2]
  · intro h
    let q := ((J : ℝ)+1/8)/E
    have hq : 0 < q := div_pos (by linarith only [hj]) hE
    have hown : q*E=(J : ℝ)+1/8 := by dsimp [q]; field_simp
    refine ⟨q,hq,hown.ge,?_⟩
    have hgap : (J : ℝ)+7/8-q*E=3/4 := by rw [hown]; ring
    rw [hgap]
    by_contra hn
    have hm := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hE
    nlinarith only [hown,h,hm]

theorem own_opening_face_iff (q c E : ℝ) (J : ℤ)
    (ho : q*E=(J : ℝ)+1/8) : Face q c E J ↔ 4*q ≤ 7*c := by
  have hgap : (J : ℝ)+7/8-q*E=3/4 := by rw [ho]; ring
  constructor
  · intro h
    have hh := h.2
    rw [hgap] at hh
    nlinarith only [hh]
  · intro h
    exact ⟨ho.ge,by rw [hgap]; nlinarith only [h]⟩

theorem quiet_face (q c E : ℝ) (hqlo : 1/8 ≤ q) (hqhi : q ≤ 3/8)
    (hc : 7/10 < c) (hElo : 1 ≤ E) (hEhi : E ≤ 5/4) : Face q c E 0 := by
  have hlo := mul_le_mul_of_nonneg_left hElo (show 0 ≤ q by linarith only [hqlo])
  have hhi := mul_le_mul hqhi hEhi (show 0 ≤ E by linarith only [hElo]) (by norm_num : (0 : ℝ) ≤ 3/8)
  have hs := mul_nonneg (show 0 ≤ 7*c by linarith only [hc])
    (show 0 ≤ (7/8 : ℝ)-q*E-13/32 by nlinarith only [hhi])
  constructor <;> norm_num at * <;> nlinarith only [hlo,hqlo,hqhi,hc,hs]

#print axioms retained_window
#print axioms retained_segment
#print axioms retained_zero
#print axioms face_upper_iff
#print axioms face_exists_iff
#print axioms own_opening_face_iff
#print axioms quiet_face
end Fresh.NativeSuppliedRetainedWindow
