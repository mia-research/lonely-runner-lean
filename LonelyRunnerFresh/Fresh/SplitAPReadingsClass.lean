import Fresh.SplitAPPositive
import Fresh.AdmissibleFlank

/-! Worklist A01/A04, G04–G08/G12. Two same-step AP reading blocks,
with arbitrary positive real offset, a free positive unit, and subject-reading
subsets. The actual reference boundaries are supplied by split_train_positive.
[PROVISIONAL: counting tool] inherited ceiling/opening placements.
[PROVISIONAL: covering] inherited finite middle-parameter splits.
-/
namespace Fresh.SplitAPBands
open Fresh

-- STANDING: DEFINITION
def SplitAPReadingsClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (r : ℕ) (s a : ℝ), 1 ≤ r ∧ r ≤ 5 ∧ 0 < s ∧ 0 < a ∧
    ∀ d ∈ disparitySet v k, ∃ q ∈ splitTrain r a, d = s*q

theorem splitAPReadings_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : SplitAPReadingsClass v k) : Isolation v k := by
  obtain ⟨r,s,a,hr1,hr5,hs,ha,hmem⟩ := h
  obtain ⟨t,ht,hclear⟩ := split_train_positive r hr1 hr5 a ha
  refine ⟨t/s,by positivity,?_⟩
  rw [Fresh.Localisation.isolatedAt_iff]
  intro d hd
  obtain ⟨q,hq,rfl⟩ := hmem d hd
  have he : s*q*(t/s)=q*t := by field_simp
  rw [he]
  exact hclear q hq

theorem translatedSixPositive_imp_splitAP {v : Fin 8 → ℝ} {k : Fin 8}
    (h : Fresh.TranslatedSix.TranslatedSixPositiveClass v k) :
    SplitAPReadingsClass v k := by
  obtain ⟨s,a,hs,ha,hmem⟩ := h
  refine ⟨1,s,a,by omega,by omega,hs,ha,?_⟩
  have he : splitTrain 1 a = Fresh.TranslatedSix.train a := by
    rw [splitTrain_eq_1]
    rfl
  simpa only [he] using hmem

theorem splitAPReadingsClass_smul {c : ℝ} (hc : 0 < c)
    {v : Fin 8 → ℝ} {k : Fin 8} :
    SplitAPReadingsClass (fun j => c*v j) k ↔ SplitAPReadingsClass v k := by
  constructor
  · rintro ⟨r,s,a,hr1,hr5,hs,ha,hmem⟩
    refine ⟨r,s/c,a,hr1,hr5,by positivity,ha,fun d hd => ?_⟩
    obtain ⟨q,hq,he⟩ := hmem (c*d) ((Fresh.AdmissibleFlank.mem_disp_smul hc v k _).2 ⟨d,hd,rfl⟩)
    refine ⟨q,hq,?_⟩
    have hqdiv : s/c*q=(s*q)/c := by ring
    rw [hqdiv,eq_div_iff hc.ne']
    nlinarith
  · rintro ⟨r,s,a,hr1,hr5,hs,ha,hmem⟩
    refine ⟨r,c*s,a,hr1,hr5,by positivity,ha,fun d hd => ?_⟩
    obtain ⟨d0,hd0,rfl⟩ := (Fresh.AdmissibleFlank.mem_disp_smul hc v k _).1 hd
    obtain ⟨q,hq,rfl⟩ := hmem d0 hd0
    exact ⟨q,hq,by ring⟩

#print axioms splitAPReadings_isolation
#print axioms translatedSixPositive_imp_splitAP
#print axioms splitAPReadingsClass_smul
end Fresh.SplitAPBands
