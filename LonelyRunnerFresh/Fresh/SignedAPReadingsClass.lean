import Fresh.SignedSplitAPAll
import Fresh.AdmissibleFlank

/-! Subject-reading class for two AP blocks that may straddle the subject.
Only disparities are represented by absolute signed packet entries; all physical
speeds retain their original roles. [PROVISIONAL: counting tool] inherited
integer grid placement; [PROVISIONAL: covering] finite middle strip splits.
-/
namespace Fresh.SplitAPBands
open Fresh

-- STANDING: DEFINITION
def SignedAPReadingsClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (r : ℕ) (s B : ℝ), 1 ≤ r ∧ r ≤ 5 ∧ 0 < s ∧
    (∀ m : ℤ, B ≠ (m : ℝ)) ∧
    ∀ d ∈ disparitySet v k, ∃ q ∈ splitTrain r B, d = s* |q|

theorem signedAPReadings_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : SignedAPReadingsClass v k) : Isolation v k := by
  obtain ⟨r,s,B,hr1,hr5,hs,hB,hmem⟩ := h
  obtain ⟨t,ht,hclear⟩ := signed_split_train_noninteger r hr1 hr5 B hB
  refine ⟨t/s,by positivity,?_⟩
  rw [Fresh.Localisation.isolatedAt_iff]
  intro d hd
  obtain ⟨q,hq,rfl⟩ := hmem d hd
  have he : s* |q| *(t/s)=|q| *t := by field_simp
  rw [he,Fresh.Localisation.distInt_abs_mul]
  exact hclear q hq

theorem signedAPReadingsClass_smul {c : ℝ} (hc : 0<c)
    {v : Fin 8 → ℝ} {k : Fin 8} :
    SignedAPReadingsClass (fun j => c*v j) k ↔ SignedAPReadingsClass v k := by
  constructor
  · rintro ⟨r,s,B,hr1,hr5,hs,hB,hmem⟩
    refine ⟨r,s/c,B,hr1,hr5,by positivity,hB,fun d hd => ?_⟩
    obtain ⟨q,hq,he⟩ := hmem (c*d) ((Fresh.AdmissibleFlank.mem_disp_smul hc v k _).2 ⟨d,hd,rfl⟩)
    refine ⟨q,hq,?_⟩
    have hqdiv : s/c* |q|=(s* |q|)/c := by ring
    rw [hqdiv,eq_div_iff hc.ne']
    nlinarith
  · rintro ⟨r,s,B,hr1,hr5,hs,hB,hmem⟩
    refine ⟨r,c*s,B,hr1,hr5,by positivity,hB,fun d hd => ?_⟩
    obtain ⟨d0,hd0,rfl⟩ := (Fresh.AdmissibleFlank.mem_disp_smul hc v k _).1 hd
    obtain ⟨q,hq,rfl⟩ := hmem d0 hd0
    exact ⟨q,hq,by ring⟩

#print axioms signedAPReadings_isolation
#print axioms signedAPReadingsClass_smul
end Fresh.SplitAPBands
