import Fresh.ExactClassicalBridge
import Fresh.BoundedClassicalProfiles
import Fresh.Nv_ResidueCasesTwoN

namespace Fresh.FiniteRelations

open LRC.OrderEightN LRC.ParityDescent

/-- Remove the common scale of an integer profile before testing its arithmetic. -/
def primitiveReadings (q : Fin 7 → ℤ) : Finset ℕ :=
  let a (i : Fin 7) := (q i).toNat
  Finset.univ.image fun i => a i / Finset.univ.gcd a

/-- The unresolved class of the existing integer dispatch. -/
def OpenResidual (S : Finset ℕ) : Prop :=
  EightResidual S ∧
    ¬ SettledCounts8' (S.filter (fun d => 8 ∣ d)).card (S.filter (fun d => ¬ 2 ∣ d)).card
      (S.filter (fun d => d % 4 = 2)).card (S.filter (fun d => d % 8 = 4)).card ∧
    ¬ OottCase8 S

/-- Apply the older integer dispatch after removing the common scale. -/
theorem profileCertificate_of_residual_clearance (q : Fin 7 → ℤ) (hq : ∀ i, 0 < q i)
    (h : OpenResidual (primitiveReadings q) →
      ∃ t : ℝ, 0 < t ∧ ∀ d ∈ primitiveReadings q, (8:ℝ)⁻¹ ≤ circDist ((d : ℝ) * t)) :
    ProfileCertificate q := by
  classical
  let a (i : Fin 7) := (q i).toNat
  let g := Finset.univ.gcd a
  let r (i : Fin 7) := a i / g
  have ha (i : Fin 7) : 0 < a i := by
    dsimp [a]
    have := hq i
    omega
  have hd (i : Fin 7) : g ∣ a i := Finset.gcd_dvd (Finset.mem_univ i)
  have hg : 0 < g := Nat.pos_of_dvd_of_pos (hd 0) (ha 0)
  have hmul (i : Fin 7) : g * r i = a i := Nat.mul_div_cancel' (hd i)
  have hr (i : Fin 7) : 0 < r i := by
    have := ha i
    rw [← hmul] at this
    exact Nat.pos_of_mul_pos_left (by simpa [mul_comm] using this)
  have hprim : Finset.univ.gcd r = 1 :=
    Finset.gcd_div_eq_one (Finset.mem_univ (0 : Fin 7)) (ha 0).ne'
  let S := primitiveReadings q
  have hS : S = Finset.univ.image r := rfl
  have hpos : ∀ d ∈ S, 0 < d := by
    rw [hS]
    rintro d hd
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hd
    exact hr i
  have hcard : S.card ≤ 7 := by
    rw [hS]
    exact Finset.card_image_le.trans (by simp)
  have hcf : ∀ c, 2 ≤ c → ∃ d ∈ S, ¬ c ∣ d := by
    intro c hc
    by_contra! hdiv
    have hh : c ∣ Finset.univ.gcd r := Finset.dvd_gcd fun i hi =>
      hdiv _ (hS ▸ Finset.mem_image_of_mem r hi)
    rw [hprim] at hh
    exact (by omega : c ≠ 1) (Nat.dvd_one.mp hh)
  have hw : ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8:ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) :=
    (lonely_eight_or_residual_open hpos hcard hcf).elim id h
  obtain ⟨t,ht,hclear⟩ := hw
  apply (profileCertificate_iff_clears q hq).mpr
  have hg' : (0:ℝ) < g := by exact_mod_cast hg
  refine ⟨t / g,div_pos ht hg',fun i => ?_⟩
  have hq' : (q i : ℝ) = (g : ℝ) * (r i : ℝ) := by
    have hi : (a i : ℤ) = q i := Int.toNat_of_nonneg (hq i).le
    exact_mod_cast (by exact (Int.ofNat_inj.mpr (hmul i)).trans hi :
      ((g * r i : ℕ) : ℤ) = q i).symm
  have hm : r i ∈ S := hS ▸ Finset.mem_image_of_mem r (Finset.mem_univ i)
  change (1/8:ℝ) ≤ distInt ((q i : ℝ) * (t / g))
  rw [hq', show (g : ℝ) * r i * (t / g) = r i * t by field_simp,
    Fresh.distInt_eq_fract]
  simpa only [one_div,circDist] using hclear _ hm

theorem profileCertificate_of_outside_residual (q : Fin 7 → ℤ) (hq : ∀ i, 0 < q i)
    (h : ¬ OpenResidual (primitiveReadings q)) : ProfileCertificate q :=
  profileCertificate_of_residual_clearance q hq (fun hr => (h hr).elim)

/-- Only the primitive profiles that survive the older arithmetic dispatch
need certificates on the finite family of lines. -/
theorem classical_eight_of_finite_open_residual :
    ∃ F : Finset (Fin 7 → ℤ), (∀ q ∈ F, ∀ i, 0 < q i) ∧
      ((∀ q ∈ F, OpenResidual (primitiveReadings q) → ProfileCertificate q) →
        LRC.Spec.ExistenceAt8_cascade ∧ LonelyRunnerEight) := by
  classical
  obtain ⟨F,hpos,hF⟩ := classical_eight_of_finite_certificates
  refine ⟨F,hpos,fun h => hF fun q hq => ?_⟩
  by_cases hr : OpenResidual (primitiveReadings q)
  · exact h q hq hr
  · exact profileCertificate_of_outside_residual q (hpos q hq) hr

/-- A numerical cutoff and the older arithmetic dispatch reduce the
classical target to primitive sets within the bound that survive the dispatch. -/
theorem classical_eight_of_bounded_open_residual
    (h : ∀ S : Finset ℕ, OpenResidual S → (∀ d ∈ S, 0 < d ∧ d ≤ (6*100352)^6) →
      ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8:ℝ)⁻¹ ≤ circDist ((d : ℝ) * t)) :
    LRC.Spec.ExistenceAt8_cascade ∧ LonelyRunnerEight := by
  apply classical_eight_of_integer_clearance
  intro p hp
  by_cases hs : StrictlyClears (fun i => (p i : ℝ)) (1/8)
  · obtain ⟨t,ht,hw⟩ := hs
    exact ⟨t,ht,fun i => (hw i).le⟩
  obtain ⟨q,hq,c,he⟩ := explicit_bounded_representative (fun _ => merged_phase) p hp hs
  have hqpos : ∀ i, 0 < q i := fun i => (hq i).1
  apply clears_of_positive_multiple hp hqpos ⟨c,he⟩
  apply (profileCertificate_iff_clears q hqpos).mp
  apply profileCertificate_of_residual_clearance q hqpos
  intro hr
  apply h _ hr
  intro d hd
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hd
  constructor
  · have ha : 0 < (q i).toNat := by have := hqpos i; omega
    have hg : Finset.univ.gcd (fun j : Fin 7 => (q j).toNat) ∣ (q i).toNat :=
      Finset.gcd_dvd (Finset.mem_univ i)
    exact Nat.div_pos (Nat.le_of_dvd ha hg) (Nat.pos_of_dvd_of_pos hg ha)
  · apply (Nat.div_le_self _ _).trans
    have hi : ((q i).toNat : ℤ) ≤ (6*100352)^6 := by
      rw [Int.toNat_of_nonneg (hqpos i).le]
      exact (hq i).2
    exact_mod_cast hi

#print axioms profileCertificate_of_outside_residual
#print axioms classical_eight_of_finite_open_residual
#print axioms classical_eight_of_bounded_open_residual

end Fresh.FiniteRelations
