import Fresh.ExplicitFourierKernel
import Fresh.Nv_RealEightN
import Fresh.DistIntFract

namespace Fresh.FiniteRelations

open Set
open scoped BigOperators

noncomputable section

open LRC.OrderFiveN (dotZ)

/-- In dimension at least two, a merged integer direction invokes order
seven and gives a strict phase in the entire subspace. -/
theorem merged_phase {d : ℕ} (U : Fin d → Fin 7 → ℤ)
    (hnz : ∀ i, (fun j => U j i) ≠ 0)
    (hnp : ∃ i k, ¬ ∀ j q, U j i * U q k = U q i * U j k) :
    MergedPhase U := by
  classical
  obtain ⟨y,hy,i,k,hik,he⟩ :=
    LRC.OrderSevenN.exists_merge_model_all (fun i j => U j i) hnz hnp
  let p (i : Fin 7) := dotZ y (fun j => U j i)
  let w (i : Fin 7) : ℝ := |(p i : ℝ)|
  let W := Finset.univ.image w
  have hpos : ∀ a ∈ W, 0 < a := by
    rintro a ha
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ha
    exact abs_pos.mpr (by exact_mod_cast hy j)
  have hcard : W.card ≤ 6 := by
    have hle : W.card ≤ 7 := Finset.card_image_le.trans (by simp)
    by_contra! hgt
    have heq : W.card = (Finset.univ : Finset (Fin 7)).card := by simp; omega
    have hinj := Finset.card_image_iff.mp heq
    apply hik (hinj (Finset.mem_univ i) (Finset.mem_univ k) ?_)
    simp only [w, ← Int.cast_abs, Int.abs_eq_natAbs]
    rw [show (p i).natAbs = (p k).natAbs from he]
  obtain ⟨t,_,ht⟩ := LRC.OrderSevenN.existenceAtN_seven W hpos (by simpa using hcard)
  refine ⟨torusCast (fun j => (y j : ℝ) * t),?_⟩
  intro j
  rw [parameterMap_cast,torusCast,UnitAddCircle.norm_eq]
  have hh := ht (w j) (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  change (7:ℝ)⁻¹ ≤ circDist (w j * t) at hh
  rw [show w j = |(p j : ℝ)| from rfl, LRC.SpecN.circDist_abs_mul] at hh
  have hsum : (∑ a, (U a j : ℝ) * ((y a : ℝ) * t)) = (p j : ℝ) * t := by
    simp only [p,dotZ,Int.cast_sum,Int.cast_mul,Finset.sum_mul,mul_assoc]
  rw [hsum]
  change (1/7:ℝ) ≤ distInt ((p j : ℝ) * t)
  rw [Fresh.distInt_eq_fract]
  simpa only [one_div] using hh

theorem clears_of_positive_multiple {p q : Fin 7 → ℤ}
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (h : ∃ c : ℚ, ∀ i, c * (q i : ℚ) = (p i : ℚ))
    (hw : Clears (fun i => (q i : ℝ)) (1/8)) :
    Clears (fun i => (p i : ℝ)) (1/8) := by
  obtain ⟨c,hc⟩ := h
  have he (i : Fin 7) : (c : ℝ) * (q i : ℝ) = (p i : ℝ) := by
    exact_mod_cast hc i
  have hq0 : (0:ℝ) < q 0 := by exact_mod_cast hq 0
  have hp0 : (0:ℝ) < p 0 := by exact_mod_cast hp 0
  have hc0 : 0 < (c : ℝ) := pos_of_mul_pos_left (he 0 ▸ hp0) hq0.le
  obtain ⟨t,ht,htq⟩ := hw
  refine ⟨t / (c : ℝ),div_pos ht hc0,fun i => ?_⟩
  change (1/8:ℝ) ≤ distInt ((p i : ℝ) * (t / c))
  rw [← he i, show (c : ℝ) * q i * (t / c) = q i * t by field_simp]
  exact htq i

/-- Transport the integer witness theorem to the classical real target and
the cascade termination statement. -/
theorem classical_eight_of_integer_clearance
    (hc : ∀ q : Fin 7 → ℤ, (∀ i, 0 < q i) → Clears (fun i => (q i : ℝ)) (1/8)) :
    LRC.Spec.ExistenceAt8_cascade ∧ LonelyRunnerEight := by
  classical
  have hn : ∀ S : Finset ℕ, (∀ d ∈ S, 0 < d) → S.card ≤ 7 →
      ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
    intro S hS hcard
    by_cases hsmall : S.card ≤ 6
    · let W := S.image (fun d : ℕ => (d : ℝ))
      have hwpos : ∀ d ∈ W, 0 < d := by
        intro d hd
        obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hd
        exact_mod_cast hS a ha
      have hwcard : W.card ≤ 6 := Finset.card_image_le.trans hsmall
      obtain ⟨t,ht,hwt⟩ := LRC.OrderSevenN.existenceAtN_seven W hwpos (by simpa using hwcard)
      refine ⟨t,ht,fun d hd => ?_⟩
      have hh := hwt (d : ℝ) (Finset.mem_image_of_mem _ hd)
      change (7 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) at hh
      exact (by norm_num : (8 : ℝ)⁻¹ ≤ (7 : ℝ)⁻¹).trans hh
    have he : S.card = 7 := by omega
    let e := S.equivFinOfCardEq he
    let q (i : Fin 7) : ℤ := (e.symm i : S).val
    have hq (i : Fin 7) : 0 < q i := by
      change 0 < ((e.symm i : S).val : ℤ)
      exact_mod_cast hS _ (e.symm i).property
    obtain ⟨t,ht,htq⟩ := hc q hq
    refine ⟨t,ht,fun d hd => ?_⟩
    have hh := htq (e ⟨d,hd⟩)
    simpa [q, Fresh.distInt_eq_fract, circDist, one_div] using hh
  have hex := LRC.OrderEightN.existenceAt8_of_nat hn
  have hold := LRC.Spec.lonelyRunnerAt8_of_existence hex
  refine ⟨LRC.Spec.target_forms_agree.mp hex,fun v hv k => ?_⟩
  obtain ⟨t,ht,hvt⟩ := hold v hv.2 k
  refine ⟨t,ht,fun i hi => ?_⟩
  rw [Fresh.distInt_eq_fract, show (v i - v k)*t = v i*t - v k*t by ring]
  simpa [circDist,one_div] using hvt i hi

/-- The classical eight-runner target follows from the weak clearance
of a finite set of positive integer disparity profiles. -/
theorem classical_eight_of_finite_integer_profiles :
    ∃ F : Finset (Fin 7 → ℤ), (∀ q ∈ F, ∀ i, 0 < q i) ∧
      ((∀ q ∈ F, Clears (fun i => (q i : ℝ)) (1/8)) →
        LRC.Spec.ExistenceAt8_cascade ∧ LonelyRunnerEight) := by
  classical
  obtain ⟨F,hpos,hF⟩ := explicit_integer_profiles (fun _ => merged_phase)
  refine ⟨F,hpos,fun hc => ?_⟩
  apply classical_eight_of_integer_clearance
  intro q hq
  rcases hF q hq with hclear | ⟨p,hp,c,he⟩
  · obtain ⟨t,ht,h⟩ := hclear
    exact ⟨t,ht,fun i => (h i).le⟩
  · exact clears_of_positive_multiple hq (hpos p hp) ⟨c,he⟩ (hc p hp)

/-- A closed modular test on a single integer profile. The lap index
ranges over one period, and both endpoints of the clear band are allowed. -/
def ProfileCertificate (q : Fin 7 → ℤ) : Prop :=
  ∃ j : Fin 7, ∃ k : Fin (q j).toNat, ∀ i : Fin 7,
    let r := q i * (8 * (k.val : ℤ) + 1) % (8 * q j)
    q j ≤ r ∧ r ≤ 8 * q j - q j

instance (q : Fin 7 → ℤ) : Decidable (ProfileCertificate q) :=
  inferInstanceAs (Decidable (∃ j : Fin 7, ∃ k : Fin (q j).toNat, ∀ i : Fin 7,
    let r := q i * (8 * (k.val : ℤ) + 1) % (8 * q j)
    q j ≤ r ∧ r ≤ 8 * q j - q j))

theorem profileCertificate_iff_clears (q : Fin 7 → ℤ) (hq : ∀ i, 0 < q i) :
    ProfileCertificate q ↔ Clears (fun i => (q i : ℝ)) (1/8) := by
  classical
  let S := Finset.univ.image (fun i : Fin 7 => (q i : ℝ))
  have hm (i : Fin 7) : (q i : ℝ) ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hp : ∀ x ∈ S, 0 < x := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact_mod_cast hq i
  have hint : ∀ x ∈ S, ∃ a : ℤ, x = (a : ℝ) := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact ⟨q i,rfl⟩
  have hsearch := Flanks.lonely_iff_emod_search (n := 8) hp ⟨_,hm 0⟩ hint
  have hl : Clears (fun i => (q i : ℝ)) (1/8) ↔
      ∃ t : ℝ, 0 < t ∧ MomentIterationN.Lonely 8 S t := by
    constructor
    · rintro ⟨t,ht,hh⟩
      refine ⟨t,ht,fun x hx => ?_⟩
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      simpa [Fresh.distInt_eq_fract,circDist,one_div] using hh i
    · rintro ⟨t,ht,hh⟩
      refine ⟨t,ht,fun i => ?_⟩
      simpa [Fresh.distInt_eq_fract,circDist,one_div] using hh _ (hm i)
  rw [hl,hsearch]
  constructor
  · rintro ⟨j,k,h⟩
    have hk : (k.val : ℤ) < q j := by
      exact (Int.lt_toNat.mp k.isLt)
    refine ⟨q j,hq j,hm j,k.val,hk,fun a ha => ?_⟩
    obtain ⟨i,_,he⟩ := Finset.mem_image.mp ha
    have hai : q i = a := by exact_mod_cast he
    simpa only [hai,Nat.cast_ofNat] using h i
  · rintro ⟨b,_,hb,k,hk,h⟩
    obtain ⟨j,_,he⟩ := Finset.mem_image.mp hb
    have hjb : q j = b := by exact_mod_cast he
    subst b
    exact ⟨j,⟨k,Int.lt_toNat.mpr hk⟩,fun i => by simpa only [Nat.cast_ofNat] using h (q i) (hm i)⟩

/-- One finite arithmetic obligation suffices for cascade termination and isolation. -/
theorem classical_eight_of_finite_certificates :
    ∃ F : Finset (Fin 7 → ℤ), (∀ q ∈ F, ∀ i, 0 < q i) ∧
      ((∀ q ∈ F, ProfileCertificate q) → LRC.Spec.ExistenceAt8_cascade ∧ LonelyRunnerEight) := by
  obtain ⟨F,hpos,hF⟩ := classical_eight_of_finite_integer_profiles
  exact ⟨F,hpos,fun h => hF fun q hq =>
    (profileCertificate_iff_clears q (hpos q hq)).mp (h q hq)⟩

#print axioms classical_eight_of_finite_integer_profiles
#print axioms profileCertificate_iff_clears
#print axioms classical_eight_of_finite_certificates

end
end Fresh.FiniteRelations
