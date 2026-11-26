import Fresh.TrainFlank
import Fresh.TrainFlankPair

/-! Rules 1–4, 8–18. The same retained-band geometry joins the one-slow
opening, two-slow opening, and polynomial pair families. No new existence
premise is introduced. Inherited opening selection uses
[PROVISIONAL: counting tool] to place the reference opening. -/
namespace Fresh.TrainFlankInterplay
open Fresh Fresh.Localisation Fresh.OpeningClump Fresh.TrainFlank Fresh.TrainFlankPair
open Fresh.AdmissibleFlank

 theorem openingClump_imp_pairTrainOpening {v : Fin 8 → ℝ} {k : Fin 8}
    (h : OpeningClumpClass v k) : PairTrainOpeningClass v k := by
  obtain ⟨s,x,w,C,hs,hx,hw,hC,hsep,hdev,hmem⟩ := h
  have hleft : pairLeft s s 0 0 = 1 / (8 * s) := by simp [pairLeft]; ring
  have hright : pairRight s s 0 0 = 7 / (8 * s) := by simp [pairRight]; ring
  have hfit : 1 / (8 * s) + 1 / x ≤ 7 / (8 * s) := by
    have hi : 1 / x ≤ 3 / (4 * s) := by
      rw [div_le_div_iff₀ hx (by positivity)]
      nlinarith
    have he : 7 / (8 * s) - 1 / (8 * s) = 3 / (4 * s) := by ring
    linarith
  refine ⟨s,s,x,w,C,0,0,hs,hs,hx,hw,hC,?_,?_,?_⟩
  · simpa [hleft,hright] using hfit
  · simpa [hleft] using hdev
  · intro d
    simpa only [← or_assoc, or_self] using hmem d

-- STANDING: DEFINITION
def PolynomialPairTrainClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (s a x w : ℝ) (C : Finset ℝ),
    0 < s ∧ 0 < a ∧ s ≤ a ∧ 0 < x ∧ 0 ≤ w ∧
    (∀ d ∈ C, x ≤ d ∧ d ≤ x + w) ∧
    8 * a * s ≤ x * (7 * s - a) ∧ 8 * s * w ≤ x * (6 * s - w) ∧
    ∀ d, d ∈ disparitySet v k ↔ d = s ∨ d = a ∨ d ∈ C

theorem polynomialPairTrain_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : PolynomialPairTrainClass v k) : Isolation v k := by
  obtain ⟨s,a,x,w,C,hs,ha,hsa,hx,hw,hC,hsep,hwidth,hmem⟩ := h
  obtain ⟨ht,hS,hA,hF⟩ := same_wrap_pair_train_polynomial hs ha hsa hx hw hC hsep hwidth
  refine ⟨openingAfter x (1/(8*s)),ht,?_⟩
  rw [isolatedAt_iff]
  intro d hd
  rcases (hmem d).1 hd with rfl | rfl | hdc
  · exact hS
  · exact hA
  · exact hF d hdc

theorem pairLeft_scale {c s a : ℝ} (hc : 0 < c) (p q : ℕ) :
    pairLeft (c*s) (c*a) p q = pairLeft s a p q / c := by
  unfold pairLeft
  rw [show ((p : ℝ)+1/8)/(c*s)=(((p : ℝ)+1/8)/s)/c by ring,
      show ((q : ℝ)+1/8)/(c*a)=(((q : ℝ)+1/8)/a)/c by ring,
      max_div_div_right hc.le]

theorem pairRight_scale {c s a : ℝ} (hc : 0 < c) (p q : ℕ) :
    pairRight (c*s) (c*a) p q = pairRight s a p q / c := by
  unfold pairRight
  rw [show ((p : ℝ)+7/8)/(c*s)=(((p : ℝ)+7/8)/s)/c by ring,
      show ((q : ℝ)+7/8)/(c*a)=(((q : ℝ)+7/8)/a)/c by ring,
      min_div_div_right hc.le]

theorem pair_cover_scale {c s a : ℝ} (hc : 0 < c) {C : Finset ℝ}
    {v : Fin 8 → ℝ} {k : Fin 8}
    (hmem : ∀ d, d ∈ disparitySet v k ↔ d=s ∨ d=a ∨ d∈C) :
    ∀ d, d ∈ disparitySet (fun j => c*v j) k ↔
      d=c*s ∨ d=c*a ∨ d∈C.image (fun z => c*z) := by
  intro d
  constructor
  · intro hd
    obtain ⟨z,hz,rfl⟩ := (mem_disp_smul hc v k d).1 hd
    rcases (hmem z).1 hz with rfl | rfl | hzC
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Finset.mem_image.mpr ⟨z,hzC,rfl⟩))
  · intro hd
    apply (mem_disp_smul hc v k d).2
    rcases hd with rfl | rfl | hdC
    · exact ⟨s,(hmem s).2 (Or.inl rfl),rfl⟩
    · exact ⟨a,(hmem a).2 (Or.inr (Or.inl rfl)),rfl⟩
    · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hdC
      exact ⟨z,(hmem z).2 (Or.inr (Or.inr hz)),rfl⟩

theorem pairTrainOpening_scale_of {c : ℝ} (hc : 0 < c)
    {v : Fin 8 → ℝ} {k : Fin 8} (h : PairTrainOpeningClass v k) :
    PairTrainOpeningClass (fun j => c*v j) k := by
  obtain ⟨s,a,x,w,C,p,q,hs,ha,hx,hw,hC,hfit,hdev,hmem⟩ := h
  have hL := pairLeft_scale (s:=s) (a:=a) hc p q
  have hR := pairRight_scale (s:=s) (a:=a) hc p q
  have he : pairLeft (c*s) (c*a) p q + 1/(c*x) = (pairLeft s a p q+1/x)/c := by
    rw [hL]; ring
  refine ⟨c*s,c*a,c*x,c*w,C.image (fun z=>c*z),p,q,by positivity,by positivity,
    by positivity,by positivity,?_,?_,?_,pair_cover_scale hc hmem⟩
  · intro d hd
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨h1,h2⟩ := hC z hz
    constructor
    · exact mul_le_mul_of_nonneg_left h1 hc.le
    · nlinarith [mul_le_mul_of_nonneg_left h2 hc.le]
  · rw [he,hR]
    exact div_le_div_of_nonneg_right hfit hc.le
  · rw [he]
    have he2 : c*w*((pairLeft s a p q+1/x)/c)=w*(pairLeft s a p q+1/x) := by field_simp
    rw [he2]
    exact hdev

theorem pairTrainOpening_smul {c : ℝ} (hc : 0 < c)
    {v : Fin 8 → ℝ} {k : Fin 8} :
    PairTrainOpeningClass (fun j=>c*v j) k ↔ PairTrainOpeningClass v k := by
  constructor
  · intro h
    have h' := pairTrainOpening_scale_of (c:=1/c) (by positivity) h
    simpa [hc.ne'] using h'
  · exact pairTrainOpening_scale_of hc

theorem twoSlowTrain_scale_of {c : ℝ} (hc : 0 < c)
    {v : Fin 8 → ℝ} {k : Fin 8} (h : TwoSlowTrainClass v k) :
    TwoSlowTrainClass (fun j=>c*v j) k := by
  obtain ⟨s,a,x,w,f,n,m,hx,hslo,hshi,halo,hahi,hf,hw,hmem⟩ := h
  refine ⟨c*s,c*a,c*x,c*w,(fun i=>c*f i),n,m,by positivity,?_,?_,?_,?_,?_,?_,?_⟩
  · convert mul_le_mul_of_nonneg_left hslo hc.le using 1 <;> ring
  · convert mul_le_mul_of_nonneg_left hshi hc.le using 1 <;> ring
  · convert mul_le_mul_of_nonneg_left halo hc.le using 1 <;> ring
  · convert mul_le_mul_of_nonneg_left hahi hc.le using 1 <;> ring
  · intro i
    constructor
    · exact mul_le_mul_of_nonneg_left (hf i).1 hc.le
    · convert mul_le_mul_of_nonneg_left (hf i).2 hc.le using 1 <;> ring
  · convert mul_le_mul_of_nonneg_left hw hc.le using 1 <;> ring
  · intro d
    constructor
    · intro hd
      obtain ⟨z,hz,rfl⟩ := (mem_disp_smul hc v k d).1 hd
      rcases (hmem z).1 hz with rfl | rfl | ⟨i,rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨i,rfl⟩)
    · intro hd
      apply (mem_disp_smul hc v k d).2
      rcases hd with rfl | rfl | ⟨i,rfl⟩
      · exact ⟨s,(hmem s).2 (Or.inl rfl),rfl⟩
      · exact ⟨a,(hmem a).2 (Or.inr (Or.inl rfl)),rfl⟩
      · exact ⟨f i,(hmem (f i)).2 (Or.inr (Or.inr ⟨i,rfl⟩)),rfl⟩

theorem twoSlowTrain_smul {c : ℝ} (hc : 0 < c)
    {v : Fin 8 → ℝ} {k : Fin 8} :
    TwoSlowTrainClass (fun j=>c*v j) k ↔ TwoSlowTrainClass v k := by
  constructor
  · intro h
    have h' := twoSlowTrain_scale_of (c:=1/c) (by positivity) h
    simpa [hc.ne'] using h'
  · exact twoSlowTrain_scale_of hc

#print axioms twoSlowTrain_scale_of
#print axioms twoSlowTrain_smul

#print axioms pairLeft_scale
#print axioms pairRight_scale
#print axioms pair_cover_scale
#print axioms pairTrainOpening_scale_of
#print axioms pairTrainOpening_smul

#print axioms openingClump_imp_pairTrainOpening
#print axioms polynomialPairTrain_isolation
end Fresh.TrainFlankInterplay
