import Fresh.OpeningClump

/-!
Rules 1–4, 8–18. Exact slow-pair band intersections select an opening
without a free lap. [PROVISIONAL: counting tool] at openingAfter_spec:
placing the named train opening within one reference revolution.
No covering argument is used here.
-/
namespace Fresh.TrainFlankPair
open Fresh Fresh.Localisation Fresh.OpeningClump

noncomputable def pairLeft (s a : ℝ) (p q : ℕ) : ℝ :=
  max (((p : ℝ) + 1 / 8) / s) (((q : ℝ) + 1 / 8) / a)
noncomputable def pairRight (s a : ℝ) (p q : ℕ) : ℝ :=
  min (((p : ℝ) + 7 / 8) / s) (((q : ℝ) + 7 / 8) / a)

theorem clear_in_pair_window {s a t : ℝ} (hs : 0 < s) (ha : 0 < a)
    (p q : ℕ) (hl : pairLeft s a p q ≤ t) (hr : t ≤ pairRight s a p q) :
    (1 / 8 : ℝ) ≤ distInt (s * t) ∧ (1 / 8 : ℝ) ≤ distInt (a * t) := by
  have hsl := (le_max_left _ _).trans hl
  have hal := (le_max_right _ _).trans hl
  have hsr := hr.trans (min_le_left _ _)
  have har := hr.trans (min_le_right _ _)
  constructor
  · apply clear_of_window (p : ℤ)
    · have := (div_le_iff₀ hs).mp hsl; push_cast; nlinarith
    · have := (le_div_iff₀ hs).mp hsr; push_cast; nlinarith
  · apply clear_of_window (q : ℤ)
    · have := (div_le_iff₀ ha).mp hal; push_cast; nlinarith
    · have := (le_div_iff₀ ha).mp har; push_cast; nlinarith

/-- The two integer bands are chosen, then the train opening is computed.
No future clear instant or opening lap is a hypothesis. -/
theorem pair_train_opening {s a x w : ℝ} {C : Finset ℝ}
    (hs : 0 < s) (ha : 0 < a) (hx : 0 < x) (hw : 0 ≤ w) (p q : ℕ)
    (hC : ∀ d ∈ C, x ≤ d ∧ d ≤ x + w)
    (hfit : pairLeft s a p q + 1 / x ≤ pairRight s a p q)
    (hdev : w * (pairLeft s a p q + 1 / x) ≤ 3 / 4) :
    0 < openingAfter x (pairLeft s a p q) ∧
      (1 / 8 : ℝ) ≤ distInt (s * openingAfter x (pairLeft s a p q)) ∧
      (1 / 8 : ℝ) ≤ distInt (a * openingAfter x (pairLeft s a p q)) ∧
      ∀ d ∈ C, (1 / 8 : ℝ) ≤ distInt (d * openingAfter x (pairLeft s a p q)) := by
  have hlo : 0 < pairLeft s a p q :=
    lt_of_lt_of_le (by positivity : 0 < ((p : ℝ) + 1 / 8) / s) (le_max_left _ _)
  obtain ⟨h1,h2,h3⟩ := openingAfter_spec (lo := pairLeft s a p q) hx
  have ht : 0 < openingAfter x (pairLeft s a p q) := hlo.trans_le h1
  have hpair := clear_in_pair_window hs ha p q h1 (h2.le.trans hfit)
  refine ⟨ht,hpair.1,hpair.2,clump_at_opening ht.le h3 hC ?_⟩
  exact (mul_le_mul_of_nonneg_left h2.le hw).trans hdev

/-- A same-wrap pair: the common window has endpoints 1/(8s), 7/(8a).
The polynomial separation inequality eliminates the choice of lap entirely. -/
theorem same_wrap_pair_train {s a x w : ℝ} {C : Finset ℝ}
    (hs : 0 < s) (ha : 0 < a) (hsa : s ≤ a) (hx : 0 < x) (hw : 0 ≤ w)
    (hC : ∀ d ∈ C, x ≤ d ∧ d ≤ x + w)
    (hsep : 8 * a * s ≤ x * (7 * s - a))
    (hdev : w * (1 / (8 * s) + 1 / x) ≤ 3 / 4) :
    0 < openingAfter x (1 / (8 * s)) ∧
      (1 / 8 : ℝ) ≤ distInt (s * openingAfter x (1 / (8 * s))) ∧
      (1 / 8 : ℝ) ≤ distInt (a * openingAfter x (1 / (8 * s))) ∧
      ∀ d ∈ C, (1 / 8 : ℝ) ≤ distInt (d * openingAfter x (1 / (8 * s))) := by
  have hleft : pairLeft s a 0 0 = 1 / (8 * s) := by
    unfold pairLeft
    norm_num
    rw [max_eq_left]
    · ring
    · exact div_le_div_of_nonneg_left (by norm_num) hs hsa
  have hright : pairRight s a 0 0 = 7 / (8 * a) := by
    unfold pairRight
    norm_num
    rw [min_eq_right]
    · ring
    · exact div_le_div_of_nonneg_left (by norm_num) hs hsa
  have hfit : 1 / (8 * s) + 1 / x ≤ 7 / (8 * a) := by
    apply (le_div_iff₀ (by positivity : 0 < 8 * a)).2
    have he : (1 / (8 * s) + 1 / x) * (8 * a) = (a * x + 8 * a * s) / (s * x) := by field_simp
    rw [he, div_le_iff₀ (by positivity : 0 < s * x)]
    nlinarith
  have h := pair_train_opening hs ha hx hw 0 0 hC (by rw [hleft,hright]; exact hfit) (by rw [hleft]; exact hdev)
  simpa [hleft] using h

/-- Entirely polynomial parameter conditions for an unbounded real-base train.
For fixed s≤a<7s and 0≤w<6s, both hold for all sufficiently large x;
no numerical height bound is assumed by the theorem. -/
theorem same_wrap_pair_train_polynomial {s a x w : ℝ} {C : Finset ℝ}
    (hs : 0 < s) (ha : 0 < a) (hsa : s ≤ a) (hx : 0 < x) (hw : 0 ≤ w)
    (hC : ∀ d ∈ C, x ≤ d ∧ d ≤ x + w)
    (hsep : 8 * a * s ≤ x * (7 * s - a))
    (hwidth : 8 * s * w ≤ x * (6 * s - w)) :
    0 < openingAfter x (1 / (8 * s)) ∧
      (1 / 8 : ℝ) ≤ distInt (s * openingAfter x (1 / (8 * s))) ∧
      (1 / 8 : ℝ) ≤ distInt (a * openingAfter x (1 / (8 * s))) ∧
      ∀ d ∈ C, (1 / 8 : ℝ) ≤ distInt (d * openingAfter x (1 / (8 * s))) := by
  apply same_wrap_pair_train hs ha hsa hx hw hC hsep
  have he : w * (1 / (8 * s) + 1 / x) = (w * x + 8 * w * s) / (8 * s * x) := by
    field_simp
  rw [he, div_le_iff₀ (by positivity : 0 < 8 * s * x)]
  nlinarith

#print axioms same_wrap_pair_train_polynomial

-- STANDING: DEFINITION
def PairTrainOpeningClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (s a x w : ℝ) (C : Finset ℝ) (p q : ℕ),
    0 < s ∧ 0 < a ∧ 0 < x ∧ 0 ≤ w ∧
    (∀ d ∈ C, x ≤ d ∧ d ≤ x + w) ∧
    pairLeft s a p q + 1 / x ≤ pairRight s a p q ∧
    w * (pairLeft s a p q + 1 / x) ≤ 3 / 4 ∧
    ∀ d, d ∈ disparitySet v k ↔ d = s ∨ d = a ∨ d ∈ C

theorem pairTrainOpening_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : PairTrainOpeningClass v k) : Isolation v k := by
  obtain ⟨s,a,x,w,C,p,q,hs,ha,hx,hw,hC,hfit,hdev,hmem⟩ := h
  obtain ⟨ht,hS,hA,hF⟩ := pair_train_opening hs ha hx hw p q hC hfit hdev
  refine ⟨openingAfter x (pairLeft s a p q),ht,?_⟩
  rw [isolatedAt_iff]
  intro d hd
  rcases (hmem d).1 hd with rfl | rfl | hdc
  · exact hS
  · exact hA
  · exact hF d hdc

#print axioms pairTrainOpening_isolation
#print axioms clear_in_pair_window
#print axioms pair_train_opening
#print axioms same_wrap_pair_train
end Fresh.TrainFlankPair
