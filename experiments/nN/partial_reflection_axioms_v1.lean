import LonelyRunner.LRC.Spec.PartialReflectionN

/-! Axiom audit and a real-event instance for `PartialReflectionN` (E181). -/

open LRC.PartialReflection

#print axioms LRC.PartialReflection.partial_reflected_right_inequalities

noncomputable def dE : Fin 7 → ℝ := ![21/37, 77/37, 126/37, 161/37, 189/37, 210/37, 7]
noncomputable def vE : Fin 7 → ℝ := ![-16/23, 3/23, 15/23, 13/23, 4/23, -12/23, 0]
def qE : Fin 7 → ℤ := ![0, 1, 1, 2, 2, 3, 3]
def PE : Fin 7 → ℤ := ![0, 0, 3, 0, 0, 5, 0]
def labE : Fin 7 → ℤ := ![0, 0, 1, 1, 1, 1, 2]

/-- A real death on the deformation from the AP to the target (1,7,12,15,17,18,23) (E181): at tau = 23/37 the window
q dies at t0 = 185/336 (reading 5 leaving, reading 2 entering); the pair's own period is 37/42 (lambda = 3/5); the
partial reflection lab is the cascade's replacement.  Every hypothesis is checked by computation. -/
theorem real_event_instance : ∃ e : ℝ, 0 < e ∧ ∀ h : ℝ, 0 ≤ h → h ≤ e → ∀ i ∈ (Finset.univ : Finset (Fin 7)),
    ∀ j ∈ (Finset.univ : Finset (Fin 7)),
      ((labE i : ℝ) + 1/8) * (dE j + h * vE j) ≤ ((labE j : ℝ) + 7/8) * (dE i + h * vE i) := by
  refine partial_reflected_right_inequalities Finset.univ {5, 2} Finset.univ_nonempty dE vE qE PE labE
    (t := 185/336) (lam := 3/5) (delta := 1/1000) ?_ (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_
  · intro i _; fin_cases i <;> norm_num [dE]
  · intro i hi; fin_cases i <;> simp at hi <;> norm_num [PE, dE]
  · intro i hi; fin_cases i <;> simp at hi <;> decide
  · intro i hi; fin_cases i <;> simp at hi <;> norm_num [qE, dE]
  · intro i hi j hj; fin_cases i <;> fin_cases j <;> simp at hi hj <;> norm_num [qE, dE, vE]
  · intro i _ hi; fin_cases i <;> simp at hi <;> norm_num [labE, dE]

#print axioms real_event_instance
