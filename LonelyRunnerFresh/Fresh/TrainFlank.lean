import Fresh.Localisation

/-!
Rules 1–4, 8–18. Two retained slow readings and an arbitrary five-reading
translated train. Source: E641 opening `(4+1/8)/28` for `(1,5,28,…,32)`
and `(1,9,28,…,32)`. The reference phase n+1/8 advances by precisely
(d-x)*(8n+1)/(8x). The second retained reading may have any wrap m.
No counting, covering or cap on n. All inequalities retain equality edges.
-/
namespace Fresh.TrainFlank
open Fresh Fresh.Localisation

theorem retained_band {x d : ℝ} (hx : 0 < x) (n m : ℕ)
    (hlo : (8 * (m : ℝ) + 1) * x ≤ d * (8 * n + 1))
    (hhi : d * (8 * n + 1) ≤ (8 * (m : ℝ) + 7) * x) :
    (1 / 8 : ℝ) ≤ distInt (d * ((8 * n + 1) / (8 * x))) := by
  apply clear_of_window (m : ℤ)
  · rw [← mul_div_assoc, le_div_iff₀ (by positivity : 0 < 8 * x)]
    push_cast
    nlinarith
  · rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < 8 * x)]
    push_cast
    nlinarith

theorem train_band {x w d : ℝ} (hx : 0 < x) (n : ℕ)
    (hd : x ≤ d) (hdw : d ≤ x + w)
    (hw : w * (8 * (n : ℝ) + 1) ≤ 6 * x) :
    (1 / 8 : ℝ) ≤ distInt (d * ((8 * n + 1) / (8 * x))) := by
  apply retained_band hx n n
  · have hu : 0 ≤ 8 * (n : ℝ) + 1 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hd hu]
  · have hu : 0 ≤ 8 * (n : ℝ) + 1 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hdw hu]

theorem two_slow_train {s a x w : ℝ} {f : Fin 5 → ℝ}
    (hx : 0 < x) (n m : ℕ)
    (hslo : x ≤ s * (8 * n + 1))
    (hshi : s * (8 * n + 1) ≤ 7 * x)
    (halo : (8 * (m : ℝ) + 1) * x ≤ a * (8 * n + 1))
    (hahi : a * (8 * n + 1) ≤ (8 * (m : ℝ) + 7) * x)
    (hf : ∀ i, x ≤ f i ∧ f i ≤ x + w)
    (hw : w * (8 * (n : ℝ) + 1) ≤ 6 * x) :
    ∃ t : ℝ, 0 < t ∧ (1 / 8 : ℝ) ≤ distInt (s * t) ∧
      (1 / 8 : ℝ) ≤ distInt (a * t) ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (f i * t) := by
  refine ⟨(8 * n + 1) / (8 * x), by positivity, ?_, retained_band hx n m halo hahi, ?_⟩
  · exact retained_band hx n 0 (by simpa using hslo) (by simpa using hshi)
  · intro i
    exact train_band hx n (hf i).1 (hf i).2 hw

/-- Independent plus/minus deviations from a translated five-term AP.
The anchor remains x, while every other train member may move both ways. -/
theorem near_ap_two_slow_train {s a x h η : ℝ} {f : Fin 5 → ℝ}
    (hx : 0 < x) (n m : ℕ) (hη : 0 ≤ η) (hh : η ≤ h)
    (hf0 : f 0 = x) (hdev : ∀ i, |f i - (x + (i : ℕ) * h)| ≤ η)
    (hslo : x ≤ s * (8 * n + 1))
    (hshi : s * (8 * n + 1) ≤ 7 * x)
    (halo : (8 * (m : ℝ) + 1) * x ≤ a * (8 * n + 1))
    (hahi : a * (8 * n + 1) ≤ (8 * (m : ℝ) + 7) * x)
    (hw : (4 * h + η) * (8 * (n : ℝ) + 1) ≤ 6 * x) :
    ∃ t : ℝ, 0 < t ∧ (1 / 8 : ℝ) ≤ distInt (s * t) ∧
      (1 / 8 : ℝ) ≤ distInt (a * t) ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (f i * t) := by
  apply two_slow_train hx n m hslo hshi halo hahi (w := 4 * h + η) _ hw
  intro i
  have he := abs_le.mp (hdev i)
  have hi4 : ((i : ℕ) : ℝ) ≤ 4 := by exact_mod_cast (by omega : (i : ℕ) ≤ 4)
  have hh0 : 0 ≤ h := le_trans hη hh
  constructor
  · by_cases hi : i = 0
    · simp [hi, hf0]
    · have hi1 : (1 : ℝ) ≤ (i : ℕ) := by
        exact_mod_cast (show 1 ≤ (i : ℕ) from by
          have : (i : ℕ) ≠ 0 := by intro hz; apply hi; exact Fin.ext hz
          omega)
      nlinarith
  · nlinarith

-- STANDING: DEFINITION
def TwoSlowTrainClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (s a x w : ℝ) (f : Fin 5 → ℝ) (n m : ℕ),
    0 < x ∧ x ≤ s * (8 * n + 1) ∧ s * (8 * n + 1) ≤ 7 * x ∧
    (8 * (m : ℝ) + 1) * x ≤ a * (8 * n + 1) ∧
    a * (8 * n + 1) ≤ (8 * (m : ℝ) + 7) * x ∧
    (∀ i, x ≤ f i ∧ f i ≤ x + w) ∧
    w * (8 * (n : ℝ) + 1) ≤ 6 * x ∧
    ∀ d, d ∈ disparitySet v k ↔ d = s ∨ d = a ∨ ∃ i, d = f i

theorem twoSlowTrain_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : TwoSlowTrainClass v k) : Isolation v k := by
  obtain ⟨s, a, x, w, f, n, m, hx, hslo, hshi, halo, hahi, hf, hw, hmem⟩ := h
  obtain ⟨t, ht, hs, ha, hF⟩ := two_slow_train hx n m hslo hshi halo hahi hf hw
  refine ⟨t, ht, ?_⟩
  rw [isolatedAt_iff]
  intro d hd
  rcases (hmem d).1 hd with rfl | rfl | ⟨i, rfl⟩
  · exact hs
  · exact ha
  · exact hF i

#print axioms near_ap_two_slow_train
#print axioms retained_band
#print axioms train_band
#print axioms two_slow_train
#print axioms twoSlowTrain_isolation
end Fresh.TrainFlank
