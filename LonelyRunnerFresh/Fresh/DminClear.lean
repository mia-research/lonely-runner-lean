import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Cascade
import Fresh.SelfMoverCommon
import Fresh.SelfMoverAllCommon
import Fresh.RatioLanding

/-!
# The d_min instant is the first isolation exactly when no reading blocks it

Written 2026-10-24.  New file.  For an arrangement `v`, subject `k`, least disparity `m` attained, the cascade starts at `t0 = 1/(8m)`.
Reading `r` is clear at `t0` iff `distInt (r t0) ≥ 1/8`, that is iff `r / m` is not within `1` of a positive multiple of `8`
(`r t0 = (r/m)/8`).  `dmin_firstIso_iff`: `t0` is the first isolation instant iff every reading is clear at `t0`.  So the d_min
displacement of the isolation (class B) is exactly the case where no reading lies within one d_min of a multiple of `8 d_min`; otherwise (class C) the first isolation
is strictly later.  `ratio_firstIso` is the special case where all readings lie in `[m, 7m]`.  Grades: [L].
-/

open Classical

namespace Fresh.OneMover

open Fresh

theorem dmin_firstIso_iff (v : Fin 8 → ℝ) (k : Fin 8) (m : ℝ) (hm : 0 < m)
    (hmem : ∃ i, i ≠ k ∧ |v i - v k| = m) (hle : ∀ i, i ≠ k → m ≤ |v i - v k|) :
    FirstIso v k (1 / (8 * m)) ↔ ∀ i, i ≠ k → (1 / 8 : ℝ) ≤ distInt (|v i - v k| * (1 / (8 * m))) := by
  constructor
  · intro h i hik
    have h1 := h.1 i hik
    rcases abs_cases (v i - v k) with ⟨ha, _⟩ | ⟨ha, _⟩
    · rw [ha]; exact h1
    · rw [ha]
      have : (-(v i - v k)) * (1 / (8 * m)) = -((v i - v k) * (1 / (8 * m))) := by ring
      rw [this, Fresh.Localisation.distInt_neg]; exact h1
  · intro hc
    have hT : 0 < 1 / (8 * m) := by positivity
    refine ⟨?_, ?_⟩
    · intro i hik
      have h1 := hc i hik
      rcases abs_cases (v i - v k) with ⟨ha, _⟩ | ⟨ha, _⟩
      · rw [ha] at h1; exact h1
      · rw [ha] at h1
        have : (-(v i - v k)) * (1 / (8 * m)) = -((v i - v k) * (1 / (8 * m))) := by ring
        rw [this, Fresh.Localisation.distInt_neg] at h1; exact h1
    · intro s hs0 hs
      by_contra hlt
      push Not at hlt
      obtain ⟨i, hik, him⟩ := hmem
      have h := hs i hik
      have hin := inway_before hm hs0 hlt
      have : distInt ((v i - v k) * s) = distInt (m * s) := by
        rcases abs_cases (v i - v k) with ⟨ha, _⟩ | ⟨ha, _⟩
        · rw [ha] at him; rw [him]
        · rw [ha] at him
          have e2 : (v i - v k) = -m := by linarith
          rw [e2, neg_mul, Fresh.Localisation.distInt_neg]
      rw [this] at h
      linarith

/-- If some reading blocks the d_min instant, the first isolation is strictly later than it (class C). -/
theorem dmin_blocked_not_first (v : Fin 8 → ℝ) (k : Fin 8) (m : ℝ) (hm : 0 < m)
    (hmem : ∃ i, i ≠ k ∧ |v i - v k| = m) (hle : ∀ i, i ≠ k → m ≤ |v i - v k|)
    (j : Fin 8) (hjk : j ≠ k) (hb : distInt (|v j - v k| * (1 / (8 * m))) < 1 / 8) :
    ¬ FirstIso v k (1 / (8 * m)) := by
  intro h
  have := (dmin_firstIso_iff v k m hm hmem hle).1 h j hjk
  linarith

#print axioms dmin_firstIso_iff
#print axioms dmin_blocked_not_first

end Fresh.OneMover
