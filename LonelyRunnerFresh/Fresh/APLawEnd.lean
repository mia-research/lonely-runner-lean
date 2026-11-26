import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Cascade
import Fresh.OneMoverA
import Fresh.SelfMoverCommon
import Fresh.SelfMoverAllCommon
import Fresh.APLaw
import Fresh.APLawArr

/-!
# The AP-neighbourhood landing law for the subject at an end of the AP: arrangement statement

Written 2026-10-23.  New file.  Speeds `v i` with `|(v i - v 0) - i| ≤ 1/64` for `i ≠ 0` (subject `0`), or `|(v 7 - v i) - (7 - i)| ≤ 1/64` for `i ≠ 7` (subject `7`).
Then `FirstIso v k T` with `T` one of three explicit instants selected by two linear inequalities in the relative readings (`apLaw_core`), and `Lands`.
Grades: [L].
-/

open Classical

namespace Fresh.OneMover

open Fresh

theorem iso_iff_clear7_0 (v : Fin 8 → ℝ) (t : ℝ) :
    IsolatedAt v 0 t ↔ Clear7 (v 1 - v 0) (v 2 - v 0) (v 3 - v 0) (v 4 - v 0) (v 5 - v 0) (v 6 - v 0) (v 7 - v 0) t := by
  unfold IsolatedAt Clear7
  constructor
  · intro h
    exact ⟨h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)⟩
  · rintro ⟨c1, c2, c3, c4, c5, c6, c7⟩ i hi
    fin_cases i
    · exact absurd rfl hi
    all_goals assumption

theorem iso_iff_clear7_7 (v : Fin 8 → ℝ) (t : ℝ) :
    IsolatedAt v 7 t ↔ Clear7 (v 7 - v 6) (v 7 - v 5) (v 7 - v 4) (v 7 - v 3) (v 7 - v 2) (v 7 - v 1) (v 7 - v 0) t := by
  unfold IsolatedAt Clear7
  have e : ∀ a b : ℝ, distInt ((a - b) * t) = distInt ((b - a) * t) := by
    intro a b
    have : (b - a) * t = -((a - b) * t) := by ring
    rw [this, Fresh.Localisation.distInt_neg]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := h 6 (by decide); rw [e] at this; exact this
    · have := h 5 (by decide); rw [e] at this; exact this
    · have := h 4 (by decide); rw [e] at this; exact this
    · have := h 3 (by decide); rw [e] at this; exact this
    · have := h 2 (by decide); rw [e] at this; exact this
    · have := h 1 (by decide); rw [e] at this; exact this
    · have := h 0 (by decide); rw [e] at this; exact this
  · rintro ⟨c1, c2, c3, c4, c5, c6, c7⟩ i hi
    fin_cases i
    · rw [e]; exact c7
    · rw [e]; exact c6
    · rw [e]; exact c5
    · rw [e]; exact c4
    · rw [e]; exact c3
    · rw [e]; exact c2
    · rw [e]; exact c1
    · exact absurd rfl hi

/-- The AP-neighbourhood landing law, subject at the left end. -/
theorem apLaw_end0 (v : Fin 8 → ℝ)
    (hb : ∀ i : Fin 8, i ≠ 0 → -(1/64 : ℝ) ≤ (v i - v 0) - ((i : ℕ) : ℝ) ∧ (v i - v 0) - ((i : ℕ) : ℝ) ≤ 1/64) :
    ∃ T : ℝ, 0 < T ∧ FirstIso v 0 T ∧
      ((v 7 - v 0 ≤ 7 * (v 1 - v 0) ∧ T = ((0 : ℝ) + 1 / 8) / (v 1 - v 0)) ∨
       (7 * (v 1 - v 0) < v 7 - v 0 ∧ 3 * (v 5 - v 0) ≤ 5 * (v 3 - v 0) ∧ T = ((1 : ℝ) + 1 / 8) / (v 3 - v 0)) ∨
       (7 * (v 1 - v 0) < v 7 - v 0 ∧ 5 * (v 3 - v 0) < 3 * (v 5 - v 0) ∧ T = ((3 : ℝ) + 1 / 8) / (v 5 - v 0))) := by
  have b1 := hb 1 (by decide); have b2 := hb 2 (by decide); have b3 := hb 3 (by decide); have b4 := hb 4 (by decide)
  have b5 := hb 5 (by decide); have b6 := hb 6 (by decide); have b7 := hb 7 (by decide)
  simp only [Fin.val_one, Fin.val_two] at *
  norm_num at b1 b2 b3 b4 b5 b6 b7
  obtain ⟨T, hT, hc, hf, hcases⟩ := apLaw_core (v 1 - v 0) (v 2 - v 0) (v 3 - v 0) (v 4 - v 0) (v 5 - v 0) (v 6 - v 0) (v 7 - v 0)
    (by linarith [b1.1]) (by linarith [b1.2]) (by linarith [b2.1]) (by linarith [b2.2]) (by linarith [b3.1]) (by linarith [b3.2])
    (by linarith [b4.1]) (by linarith [b4.2]) (by linarith [b5.1]) (by linarith [b5.2]) (by linarith [b6.1]) (by linarith [b6.2])
    (by linarith [b7.1]) (by linarith [b7.2])
  refine ⟨T, hT, ⟨(iso_iff_clear7_0 v T).2 hc, ?_⟩, hcases⟩
  intro s hs0 hs
  by_contra hlt
  push Not at hlt
  exact hf s hs0 hlt ((iso_iff_clear7_0 v s).1 hs)

#print axioms apLaw_end0

end Fresh.OneMover
