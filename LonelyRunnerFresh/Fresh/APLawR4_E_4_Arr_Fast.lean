import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Cascade
import Fresh.OneMoverA
import Fresh.SelfMoverCommon
import Fresh.SelfMoverAllCommon
import Fresh.APLaw
import Fresh.APLawR4_E_4_Core_Fast

/-!
# Arrangement statements (speeds within 1/8 of the AP), on the heartbeat-raised core

Written 2026-11-06.  New file: `Fresh/APLawR4_E_4_Arr.lean` (2026-11-02, another session, uncommitted, left
untouched) with the single import `Fresh.APLawR4_E_4_Core` replaced by `Fresh.APLawR4_E_4_Core_Fast`
(same `apLawR4_E_4_core`, proved within a 16000000-heartbeat budget).  Everything else is verbatim:
`FirstIso v k T` for the listed subjects with `T` one of 33 explicit instants `(M + 1/8)/reading`, from speeds
within 1/8 of `c + i` (relative readings within 1/4).  Grades: [L].
-/

open Classical

namespace Fresh.OneMover

open Fresh

theorem apLawR4_E_4_iso_0 (v : Fin 8 → ℝ) (t : ℝ) :
    IsolatedAt v 0 t ↔ Clear7 (v 1 - v 0) (v 2 - v 0) (v 3 - v 0) (v 4 - v 0) (v 5 - v 0) (v 6 - v 0) (v 7 - v 0) t := by
  unfold IsolatedAt Clear7
  have e : ∀ a b : ℝ, distInt ((a - b) * t) = distInt ((b - a) * t) := by
    intro a b
    have : (b - a) * t = -((a - b) * t) := by ring
    rw [this, Fresh.Localisation.distInt_neg]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact h 1 (by decide)
    · exact h 2 (by decide)
    · exact h 3 (by decide)
    · exact h 4 (by decide)
    · exact h 5 (by decide)
    · exact h 6 (by decide)
    · exact h 7 (by decide)
  · rintro ⟨c1, c2, c3, c4, c5, c6, c7⟩ i hi
    fin_cases i
    · exact absurd rfl hi
    · exact c1
    · exact c2
    · exact c3
    · exact c4
    · exact c5
    · exact c6
    · exact c7

theorem apLawR4_E_4_end_0 (c : ℝ) (v : Fin 8 → ℝ) (hv : ∀ i : Fin 8, |v i - (c + ((i : ℕ) : ℝ))| ≤ 1/8) :
    ∃ T : ℝ, 0 < T ∧ FirstIso v 0 T ∧
      (T = ((0 : ℝ) + 1 / 8) / (v 1 - v 0) ∨ T = ((2 : ℝ) + 1 / 8) / (v 7 - v 0) ∨ T = ((3 : ℝ) + 1 / 8) / (v 7 - v 0) ∨ T = ((4 : ℝ) + 1 / 8) / (v 6 - v 0) ∨ T = ((4 : ℝ) + 1 / 8) / (v 7 - v 0) ∨ T = ((6 : ℝ) + 1 / 8) / (v 7 - v 0) ∨ T = ((4 : ℝ) + 1 / 8) / (v 5 - v 0) ∨ T = ((5 : ℝ) + 1 / 8) / (v 6 - v 0) ∨ T = ((3 : ℝ) + 1 / 8) / (v 4 - v 0) ∨ T = ((2 : ℝ) + 1 / 8) / (v 3 - v 0) ∨ T = ((3 : ℝ) + 1 / 8) / (v 5 - v 0) ∨ T = ((6 : ℝ) + 1 / 8) / (v 5 - v 0) ∨ T = ((1 : ℝ) + 1 / 8) / (v 1 - v 0) ∨ T = ((9 : ℝ) + 1 / 8) / (v 6 - v 0) ∨ T = ((5 : ℝ) + 1 / 8) / (v 4 - v 0) ∨ T = ((8 : ℝ) + 1 / 8) / (v 7 - v 0) ∨ T = ((2 : ℝ) + 1 / 8) / (v 2 - v 0) ∨ T = ((6 : ℝ) + 1 / 8) / (v 6 - v 0) ∨ T = ((2 : ℝ) + 1 / 8) / (v 4 - v 0) ∨ T = ((1 : ℝ) + 1 / 8) / (v 2 - v 0) ∨ T = ((2 : ℝ) + 1 / 8) / (v 5 - v 0) ∨ T = ((1 : ℝ) + 1 / 8) / (v 3 - v 0) ∨ T = ((1 : ℝ) + 1 / 8) / (v 4 - v 0) ∨ T = ((2 : ℝ) + 1 / 8) / (v 6 - v 0) ∨ T = ((5 : ℝ) + 1 / 8) / (v 7 - v 0) ∨ T = ((3 : ℝ) + 1 / 8) / (v 6 - v 0) ∨ T = ((8 : ℝ) + 1 / 8) / (v 6 - v 0) ∨ T = ((4 : ℝ) + 1 / 8) / (v 4 - v 0) ∨ T = ((9 : ℝ) + 1 / 8) / (v 7 - v 0) ∨ T = ((3 : ℝ) + 1 / 8) / (v 3 - v 0) ∨ T = ((5 : ℝ) + 1 / 8) / (v 5 - v 0) ∨ T = ((1 : ℝ) + 1 / 8) / (v 5 - v 0) ∨ T = ((1 : ℝ) + 1 / 8) / (v 6 - v 0)) := by
  have h0 := abs_le.1 (hv 0)
  have e0 : ((0 : Fin 8) : ℕ) = 0 := rfl
  rw [e0] at h0
  push_cast at h0
  have h1 := abs_le.1 (hv 1)
  have e1 : ((1 : Fin 8) : ℕ) = 1 := rfl
  rw [e1] at h1
  push_cast at h1
  have h2 := abs_le.1 (hv 2)
  have e2 : ((2 : Fin 8) : ℕ) = 2 := rfl
  rw [e2] at h2
  push_cast at h2
  have h3 := abs_le.1 (hv 3)
  have e3 : ((3 : Fin 8) : ℕ) = 3 := rfl
  rw [e3] at h3
  push_cast at h3
  have h4 := abs_le.1 (hv 4)
  have e4 : ((4 : Fin 8) : ℕ) = 4 := rfl
  rw [e4] at h4
  push_cast at h4
  have h5 := abs_le.1 (hv 5)
  have e5 : ((5 : Fin 8) : ℕ) = 5 := rfl
  rw [e5] at h5
  push_cast at h5
  have h6 := abs_le.1 (hv 6)
  have e6 : ((6 : Fin 8) : ℕ) = 6 := rfl
  rw [e6] at h6
  push_cast at h6
  have h7 := abs_le.1 (hv 7)
  have e7 : ((7 : Fin 8) : ℕ) = 7 := rfl
  rw [e7] at h7
  push_cast at h7
  obtain ⟨T, hT, hc, hf, hcases⟩ := apLawR4_E_4_core (v 1 - v 0) (v 2 - v 0) (v 3 - v 0) (v 4 - v 0) (v 5 - v 0) (v 6 - v 0) (v 7 - v 0)
    (by linarith [h1.1, h1.2, h0.1, h0.2]) (by linarith [h1.1, h1.2, h0.1, h0.2]) (by linarith [h2.1, h2.2, h0.1, h0.2]) (by linarith [h2.1, h2.2, h0.1, h0.2]) (by linarith [h3.1, h3.2, h0.1, h0.2]) (by linarith [h3.1, h3.2, h0.1, h0.2]) (by linarith [h4.1, h4.2, h0.1, h0.2]) (by linarith [h4.1, h4.2, h0.1, h0.2]) (by linarith [h5.1, h5.2, h0.1, h0.2]) (by linarith [h5.1, h5.2, h0.1, h0.2]) (by linarith [h6.1, h6.2, h0.1, h0.2]) (by linarith [h6.1, h6.2, h0.1, h0.2]) (by linarith [h7.1, h7.2, h0.1, h0.2]) (by linarith [h7.1, h7.2, h0.1, h0.2])
  refine ⟨T, hT, ⟨(apLawR4_E_4_iso_0 v T).2 hc, ?_⟩, hcases⟩
  intro s hs0 hs
  by_contra hlt
  push Not at hlt
  exact hf s hs0 hlt ((apLawR4_E_4_iso_0 v s).1 hs)

theorem apLawR4_E_4_iso_7 (v : Fin 8 → ℝ) (t : ℝ) :
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

theorem apLawR4_E_4_end_7 (c : ℝ) (v : Fin 8 → ℝ) (hv : ∀ i : Fin 8, |v i - (c + ((i : ℕ) : ℝ))| ≤ 1/8) :
    ∃ T : ℝ, 0 < T ∧ FirstIso v 7 T ∧
      (T = ((0 : ℝ) + 1 / 8) / (v 7 - v 6) ∨ T = ((2 : ℝ) + 1 / 8) / (v 7 - v 0) ∨ T = ((3 : ℝ) + 1 / 8) / (v 7 - v 0) ∨ T = ((4 : ℝ) + 1 / 8) / (v 7 - v 1) ∨ T = ((4 : ℝ) + 1 / 8) / (v 7 - v 0) ∨ T = ((6 : ℝ) + 1 / 8) / (v 7 - v 0) ∨ T = ((4 : ℝ) + 1 / 8) / (v 7 - v 2) ∨ T = ((5 : ℝ) + 1 / 8) / (v 7 - v 1) ∨ T = ((3 : ℝ) + 1 / 8) / (v 7 - v 3) ∨ T = ((2 : ℝ) + 1 / 8) / (v 7 - v 4) ∨ T = ((3 : ℝ) + 1 / 8) / (v 7 - v 2) ∨ T = ((6 : ℝ) + 1 / 8) / (v 7 - v 2) ∨ T = ((1 : ℝ) + 1 / 8) / (v 7 - v 6) ∨ T = ((9 : ℝ) + 1 / 8) / (v 7 - v 1) ∨ T = ((5 : ℝ) + 1 / 8) / (v 7 - v 3) ∨ T = ((8 : ℝ) + 1 / 8) / (v 7 - v 0) ∨ T = ((2 : ℝ) + 1 / 8) / (v 7 - v 5) ∨ T = ((6 : ℝ) + 1 / 8) / (v 7 - v 1) ∨ T = ((2 : ℝ) + 1 / 8) / (v 7 - v 3) ∨ T = ((1 : ℝ) + 1 / 8) / (v 7 - v 5) ∨ T = ((2 : ℝ) + 1 / 8) / (v 7 - v 2) ∨ T = ((1 : ℝ) + 1 / 8) / (v 7 - v 4) ∨ T = ((1 : ℝ) + 1 / 8) / (v 7 - v 3) ∨ T = ((2 : ℝ) + 1 / 8) / (v 7 - v 1) ∨ T = ((5 : ℝ) + 1 / 8) / (v 7 - v 0) ∨ T = ((3 : ℝ) + 1 / 8) / (v 7 - v 1) ∨ T = ((8 : ℝ) + 1 / 8) / (v 7 - v 1) ∨ T = ((4 : ℝ) + 1 / 8) / (v 7 - v 3) ∨ T = ((9 : ℝ) + 1 / 8) / (v 7 - v 0) ∨ T = ((3 : ℝ) + 1 / 8) / (v 7 - v 4) ∨ T = ((5 : ℝ) + 1 / 8) / (v 7 - v 2) ∨ T = ((1 : ℝ) + 1 / 8) / (v 7 - v 2) ∨ T = ((1 : ℝ) + 1 / 8) / (v 7 - v 1)) := by
  have h0 := abs_le.1 (hv 0)
  have e0 : ((0 : Fin 8) : ℕ) = 0 := rfl
  rw [e0] at h0
  push_cast at h0
  have h1 := abs_le.1 (hv 1)
  have e1 : ((1 : Fin 8) : ℕ) = 1 := rfl
  rw [e1] at h1
  push_cast at h1
  have h2 := abs_le.1 (hv 2)
  have e2 : ((2 : Fin 8) : ℕ) = 2 := rfl
  rw [e2] at h2
  push_cast at h2
  have h3 := abs_le.1 (hv 3)
  have e3 : ((3 : Fin 8) : ℕ) = 3 := rfl
  rw [e3] at h3
  push_cast at h3
  have h4 := abs_le.1 (hv 4)
  have e4 : ((4 : Fin 8) : ℕ) = 4 := rfl
  rw [e4] at h4
  push_cast at h4
  have h5 := abs_le.1 (hv 5)
  have e5 : ((5 : Fin 8) : ℕ) = 5 := rfl
  rw [e5] at h5
  push_cast at h5
  have h6 := abs_le.1 (hv 6)
  have e6 : ((6 : Fin 8) : ℕ) = 6 := rfl
  rw [e6] at h6
  push_cast at h6
  have h7 := abs_le.1 (hv 7)
  have e7 : ((7 : Fin 8) : ℕ) = 7 := rfl
  rw [e7] at h7
  push_cast at h7
  obtain ⟨T, hT, hc, hf, hcases⟩ := apLawR4_E_4_core (v 7 - v 6) (v 7 - v 5) (v 7 - v 4) (v 7 - v 3) (v 7 - v 2) (v 7 - v 1) (v 7 - v 0)
    (by linarith [h6.1, h6.2, h7.1, h7.2]) (by linarith [h6.1, h6.2, h7.1, h7.2]) (by linarith [h5.1, h5.2, h7.1, h7.2]) (by linarith [h5.1, h5.2, h7.1, h7.2]) (by linarith [h4.1, h4.2, h7.1, h7.2]) (by linarith [h4.1, h4.2, h7.1, h7.2]) (by linarith [h3.1, h3.2, h7.1, h7.2]) (by linarith [h3.1, h3.2, h7.1, h7.2]) (by linarith [h2.1, h2.2, h7.1, h7.2]) (by linarith [h2.1, h2.2, h7.1, h7.2]) (by linarith [h1.1, h1.2, h7.1, h7.2]) (by linarith [h1.1, h1.2, h7.1, h7.2]) (by linarith [h0.1, h0.2, h7.1, h7.2]) (by linarith [h0.1, h0.2, h7.1, h7.2])
  refine ⟨T, hT, ⟨(apLawR4_E_4_iso_7 v T).2 hc, ?_⟩, hcases⟩
  intro s hs0 hs
  by_contra hlt
  push Not at hlt
  exact hf s hs0 hlt ((apLawR4_E_4_iso_7 v s).1 hs)

#print axioms apLawR4_E_4_end_0
#print axioms apLawR4_E_4_end_7

end Fresh.OneMover
