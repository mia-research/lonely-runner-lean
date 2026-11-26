import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.AdmissibleFlank

/-!
# A reference opening carries an entire compact block

Worklist G04, G12, H06, A04.  The reference is a common reading `x`;
each block reading is `x + δ`, so at its opening its phase changes by
exactly `δ * t`.  The unchanged low readings retain their explicit bands.
No global time bound or stopping principle is assumed.

The integer ceiling locates a specific opening, rather than a sampled point.
The opening-spacing step is [PROVISIONAL: counting tool], supporting the
claim that this opening lies between `lo` and `lo + 1/x`.
-/

namespace Fresh.OpeningClump

open Fresh

noncomputable def openingAfter (x lo : ℝ) : ℝ :=
  (((⌈x * lo - 1 / 8⌉ : ℤ) : ℝ) + 1 / 8) / x

theorem openingAfter_spec {x lo : ℝ} (hx : 0 < x) :
    lo ≤ openingAfter x lo ∧ openingAfter x lo < lo + 1 / x ∧
      x * openingAfter x lo = (⌈x * lo - 1 / 8⌉ : ℤ) + 1 / 8 := by
  have h1 := Int.le_ceil (x * lo - 1 / 8)
  have h2 := Int.ceil_lt_add_one (x * lo - 1 / 8)
  unfold openingAfter
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ hx]
    nlinarith
  · rw [div_lt_iff₀ hx]
    have he : (lo + 1 / x) * x = x * lo + 1 := by field_simp
    rw [he]
    linarith
  · field_simp

/-- The deviation of every block reading is nonnegative and at most `w`.
At the same reference opening this gives its entire clear band. -/
theorem clump_at_opening {C : Finset ℝ} {x w t : ℝ} {N : ℤ}
    (ht : 0 ≤ t) (hopen : x * t = (N : ℝ) + 1 / 8)
    (hC : ∀ d ∈ C, x ≤ d ∧ d ≤ x + w) (hw : w * t ≤ 3 / 4) :
    ∀ d ∈ C, (1 / 8 : ℝ) ≤ distInt (d * t) := by
  intro d hd
  obtain ⟨hlo, hhi⟩ := hC d hd
  apply Fresh.Localisation.clear_of_window N
  · have := mul_le_mul_of_nonneg_right hlo ht
    linarith
  · have := mul_le_mul_of_nonneg_right hhi ht
    nlinarith

/-- A concrete opening of the block reference lies in the retained core
interval.  [PROVISIONAL: counting tool] at `openingAfter_spec`, supporting
the placement of this opening in `[lo,hi]`. -/
theorem core_clump_opening {S C : Finset ℝ} {lo hi x w : ℝ}
    (hlo : 0 < lo) (hx : 0 < x) (hw : 0 ≤ w)
    (hS : ∀ t : ℝ, lo ≤ t → t ≤ hi → ∀ d ∈ S, (1 / 8 : ℝ) ≤ distInt (d * t))
    (hC : ∀ d ∈ C, x ≤ d ∧ d ≤ x + w)
    (hfit : lo + 1 / x ≤ hi) (hdev : w * hi ≤ 3 / 4) :
    0 < openingAfter x lo ∧
      (∀ d ∈ S, (1 / 8 : ℝ) ≤ distInt (d * openingAfter x lo)) ∧
      ∀ d ∈ C, (1 / 8 : ℝ) ≤ distInt (d * openingAfter x lo) := by
  obtain ⟨h1, h2, h3⟩ := openingAfter_spec (lo := lo) hx
  have hpos : 0 < openingAfter x lo := hlo.trans_le h1
  have hupper : openingAfter x lo ≤ hi := h2.le.trans hfit
  refine ⟨hpos, hS _ h1 hupper, clump_at_opening hpos.le h3 hC ?_⟩
  exact (mul_le_mul_of_nonneg_left hupper hw).trans hdev

/-- A single slow reading with a fast block of arbitrary real readings.
The named instant is the reference block's opening after `1/(8s)`.
No lower-order theorem, clump cardinality, or commensurability is needed. -/
theorem single_slow_opening {C : Finset ℝ} {s x w : ℝ}
    (hs : 0 < s) (hx : 0 < x) (hw : 0 ≤ w)
    (hC : ∀ d ∈ C, x ≤ d ∧ d ≤ x + w)
    (hsep : 4 * s ≤ 3 * x)
    (hdev : w * (1 / (8 * s) + 1 / x) ≤ 3 / 4) :
    0 < openingAfter x (1 / (8 * s)) ∧
      (1 / 8 : ℝ) ≤ distInt (s * openingAfter x (1 / (8 * s))) ∧
      ∀ d ∈ C, (1 / 8 : ℝ) ≤ distInt (d * openingAfter x (1 / (8 * s))) := by
  obtain ⟨h1, h2, h3⟩ := openingAfter_spec (lo := 1 / (8 * s)) hx
  have hpos : 0 < openingAfter x (1 / (8 * s)) := lt_of_lt_of_le (by positivity) h1
  have hbound : 1 / (8 * s) + 1 / x ≤ 7 / (8 * s) := by
    have hi : 1 / x ≤ 3 / (4 * s) := by
      rw [div_le_div_iff₀ hx (by positivity)]
      nlinarith
    have he : 7 / (8 * s) - 1 / (8 * s) = 3 / (4 * s) := by ring
    linarith
  refine ⟨hpos, ?_, clump_at_opening hpos.le h3 hC ?_⟩
  · apply Fresh.Localisation.clear_of_window (0 : ℤ)
    · norm_num only [Int.cast_zero, zero_add]
      have := mul_le_mul_of_nonneg_left h1 hs.le
      have he : s * (1 / (8 * s)) = 1 / 8 := by field_simp
      linarith
    · norm_num only [Int.cast_zero, zero_add]
      have := mul_le_mul_of_nonneg_left (h2.le.trans hbound) hs.le
      have he : s * (7 / (8 * s)) = 7 / 8 := by field_simp
      linarith
  · exact (mul_le_mul_of_nonneg_left h2.le hw).trans hdev

-- STANDING: DEFINITION
def OpeningClumpClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (s x w : ℝ) (C : Finset ℝ), 0 < s ∧ 0 < x ∧ 0 ≤ w ∧
    (∀ d ∈ C, x ≤ d ∧ d ≤ x + w) ∧ 4 * s ≤ 3 * x ∧
    w * (1 / (8 * s) + 1 / x) ≤ 3 / 4 ∧
    ∀ d, d ∈ disparitySet v k ↔ d = s ∨ d ∈ C

theorem openingClump_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : OpeningClumpClass v k) : Isolation v k := by
  obtain ⟨s, x, w, C, hs, hx, hw, hC, hsep, hdev, hmem⟩ := h
  obtain ⟨ht, hslow, hfast⟩ := single_slow_opening hs hx hw hC hsep hdev
  refine ⟨openingAfter x (1 / (8 * s)), ht, ?_⟩
  rw [Fresh.Localisation.isolatedAt_iff]
  intro d hd
  rcases (hmem d).1 hd with rfl | h
  · exact hslow
  · exact hfast d h

#print axioms openingAfter_spec
#print axioms clump_at_opening
#print axioms core_clump_opening
#print axioms single_slow_opening
#print axioms openingClump_isolation

end Fresh.OpeningClump
