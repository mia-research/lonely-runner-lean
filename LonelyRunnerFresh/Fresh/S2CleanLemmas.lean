import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Cascade
import Fresh.OneMoverA
import Fresh.CascadeLanding
import Fresh.CascadeLandingG
import Fresh.CascadeLanding2
import Fresh.CascadeLanding2b

/-!
# Two movers: witness lemmas for a common clear instant in an interval (S2Clean)

Written 2026-10-23.  New file.  Four lemmas used by the `S2Clean_<set>` files to certify a box of mover pairs `(d1, d2)`:
* `clear2_symm`: `Clear2` is symmetric;
* `wit_pt`: a point witness (`d1 t`, `d2 t` each inside a clear window `[n + 1/8, n + 7/8]`);
* `r1_rect` (**rule R1**): if the slower-or-either mover `d1` is clear on all of `[p, q] ⊆ [l, r]` (one window) and
  `q - p ≥ 1/(4 d2)`, the mover `d2` has a clear instant in `[p, q]` (`opening_close`, `firstPt`), hence a common clear
  instant in `[l, r]`;
* `big_both`: both movers at least `D` with `l + 1/D ≤ r` (`two_clear_in2`).
Grades: [L]; `r1_rect` and `big_both` are **[PROVISIONAL: counting tool]** (a clear window of one mover against the
period of the other).
-/

open Classical

namespace Fresh.OneMover

open Fresh

theorem clear2_symm {d1 d2 t : ℝ} (h : Clear2 d1 d2 t) : Clear2 d2 d1 t := ⟨h.2, h.1⟩

/-- A point witness. -/
theorem wit_pt {d1 d2 t : ℝ} (n1 n2 : ℤ) (h1 : (n1 : ℝ) + 1 / 8 ≤ d1 * t) (h1' : d1 * t ≤ (n1 : ℝ) + 7 / 8)
    (h2 : (n2 : ℝ) + 1 / 8 ≤ d2 * t) (h2' : d2 * t ≤ (n2 : ℝ) + 7 / 8) : Clear2 d1 d2 t :=
  ⟨Fresh.Localisation.clear_of_window n1 h1 h1', Fresh.Localisation.clear_of_window n2 h2 h2'⟩

/-- **Rule R1** (rectangle form).  `d1` is clear on the whole of `[p, q]`, and `[p, q]` is at least `1/(4 d2)` long. -/
theorem r1_rect {d1 d2 l r p q : ℝ} (n : ℤ) (hd1 : 0 < d1) (hd2 : 0 < d2) (hl : l ≤ p) (hr : q ≤ r)
    (h1 : (n : ℝ) + 1 / 8 ≤ d1 * p) (h2 : d1 * q ≤ (n : ℝ) + 7 / 8) (hw : 1 ≤ 4 * d2 * (q - p)) :
    ∃ t, l ≤ t ∧ t ≤ r ∧ Clear2 d1 d2 t := by
  have hq : 1 / (4 * d2) ≤ q - p := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hpq : p ≤ q := by
    have : 0 < 1 / (4 * d2) := by positivity
    linarith
  have hhold : Holds d2 p q := by
    by_cases hc : (1 / 8 : ℝ) ≤ distInt (d2 * p)
    · exact Or.inl hc
    · right
      have := opening_close hd2 hc
      linarith
  obtain ⟨hcl, hl1, hl2, _⟩ := holds_clear hd2 hpq hhold
  refine ⟨firstPt d2 p, by linarith, by linarith, ?_, hcl⟩
  apply Fresh.Localisation.clear_of_window n
  · have := mul_le_mul_of_nonneg_left hl1 hd1.le; linarith
  · have := mul_le_mul_of_nonneg_left hl2 hd1.le; linarith

/-- Both movers at least `D`, and `l + 1/D ≤ r`. -/
theorem big_both {d1 d2 l r D : ℝ} (hD : 0 < D) (hw : l + 1 / D ≤ r) (h1 : D ≤ d1) (h2 : D ≤ d2) :
    ∃ t, l ≤ t ∧ t ≤ r ∧ Clear2 d1 d2 t := by
  have hd1 : 0 < d1 := lt_of_lt_of_le hD h1
  have hd2 : 0 < d2 := lt_of_lt_of_le hD h2
  have hle : ∀ d : ℝ, D ≤ d → 1 / d ≤ 1 / D := fun d hd => one_div_le_one_div_of_le hD hd
  rcases le_total d1 d2 with h | h
  · exact two_clear_in2 (l := l) (r := r) hd1 h (by linarith [hle d1 h1])
  · obtain ⟨t, a, b, c⟩ := two_clear_in2 (l := l) (r := r) hd2 h (by linarith [hle d2 h2])
    exact ⟨t, a, b, clear2_symm c⟩

#print axioms clear2_symm
#print axioms wit_pt
#print axioms r1_rect
#print axioms big_both

end Fresh.OneMover
