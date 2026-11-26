import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Cascade
import Fresh.OneMoverA
import Fresh.CascadeLanding
import Fresh.CascadeLandingG
import Fresh.CascadeLanding2
import Fresh.CascadeLanding2b
import Fresh.CascadeLanding3
import Fresh.S2CleanLemmas
import Fresh.S3CoverLemmas

/-!
# Three movers, second cover: box-form leaf lemmas (S3Cover2)

Written 2026-10-23.  New file.  The leaf rules of `S3CoverLemmas` (`r2_rect`, `r3_rect`, `wit3`) restated with the box bounds as hypotheses
(`A ≤ d`, `d ≤ B`), so that a leaf of the box cover is closed by `norm_num` on numerals alone (no `linarith`):
* `r2_box` (rule R2): movers `da`, `db` with `Aa ≤ da ≤ Ba`, `Ab ≤ db ≤ Bb` both clear on all of `[p, q]` (one window each, checked on the
  box corners), third mover `Ac ≤ dc` with `1 ≤ 4 Ac (q - p)`;
* `r3_box` (rule R3): mover `dX` with `AX ≤ dX ≤ BX` clear on all of `[p, q]`, the other two `dY ≤ dZ`, `A ≤ dY`, `p + 1/A ≤ q`;
* `wit3_box` (point witness P).
Grades: [L]; `r2_box`, `r3_box` are **[PROVISIONAL: counting tool]** (a clear window of one mover against the period of another).
-/

open Classical

namespace Fresh.OneMover

open Fresh

theorem r2_box {da db dc Aa Ba Ab Bb Ac l r p q : ℝ} (na nb : ℤ) (hAa : Aa ≤ da) (hBa : da ≤ Ba) (hAb : Ab ≤ db) (hBb : db ≤ Bb)
    (hAc : Ac ≤ dc) (hAa0 : 0 < Aa) (hAb0 : 0 < Ab) (hAc0 : 0 < Ac) (hp : 0 ≤ p) (hq : 0 ≤ q) (hl : l ≤ p) (hr : q ≤ r)
    (h1 : (na : ℝ) + 1 / 8 ≤ Aa * p) (h2 : Ba * q ≤ (na : ℝ) + 7 / 8)
    (h3 : (nb : ℝ) + 1 / 8 ≤ Ab * p) (h4 : Bb * q ≤ (nb : ℝ) + 7 / 8) (hw : 1 ≤ 4 * Ac * (q - p)) :
    ∃ t, l ≤ t ∧ t ≤ r ∧ (1 / 8 : ℝ) ≤ distInt (da * t) ∧ (1 / 8 : ℝ) ≤ distInt (db * t) ∧ (1 / 8 : ℝ) ≤ distInt (dc * t) := by
  have hpq : p ≤ q := by
    by_contra h
    push Not at h
    nlinarith
  apply r2_rect na nb (lt_of_lt_of_le hAa0 hAa) (lt_of_lt_of_le hAb0 hAb) (lt_of_lt_of_le hAc0 hAc) hl hr
  · have := mul_le_mul_of_nonneg_right hAa hp; linarith
  · have := mul_le_mul_of_nonneg_right hBa hq; linarith
  · have := mul_le_mul_of_nonneg_right hAb hp; linarith
  · have := mul_le_mul_of_nonneg_right hBb hq; linarith
  · have h5 : Ac * (q - p) ≤ dc * (q - p) := mul_le_mul_of_nonneg_right hAc (by linarith)
    nlinarith

theorem r3_box {dX dY dZ AX BX A l r p q : ℝ} (n : ℤ) (hAX : AX ≤ dX) (hBX : dX ≤ BX) (hAY : A ≤ dY) (hYZ : dY ≤ dZ)
    (hAX0 : 0 < AX) (hA : 0 < A) (hp : 0 ≤ p) (hq : 0 ≤ q) (hl : l ≤ p) (hr : q ≤ r)
    (h1 : (n : ℝ) + 1 / 8 ≤ AX * p) (h2 : BX * q ≤ (n : ℝ) + 7 / 8) (hw : p + 1 / A ≤ q) :
    ∃ t, l ≤ t ∧ t ≤ r ∧ (1 / 8 : ℝ) ≤ distInt (dX * t) ∧ (1 / 8 : ℝ) ≤ distInt (dY * t) ∧ (1 / 8 : ℝ) ≤ distInt (dZ * t) := by
  apply r3_rect n (lt_of_lt_of_le hAX0 hAX) hA hAY hYZ hl hr
  · have := mul_le_mul_of_nonneg_right hAX hp; linarith
  · have := mul_le_mul_of_nonneg_right hBX hq; linarith
  · exact hw

theorem wit3_box {d1 d2 d3 A1 B1 A2 B2 A3 B3 t : ℝ} (n1 n2 n3 : ℤ) (hA1 : A1 ≤ d1) (hB1 : d1 ≤ B1) (hA2 : A2 ≤ d2) (hB2 : d2 ≤ B2)
    (hA3 : A3 ≤ d3) (hB3 : d3 ≤ B3) (ht : 0 ≤ t)
    (h1 : (n1 : ℝ) + 1 / 8 ≤ A1 * t) (h1' : B1 * t ≤ (n1 : ℝ) + 7 / 8)
    (h2 : (n2 : ℝ) + 1 / 8 ≤ A2 * t) (h2' : B2 * t ≤ (n2 : ℝ) + 7 / 8)
    (h3 : (n3 : ℝ) + 1 / 8 ≤ A3 * t) (h3' : B3 * t ≤ (n3 : ℝ) + 7 / 8) : Clear3 d1 d2 d3 t := by
  apply wit3 n1 n2 n3
  · have := mul_le_mul_of_nonneg_right hA1 ht; linarith
  · have := mul_le_mul_of_nonneg_right hB1 ht; linarith
  · have := mul_le_mul_of_nonneg_right hA2 ht; linarith
  · have := mul_le_mul_of_nonneg_right hB2 ht; linarith
  · have := mul_le_mul_of_nonneg_right hA3 ht; linarith
  · have := mul_le_mul_of_nonneg_right hB3 ht; linarith

#print axioms r2_box
#print axioms r3_box
#print axioms wit3_box

end Fresh.OneMover
