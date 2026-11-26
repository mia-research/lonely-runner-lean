import Fresh.TwoMoverSubjectBand
import Fresh.SelfMoverCommon

/-!
Rules: 1–4, 8–18. A04/A05, subject among the two moved runners.
Six speeds c+1,...,c+6 remain on the AP; subject 0 moves to c+x and
runner 7 to y. For x<1/6 and d=|y-(c+x)| with d≥1-x and
2(1-x)(6-x)≤(1-6x)d, the actual cascade from the subject's least
reading has its first isolation either at its start or at the outsider's
next opening. This is an unbounded real two-parameter family, with exact
closed retention edge. The IsArrangement hypothesis retains positivity
and all physical collision exclusions. No imported smaller-order proof.
-/

open Classical
namespace Fresh.OneMover
open Fresh

/-- Exact disparity geometry for the moved end subject. -/
theorem subject_end_shape (c x y : ℝ) (hx : x < 1/6) :
    let v := twoMover c (c+x) y (0 : Fin 8) (7 : Fin 8)
    (1-x) ∈ disparitySet v 0 ∧
    |y-(c+x)| ∈ disparitySet v 0 ∧
    ∀ e ∈ disparitySet v 0, e = |y-(c+x)| ∨ (1-x ≤ e ∧ e ≤ 6-x) := by
  dsimp
  have hv0 : twoMover c (c+x) y (0 : Fin 8) 7 0 = c+x := by simp [twoMover]
  refine ⟨?_, ?_, ?_⟩
  · apply Finset.mem_image.mpr
    refine ⟨(1 : Fin 8), by simp, ?_⟩
    rw [hv0]
    simp only [twoMover, show (1 : Fin 8) ≠ 0 by decide, show (1 : Fin 8) ≠ 7 by decide, ↓reduceIte]
    norm_num
    linarith
  · apply Finset.mem_image.mpr
    refine ⟨(7 : Fin 8), by simp, ?_⟩
    simp [twoMover]
  · intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    have hi0 : i ≠ (0 : Fin 8) := (Finset.mem_erase.mp hi).1
    rw [hv0]
    by_cases hi7 : i = (7 : Fin 8)
    · left
      simp [twoMover, hi7]
    · right
      have hil : 1 ≤ (i : ℕ) := by have := i.isLt; have := Fin.val_ne_of_ne hi0; simp at this; omega
      have hir : (i : ℕ) ≤ 6 := by have := i.isLt; have := Fin.val_ne_of_ne hi7; simp at this; omega
      have hilR : (1 : ℝ) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hil
      have hirR : (((i : ℕ) : ℝ)) ≤ 6 := by exact_mod_cast hir
      simp only [twoMover, hi0, hi7, ↓reduceIte]
      rw [show c+((i : ℕ) : ℝ)-(c+x) = ((i : ℕ) : ℝ)-x by ring,
        abs_of_pos (by linarith)]
      constructor <;> linarith

/-- Consuming theorem for the physical two-mover family. It names the native
first isolation and the actual initial cascade move, including fixed starts. -/
theorem subject_end_first (c x y : ℝ)
    (hphysical : IsArrangement (twoMover c (c+x) y (0 : Fin 8) 7))
    (hx : x < 1/6) (hd : 1-x ≤ |y-(c+x)|)
    (hretain : 2*(1-x)*(6-x) ≤ (1-6*x)*|y-(c+x)|) :
    ∃ T : ℝ, 0 < T ∧
      IsMove (disparitySet (twoMover c (c+x) y (0 : Fin 8) 7) 0) (1/(8*(1-x))) T ∧
      FirstIso (twoMover c (c+x) y (0 : Fin 8) 7) 0 T := by
  obtain ⟨ha, hdmem, hshape⟩ := subject_end_shape c x y hx
  obtain ⟨T, hlo, hm, hl, hfirst⟩ := subject_band_first
    (by linarith : 0 < 1-x) (by linarith : 1-x ≤ 6-x) hd ha hdmem hshape
    (by nlinarith : 2*(1-x)*(6-x) ≤ (7*(1-x)-(6-x))*|y-(c+x)|)
  have hapos : 0 < 1-x := by linarith
  refine ⟨T, lt_of_lt_of_le (by positivity) hlo, hm, ?_, ?_⟩
  · exact (Fresh.Cascade.isolatedAt_iff_lonelyAt _ _ _).2 hl
  · intro s hs hsiso
    exact hfirst s hs ((Fresh.Cascade.isolatedAt_iff_lonelyAt _ _ _).1 hsiso)

#print axioms subject_end_shape
#print axioms subject_end_first
end Fresh.OneMover
