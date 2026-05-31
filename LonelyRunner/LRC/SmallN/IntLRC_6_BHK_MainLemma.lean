import LonelyRunner.LRC.SmallN.IntLRC_6_BHK_Defs

/-!
# BHK §3 — Main Lemma and Corollary 6 (2-torus subgroup ↔ rectangle)

The Main Lemma says: a finite cyclic subgroup `G ⊆ T = [0,1)²` of order `n`
intersects every `α × β` rectangle whenever `αβ ≥ 1/n`, modulo two
exceptional configurations (a small lattice point `(i,j) ∈ ℤ²` close to the
origin lying in `G` after scaling).

Corollary 6 packages the applied form used by §§5–8.

## Source

T. Bohman, R. Holzman, D. Kleitman, *Six Lonely Runners*, EJC **8** (2001)
R3, §3 (p5–11) — proof in §§3.1, 3.2; minimality refinement in §3.3.
-/

open MeasureTheory Set

namespace BHK

/-- **BHK Main Lemma.** Let `G ⊆ ℝ²` be a finite cyclic subgroup mod 1 in
    each coordinate, of order `n > 1`, and let `0 < α, β < 1` with
    `α · β ≥ 1 / n`. Then `G` intersects every `α × β` rectangle, unless
    there exists a nonzero `(i, j) ∈ ℤ²` with `(i/n, j/n) ∈ G` satisfying
    `β|i| + α|j| - (2/n)|i||j| < 1`. -/
theorem bhk_main_lemma
    (G : Set (ℝ × ℝ)) (hG_fin : G.Finite) (n : ℕ) (hn : 1 < n)
    (hG_card : G.ncard = n)
    (α β : ℝ) (hα : 0 < α) (hα' : α < 1) (hβ : 0 < β) (hβ' : β < 1)
    (hαβ : α * β ≥ 1 / (n : ℝ)) :
    (∀ x₁ x₂, (G ∩ bhkRectangle x₁ x₂ α β).Nonempty) ∨
    (∃ ij : ℤ × ℤ, ij ≠ (0, 0) ∧
      ((ij.1 : ℝ) / n, (ij.2 : ℝ) / n) ∈ G ∧
      β * |(ij.1 : ℝ)| + α * |(ij.2 : ℝ)| - 2 / n * |(ij.1 : ℝ)| * |(ij.2 : ℝ)| < 1) := by
  sorry

/-- **BHK Corollary 6.** Applied form of the Main Lemma: either every
    `α × β` rectangle is hit, or there is a small lattice point `(i, j)`
    with `(i/n, j/n) ∈ G` satisfying explicit linear inequalities. -/
theorem bhk_corollary_6
    (G : Set (ℝ × ℝ)) (hG_fin : G.Finite) (n : ℕ) (hn : 1 < n)
    (hG_card : G.ncard = n)
    (α β : ℝ) (hα : 0 < α) (hα' : α < 1) (hβ : 0 < β) (hβ' : β < 1) :
    (∀ x₁ x₂, (G ∩ bhkRectangle x₁ x₂ α β).Nonempty) ∨
    (∃ ij : ℤ × ℤ, ij ≠ (0, 0) ∧
      ((ij.1 : ℝ) / n, (ij.2 : ℝ) / n) ∈ G ∧
      0 ≤ ij.1 ∧ (ij.1 : ℝ) < 1 / β ∧
      -1 / α - β / α * ij.1 < (ij.2 : ℝ) ∧
      (ij.2 : ℝ) < 1 / α + β / α * ij.1) := by
  sorry

end BHK
