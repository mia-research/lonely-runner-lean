import LonelyRunner.LRC.Cascade.Flanks

/-!
# The cascade's first move, and the §8 start (observations formalised)

Observed on 17,135 order-six residual sets (`six_first_setter_v1.out`, 0 mismatches): the first move
from `1/(n·D)` goes to the latest next opening among the elements in the way, and an element `d` is in
the way exactly when `|d/D − n·N| < 1` for an integer `N`. In BHK's §8 case (`v₃ ≤ 3v₁`) only `v₄`, `v₅`
are ever in the way at the start. Both are packaged here from existing framework lemmas; nothing here
is new mathematics.
-/

namespace CascadeFirstMove

open MomentIterationN

variable {n : ℕ} [Fact (2 ≤ n)]

/-- **The first move.** From `1/(n·D)` the move either stays (no element in the way) or lands on the
next opening of an element in the way, and that opening is the latest among the elements in the way.
Being in the way is the ratio test `|d/D − n·N| < 1`, and the opening is `1/(n·(d/(n·N+1)))`. -/
theorem first_move {ds : Finset ℝ} {D : ℝ} (hD : 0 < D) (hpos : ∀ d ∈ ds, 0 < d) :
    (∀ d ∈ ds, inWay n d (1 / (n * D)) ↔ ∃ N : ℤ, |d / D - n * N| < 1) ∧
    (move n ds (1 / (n * D)) = 1 / (n * D) ∨
      ∃ d ∈ ds, inWay n d (1 / (n * D)) ∧
        move n ds (1 / (n * D)) = nextOpening n d (1 / (n * D)) ∧
        ∀ d' ∈ ds, inWay n d' (1 / (n * D)) →
          nextOpening n d' (1 / (n * D)) ≤ nextOpening n d (1 / (n * D))) ∧
    (∀ d ∈ ds, ∀ N : ℤ, |d / D - n * N| < 1 →
      nextOpening n d (1 / (n * D)) = 1 / (n * (d / (n * N + 1)))) := by
  refine ⟨fun d _ => inWay_at_scale_iff hD, ?_, fun d hd N hN => nextOpening_at_scale (hpos d hd) hD hN⟩
  rcases move_eq_self_or_opening (n := n) ds (1 / (n * D)) with h | ⟨d, hd, hw, he⟩
  · exact Or.inl h
  · refine Or.inr ⟨d, hd, hw, he, fun d' hd' hw' => ?_⟩
    rw [← he]; exact nextOpening_le_move hd' hw'

/-- **The §8 start.** If `v₁ ≤ d ≤ (n − 1)·v₁`, then `d` is clear at `1/(n·v₁)`. At `n = 6` with
`v₁ < v₂ < v₃ ≤ 3v₁`, the three slowest are clear at the start, so only `v₄`, `v₅` can set the first
move. (`Flanks.clear_at_bound_of_ratio`, the first opening of the least flank.) -/
theorem s8_slow_three_clear {v1 d : ℝ} (hv1 : 0 < v1) (h1 : v1 ≤ d) (h3 : d ≤ 3 * v1) :
    ((6 : ℕ) : ℝ)⁻¹ ≤ circDist (d * (1 / ((6 : ℕ) * v1))) := by
  haveI : Fact (2 ≤ 6) := ⟨by norm_num⟩
  have h5 : d ≤ (((6 : ℕ) : ℝ) - 1) * v1 := by push_cast; linarith
  have := Flanks.clear_at_bound_of_ratio (n := 6) hv1 h1 h5
  have e : Flanks.flankOpening 6 v1 0 = 1 / ((6 : ℕ) * v1) := by
    unfold Flanks.flankOpening; push_cast; field_simp; ring
  rwa [e] at this

end CascadeFirstMove

#print axioms CascadeFirstMove.first_move
#print axioms CascadeFirstMove.s8_slow_three_clear
