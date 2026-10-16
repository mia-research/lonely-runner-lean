import LonelyRunner.LRC.Spec.OrderSixEightNativeN

/-!
# The corner lemma (n6_native, E89)

At a residue-isolation arrangement `d` (residues `1, …, 5` mod 6, one each) the lonely points are `1/6` and `5/6`, with
lap boxes `K = ⌊d/6⌋` and `K' = ⌊5d/6⌋`. In each box every pair condition is strict at `d` except the entry/exit pair
(`e`, the residue-1 runner, and `x`, the residue-5 runner), and the two exceptional conditions are the two sides of one
hyperplane: `d_e v_x ≤ d_x v_e` and `d_x v_e ≤ d_e v_x` (`5 d_x = 6K'_x + 1`, `5 d_e = 6K'_e + 5`). So near `d` one of the
two boxes always holds (`corner_two_boxes`). The same holds at any simple degenerate point (E23 `mirror_opening`), e.g.
the tight set (1,3,4,5,9).
-/

namespace N6Native
open LRC.S8Native

/-- **Two boxes meeting on one hyperplane.** If box `K` holds except possibly for the pair `(e, x)`, box `K'` holds
except possibly for `(x, e)`, and those two conditions are complementary
(`(6K_e+1)(6K'_x+1) = (6K_x+5)(6K'_e+5)`, all positive), then one of the boxes holds, so the arrangement is lonely. -/
theorem corner_two_boxes (v : Fin 5 → ℝ) (hv : ∀ i, 0 < v i) (K K' : Fin 5 → ℕ) (e x : Fin 5)
    (hK : ∀ i j, ¬ (i = e ∧ j = x) → (6 * (K i : ℝ) + 1) * v j ≤ (6 * (K j : ℝ) + 5) * v i)
    (hK' : ∀ i j, ¬ (i = x ∧ j = e) → (6 * (K' i : ℝ) + 1) * v j ≤ (6 * (K' j : ℝ) + 5) * v i)
    (hc : (6 * (K e : ℝ) + 1) * (6 * (K' x : ℝ) + 1) = (6 * (K x : ℝ) + 5) * (6 * (K' e : ℝ) + 5)) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, (6 : ℝ)⁻¹ ≤ circDist (v i * t) := by
  have pe : (0 : ℝ) < 6 * (K e : ℝ) + 1 := by positivity
  have px : (0 : ℝ) < 6 * (K x : ℝ) + 5 := by positivity
  have qx : (0 : ℝ) < 6 * (K' x : ℝ) + 1 := by positivity
  have qe : (0 : ℝ) < 6 * (K' e : ℝ) + 5 := by positivity
  rcases le_total ((6 * (K e : ℝ) + 1) * v x) ((6 * (K x : ℝ) + 5) * v e) with h | h
  · exact box5' v K hv (fun i j => by
      by_cases hij : i = e ∧ j = x
      · obtain ⟨rfl, rfl⟩ := hij; exact h
      · exact hK i j hij)
  · refine box5' v K' hv (fun i j => ?_)
    by_cases hij : i = x ∧ j = e
    · obtain ⟨rfl, rfl⟩ := hij
      have h2 : (6 * (K' i : ℝ) + 1) * ((6 * (K i : ℝ) + 5) * v j) ≤ (6 * (K' i : ℝ) + 1) * ((6 * (K j : ℝ) + 1) * v i) :=
        mul_le_mul_of_nonneg_left h qx.le
      have : (6 * (K i : ℝ) + 5) * ((6 * (K' i : ℝ) + 1) * v j) ≤ (6 * (K i : ℝ) + 5) * ((6 * (K' j : ℝ) + 5) * v i) := by
        calc (6 * (K i : ℝ) + 5) * ((6 * (K' i : ℝ) + 1) * v j)
            = (6 * (K' i : ℝ) + 1) * ((6 * (K i : ℝ) + 5) * v j) := by ring
          _ ≤ (6 * (K' i : ℝ) + 1) * ((6 * (K j : ℝ) + 1) * v i) := h2
          _ = ((6 * (K j : ℝ) + 1) * (6 * (K' i : ℝ) + 1)) * v i := by ring
          _ = ((6 * (K i : ℝ) + 5) * (6 * (K' j : ℝ) + 5)) * v i := by rw [hc]
          _ = (6 * (K i : ℝ) + 5) * ((6 * (K' j : ℝ) + 5) * v i) := by ring
      exact le_of_mul_le_mul_left this px
    · exact hK' i j hij

end N6Native

#print axioms N6Native.corner_two_boxes
