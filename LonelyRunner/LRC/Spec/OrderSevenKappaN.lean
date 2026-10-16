import LonelyRunner.LRC.Spec.OrderSixWholeN

/-!
# Order seven: the five-runner window at `1/7` from order six

`kappa(P) = v5 * W5(P)`, where `W5(P)` is the longest interval on which five speeds are all in the band
`[1/7, 6/7]`.  Order six (native, `lonely_six_nat`) gives an instant at which all five readings are at
distance at least `1/6` from the integers.  Each reading moves at its own speed, at most `V`, so all
five stay at distance at least `1/7` on the interval of half-width `1/(42 V)`: `kappa >= 1/21`.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.O7Kappa

open LRC.OrderSixN

/-- **Window from order six.**  At most five positive whole numbers bounded by `V` are all at distance
at least `1/7` on a closed interval of half-width `1/(42 V)`. -/
theorem window_of_six (S : Finset ℕ) (hpos : ∀ d ∈ S, 0 < d) (hcard : S.card ≤ 5) {V : ℕ}
    (hV0 : 0 < V) (hV : ∀ d ∈ S, d ≤ V) :
    ∃ t : ℝ, 0 < t ∧ ∀ s : ℝ, |s - t| ≤ 1 / (42 * V) → ∀ d ∈ S, (1 : ℝ) / 7 ≤ circDist ((d : ℝ) * s) := by
  obtain ⟨t, ht, hl⟩ := lonely_six_nat S hpos hcard
  refine ⟨t, ht, fun s hs d hd => ?_⟩
  have h6 := hl d hd
  have hVr : (0 : ℝ) < V := by exact_mod_cast hV0
  have hdV : (d : ℝ) ≤ V := by exact_mod_cast hV d hd
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hlip := circDist_lipschitz.dist_le_mul ((d : ℝ) * s) ((d : ℝ) * t)
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, ← mul_sub, abs_mul, abs_of_nonneg hd0] at hlip
  have hmove : (d : ℝ) * |s - t| ≤ 1 / 42 := by
    calc (d : ℝ) * |s - t| ≤ V * (1 / (42 * V)) :=
          mul_le_mul hdV hs (abs_nonneg _) hVr.le
      _ = 1 / 42 := by field_simp
  have := neg_abs_le (circDist ((d : ℝ) * s) - circDist ((d : ℝ) * t))
  rw [inv_eq_one_div] at h6
  linarith

/-- **`kappa >= 1/21`.**  The window of `window_of_six` has length `1/(21 V)`. -/
theorem kappa_ge (S : Finset ℕ) (hpos : ∀ d ∈ S, 0 < d) (hcard : S.card ≤ 5) {V : ℕ}
    (hV0 : 0 < V) (hV : ∀ d ∈ S, d ≤ V) :
    ∃ L : ℝ, 0 < L + 1 / (42 * V) ∧ ∀ s ∈ Set.Icc L (L + 1 / (21 * V)), ∀ d ∈ S,
      (1 : ℝ) / 7 ≤ circDist ((d : ℝ) * s) := by
  obtain ⟨t, ht, hw⟩ := window_of_six S hpos hcard hV0 hV
  have hVr : (0 : ℝ) < V := by exact_mod_cast hV0
  refine ⟨t - 1 / (42 * V), by linarith, fun s hs d hd => hw s ?_ d hd⟩
  have h2 : (1 : ℝ) / (21 * V) = 2 * (1 / (42 * V)) := by field_simp; norm_num
  rw [abs_le]; constructor <;> linarith [hs.1, hs.2]

end LRC.O7Kappa
