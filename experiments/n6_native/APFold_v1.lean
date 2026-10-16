import Mathlib
import LonelyRunner.LRC.Defs

/-!
# The AP plus one runner, at every order (n6_native, E74, E75, E79)

The runners `1, …, n − 2` and one more runner `X > n − 2`, threshold `1/n`.

* `X` not a multiple of `n`: the global-isolation instant `1/n` is lonely (`ap_plus_one_unit`).
* `X` a multiple of `n`: `X` sits on the subject at `1/n`; the instant `1/n + 1/(nX)`, where `X` re-enters on its
  next lap, is lonely (`ap_plus_one_fold`). The runners `1, …, n − 2` stay clear across `[1/n, (n−1)/(n(n−2))]`.

`ap_plus_one` combines them. With `n = 6` and `X = lcm(1..Q₀)` this is E73's family; the second instant is the
cascade's (E75: `T = 1/6 + 1/(6L)`).
-/

namespace N6Native

/-- A reading in `[p + 1/n, p + 1 − 1/n]` is at distance at least `1/n` from the integers. -/
theorem clear_of_band_n {n z : ℝ} {p : ℤ} (hn : 0 < n) (h1 : (p : ℝ) + 1 / n ≤ z)
    (h2 : z ≤ (p : ℝ) + 1 - 1 / n) : 1 / n ≤ circDist z := by
  have hpos : 0 < 1 / n := by positivity
  have hfr : Int.fract z = z - p := by
    rw [Int.fract_eq_iff]; exact ⟨by linarith, by linarith, p, by ring⟩
  unfold circDist; rw [hfr]; exact le_min (by linarith) (by linarith)

/-- `X` not a multiple of `n`: lonely at the global-isolation instant `1/n`. -/
theorem ap_plus_one_unit (n X : ℕ) (hn : 3 ≤ n) (hX : ¬ n ∣ X) :
    (∀ k : ℕ, 1 ≤ k → k ≤ n - 2 → (1 / n : ℝ) ≤ circDist (k * (1 / n : ℝ))) ∧
      (1 / n : ℝ) ≤ circDist (X * (1 / n : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  refine ⟨fun k hk1 hk2 => ?_, ?_⟩
  · refine clear_of_band_n (p := 0) hn0 ?_ ?_ <;> simp only [Int.cast_zero, zero_add]
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      push_cast; rw [mul_one_div]; exact div_le_div_of_nonneg_right this hn0.le
    · have hk : (k : ℝ) ≤ n - 2 := by
        have : k + 2 ≤ n := by omega
        have : ((k + 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
        push_cast at this; linarith
      push_cast; rw [mul_one_div, div_le_iff₀ hn0]; field_simp; nlinarith
  · obtain ⟨q, r, hr, hX'⟩ : ∃ q r : ℕ, r < n ∧ X = n * q + r := ⟨X / n, X % n, Nat.mod_lt _ (by omega),
      (Nat.div_add_mod X n).symm⟩
    have hr0 : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with h | h
      · exact absurd ⟨q, by omega⟩ hX
      · exact h
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr0
    have hrn : (r : ℝ) ≤ n - 1 := by
      have : r + 1 ≤ n := by omega
      have : ((r + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
      push_cast at this; linarith
    have e : (X : ℝ) * (1 / n) = ((q : ℤ) : ℝ) + r / n := by
      rw [hX']; push_cast; field_simp
    rw [e]; refine clear_of_band_n (p := q) hn0 ?_ ?_
    · have : 1 / (n : ℝ) ≤ r / n := div_le_div_of_nonneg_right hrR hn0.le
      linarith
    · have : (r : ℝ) / n ≤ 1 - 1 / n := by rw [div_le_iff₀ hn0]; field_simp; linarith
      linarith

/-- `X` a multiple of `n` (`X = n q`, `q ≥ 1`) with `n − 2 < X`: lonely at `1/n + 1/(nX)`, where `X` re-enters. -/
theorem ap_plus_one_fold (n q : ℕ) (hn : 3 ≤ n) (hq : 1 ≤ q) :
    let t : ℝ := ((n * q : ℕ) + 1 : ℝ) / (n * (n * q : ℕ))
    (∀ k : ℕ, 1 ≤ k → k ≤ n - 2 → (1 / n : ℝ) ≤ circDist (k * t)) ∧
      (1 / n : ℝ) ≤ circDist (((n * q : ℕ) : ℝ) * t) := by
  intro t
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hq0 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hX0 : (0 : ℝ) < ((n * q : ℕ) : ℝ) := by push_cast; positivity
  have ht1 : 1 / (n : ℝ) ≤ t := by
    show 1 / (n : ℝ) ≤ ((n * q : ℕ) + 1 : ℝ) / (n * (n * q : ℕ))
    rw [div_le_div_iff₀ hn0 (by positivity)]; nlinarith
  refine ⟨fun k hk1 hk2 => ?_, ?_⟩
  · have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hk : (k : ℝ) ≤ n - 2 := by
      have : k + 2 ≤ n := by omega
      have : ((k + 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
      push_cast at this; linarith
    refine clear_of_band_n (p := 0) hn0 ?_ ?_ <;> simp only [Int.cast_zero, zero_add]
    · push_cast
      have ht0 : 0 ≤ t := le_trans (by positivity) ht1
      nlinarith
    · push_cast
      have key : (n - 2 : ℝ) * t ≤ 1 - 1 / n := by
        show (n - 2 : ℝ) * (((n * q : ℕ) + 1 : ℝ) / (n * (n * q : ℕ))) ≤ 1 - 1 / n
        push_cast
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        field_simp
        nlinarith
      have ht0 : 0 ≤ t := le_trans (by positivity) ht1
      nlinarith
  · have e : ((n * q : ℕ) : ℝ) * t = ((q : ℤ) : ℝ) + 1 / n := by
      show ((n * q : ℕ) : ℝ) * (((n * q : ℕ) + 1 : ℝ) / (n * (n * q : ℕ))) = ((q : ℤ) : ℝ) + 1 / n
      push_cast; field_simp
    rw [e]; refine clear_of_band_n (p := q) hn0 ?_ ?_
    · linarith
    · have : 1 / (n : ℝ) ≤ 1 / 3 := by
        rw [div_le_div_iff₀ hn0 (by norm_num)]
        have : (3 : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      linarith

/-- **The AP `1, …, n − 2` plus any runner `X > n − 2` is lonely at threshold `1/n`.** -/
theorem ap_plus_one (n X : ℕ) (hn : 3 ≤ n) (hX : n - 2 < X) :
    ∃ t : ℝ, 0 < t ∧ (∀ k : ℕ, 1 ≤ k → k ≤ n - 2 → (1 / n : ℝ) ≤ circDist (k * t)) ∧
      (1 / n : ℝ) ≤ circDist (X * t) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  by_cases h : n ∣ X
  · obtain ⟨q, rfl⟩ := h
    have hq : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · subst h0; omega
      · exact h0
    obtain ⟨h1, h2⟩ := ap_plus_one_fold n q hn hq
    refine ⟨_, ?_, h1, h2⟩
    have : (0 : ℝ) < ((n * q : ℕ) : ℝ) := by
      have : 0 < n * q := Nat.mul_pos (by omega) hq
      exact_mod_cast this
    positivity
  · exact ⟨1 / n, by positivity, ap_plus_one_unit n X hn h⟩

/-- **The knot's other side, for the knotted pair (E68).** A lap box dies at a knot: runner `I` (lap `a`) enters at
the instant runner `J` (lap `b`) exits, `(n a + 1) v_J = (n b + n − 1) v_I`. In the box where `J` takes one more lap, the
pair's first condition `(n a + 1) v_J ≤ (n (b+1) + n − 1) v_I` always holds, and the second
`(n (b+1) + 1) v_I ≤ (n a + n − 1) v_J` holds exactly when `2a ≤ (n − 2) b + n − 3`. -/
theorem knot_other_side (n a b : ℕ) (hn : 1 ≤ n) {vI vJ : ℝ} (hI : 0 < vI) (hJ : 0 < vJ)
    (htight : ((n : ℝ) * a + 1) * vJ = ((n : ℝ) * b + n - 1) * vI) :
    (((n : ℝ) * a + 1) * vJ ≤ ((n : ℝ) * (b + 1) + n - 1) * vI) ∧
      ((((n : ℝ) * (b + 1) + 1) * vI ≤ ((n : ℝ) * a + n - 1) * vJ) ↔
        (2 * a : ℝ) ≤ ((n : ℝ) - 2) * b + n - 3) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hA : (0 : ℝ) < (n : ℝ) * a + 1 := by positivity
  refine ⟨by rw [htight]; nlinarith, ?_⟩
  have key : (((n : ℝ) * a + n - 1) * vJ) * ((n : ℝ) * a + 1) = ((n : ℝ) * a + n - 1) * ((n : ℝ) * b + n - 1) * vI := by
    rw [mul_assoc, mul_comm vJ, htight]; ring
  constructor
  · intro h
    have h2 := mul_le_mul_of_nonneg_right h hA.le
    rw [key] at h2
    have h3 : ((n : ℝ) * (b + 1) + 1) * ((n : ℝ) * a + 1) ≤ ((n : ℝ) * a + n - 1) * ((n : ℝ) * b + n - 1) := by
      by_contra hc; push Not at hc; nlinarith
    nlinarith
  · intro h
    have h3 : ((n : ℝ) * (b + 1) + 1) * ((n : ℝ) * a + 1) ≤ ((n : ℝ) * a + n - 1) * ((n : ℝ) * b + n - 1) := by nlinarith
    have h4 : ((n : ℝ) * (b + 1) + 1) * vI * ((n : ℝ) * a + 1) ≤ (((n : ℝ) * a + n - 1) * vJ) * ((n : ℝ) * a + 1) := by
      rw [key]; nlinarith
    exact le_of_mul_le_mul_right h4 hA

end N6Native

#print axioms N6Native.ap_plus_one
#print axioms N6Native.knot_other_side
