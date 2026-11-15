import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.PathLaws
import Fresh.Grid
import Fresh.ClusterTransfer
import Fresh.FastPairReal
import Fresh.Cascade

/-!
# Bounded gaps for one and two fast readings, and the slow-cluster transfer they give

Written 2026-10-25.  New file.  Worklist tags: G03 (low cluster and one high outlier, 6 | 1), G05 (low cluster and two high readings, 5 | 2), H06 (slow group against a fast group), A08 (closed edges).
`single_gap`: a single reading `x` is `1/8`-clear somewhere in every interval of length `1/(4x)`.  `pair_gap`: two arbitrary positive reals `a ≤ b` are jointly clear somewhere in every
interval of length `3/(4a)` (this is `FastPairReal.pair_window`; no commensurability).  `fast_single_far`, `fast_pair_far`: with `ClusterTransfer.cluster_transfer_gap`, a slow set `S`
(arbitrary positive reals) clear at gate `γ` at `σ` and one (two) fast readings of size at least `M / (8 (γ - 1/8))` (`3 M / (8 (γ - 1/8))`) are jointly clear at one instant.
At gate `1/6` the pair threshold is `9 M`, the `FastPairClass` slack (`FastPairReal`); at gate `1/7` the single threshold is `7 M`.  Mechanisms: M-A (window), and the pair window (M-A applied to two readings).  Grade [L].
-/

namespace Fresh.FastGaps

open Fresh Fresh.ClusterTransfer Fresh.FastPairReal

theorem single_gap {x : ℝ} (hx : 0 < x) : ClearGap {x} (1 / (4 * x)) := by
  intro a
  obtain ⟨w, hw1, hw2, m, hm1, hm2⟩ := exists_band_point (x * a)
  refine ⟨w / x, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hx]; linarith
  · rw [div_le_iff₀ hx]
    have : (a + 1 / (4 * x)) * x = x * a + 1 / 4 := by field_simp
    linarith
  · intro f hf
    rw [Finset.mem_singleton] at hf
    subst hf
    rw [show f * (w / f) = w by field_simp]
    exact Fresh.Localisation.clear_of_window m hm1 (by linarith)

theorem pair_gap {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : ClearGap {a, b} (3 / (4 * a)) := by
  intro x
  obtain ⟨t, h1, h2, h3, h4⟩ := pair_window ha hab x
  refine ⟨t, h1, h2, ?_⟩
  intro f hf
  rw [Finset.mem_insert, Finset.mem_singleton] at hf
  rcases hf with rfl | rfl
  · exact h3
  · exact h4

/-- From a blocked instant, the next opening is at most one blocked
interval away and starts a full clear interval. -/
private theorem opening_window {a x : ℝ} (ha : 0 < a) (blocked : InWay a x) :
    x ≤ nextOpening a x ∧ nextOpening a x ≤ x + 1 / (4 * a) ∧
      ∀ t, nextOpening a x ≤ t → t ≤ nextOpening a x + 3 / (4 * a) →
        (1 / 8 : ℝ) ≤ distInt (a * t) := by
  obtain ⟨k, hk⟩ := Fresh.Cascade.exists_near_int blocked
  have he := Fresh.Cascade.nextOpening_eq hk
  have hphase : a * nextOpening a x = (k : ℝ) + 1 / 8 := by
    rw [he, mul_div_cancel₀ _ ha.ne']
  have hstep : a * (1 / (4 * a)) = 1 / 4 := by field_simp
  have hclear : a * (3 / (4 * a)) = 3 / 4 := by field_simp
  refine ⟨(Fresh.Cascade.lt_nextOpening ha blocked).le, ?_, ?_⟩
  · have hlo := (abs_lt.mp hk).1
    apply le_of_mul_le_mul_left _ ha
    rw [mul_add, hstep, hphase]
    linarith
  · intro t ht hu
    apply Fresh.Localisation.clear_of_window k
    · simpa only [hphase] using mul_le_mul_of_nonneg_left ht ha.le
    · have h := mul_le_mul_of_nonneg_left hu ha.le
      rw [mul_add, hclear, hphase] at h
      linarith

/-- At most two short advances and one slow advance are needed. If the
short advances do not fit, the faster reading stays clear during the slow one. -/
theorem pair_gap_half {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ClearGap {a, b} (1 / (2 * a)) := by
  intro x
  have hb := ha.trans_le hab
  have hshort : 1 / (4 * b) ≤ 1 / (4 * a) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hhalf : 1 / (2 * a) = 2 * (1 / (4 * a)) := by ring
  have hlong : 3 / (4 * a) = 3 * (1 / (4 * a)) := by ring
  have select (t : ℝ) (ht : x ≤ t) (hu : t ≤ x + 1 / (2 * a))
      (ca : (1 / 8 : ℝ) ≤ distInt (a * t)) (cb : (1 / 8 : ℝ) ≤ distInt (b * t)) :
      ∃ t : ℝ, x ≤ t ∧ t ≤ x + 1 / (2 * a) ∧
        ∀ f ∈ ({a, b} : Finset ℝ), (1 / 8 : ℝ) ≤ distInt (f * t) := by
    refine ⟨t, ht, hu, fun f hf => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl
    · exact ca
    · exact cb
  by_cases ax : InWay a x
  · obtain ⟨he, hu, hc⟩ := opening_window ha ax
    obtain ⟨t, ht, ht', cb⟩ := single_gap hb (nextOpening a x)
    exact select t (he.trans ht) (by linarith) (hc t ht (by linarith))
      (cb b (Finset.mem_singleton_self b))
  by_cases bx : InWay b x
  · let y := nextOpening b x
    obtain ⟨hy, hy', cy⟩ := opening_window hb bx
    change x ≤ y at hy
    change y ≤ x + 1 / (4 * b) at hy'
    by_cases ay : InWay a y
    · let z := nextOpening a y
      obtain ⟨hz, hz', cz⟩ := opening_window ha ay
      change y ≤ z at hz
      change z ≤ y + 1 / (4 * a) at hz'
      by_cases ratio : b ≤ 2 * a
      · have hh : 1 / (4 * a) ≤ 3 / (4 * b) := by
          rw [le_div_iff₀ (by positivity : 0 < 4 * b)]
          have hm := mul_le_mul_of_nonneg_left ratio
            (by positivity : 0 ≤ 1 / (4 * a))
          have heq : 1 / (4 * a) * (4 * (2 * a)) = 2 := by field_simp
          nlinarith only [hm, heq]
        exact select z (hy.trans hz) (by linarith) (cz z le_rfl (le_add_of_nonneg_right (by positivity : 0 ≤ 3 / (4 * a))))
          (cy z hz (by linarith))
      · have hh : 2 * (1 / (4 * b)) ≤ 1 / (4 * a) := by
          rw [show 2 * (1 / (4 * b)) = 1 / (2 * b) by ring]
          exact one_div_le_one_div_of_le (by positivity) (by linarith)
        obtain ⟨t, ht, ht', cb⟩ := single_gap hb z
        exact select t (hy.trans (hz.trans ht)) (by linarith) (cz t ht (by linarith))
          (cb b (Finset.mem_singleton_self b))
    · exact select y hy (by linarith) (le_of_not_gt ay) (cy y le_rfl (le_add_of_nonneg_right (by positivity : 0 ≤ 3 / (4 * b))))
  · exact select x le_rfl (le_add_of_nonneg_right (by positivity : 0 ≤ 1 / (2 * a))) (le_of_not_gt ax) (le_of_not_gt bx)

/-- Try the existing block first. If its witness is blocked by the new
reading, retry from that reading's next opening. -/
theorem insert_gap {F : Finset ℝ} {a D : ℝ} (ha : 0 < a)
    (short : D ≤ 3 / (4 * a)) (gap : ClearGap F D) :
    ClearGap (insert a F) (2 * D + 1 / (4 * a)) := by
  intro x
  obtain ⟨y, hxy, hy, cy⟩ := gap x
  have hD : 0 ≤ D := by linarith
  have hstep : 0 ≤ 1 / (4 * a) := by positivity
  by_cases blocked : InWay a y
  · obtain ⟨he, hu, hc⟩ := opening_window ha blocked
    obtain ⟨t, ht, ht', ct⟩ := gap (nextOpening a y)
    refine ⟨t, hxy.trans (he.trans ht), by linarith, fun f hf => ?_⟩
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact hc t ht (by linarith)
    · exact ct f hf
  · refine ⟨y, hxy, by linarith, fun f hf => ?_⟩
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact le_of_not_gt blocked
    · exact cy f hf

theorem triple_gap {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) :
    ClearGap {a, b, c} (1 / b + 1 / (4 * a)) := by
  have hb := ha.trans_le hab
  have hle : 1 / (2 * b) ≤ 1 / (2 * a) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hdiff : 3 / (4 * a) - 1 / (2 * a) = 1 / (4 * a) := by ring
  have hpos : 0 ≤ 1 / (4 * a) := by positivity
  have h := insert_gap ha (by linarith : 1 / (2 * b) ≤ 3 / (4 * a))
    (pair_gap_half hb hbc)
  simpa only [show 2 * (1 / (2 * b)) = 1 / b by ring] using h

theorem fast_single_far {S : Finset ℝ} {γ M σ x : ℝ} (hγ : 1 / 8 < γ) (hSne : S.Nonempty) (hSpos : ∀ s ∈ S, 0 < s)
    (hM : ∀ s ∈ S, s ≤ M) (hσ0 : 0 < σ) (hσ : ∀ s ∈ S, γ ≤ distInt (s * σ)) (hx : M ≤ 8 * (γ - 1 / 8) * x) (hxpos : 0 < x) :
    ∃ t : ℝ, 0 < t ∧ (∀ s ∈ S, (1 / 8 : ℝ) ≤ distInt (s * t)) ∧ (1 / 8 : ℝ) ≤ distInt (x * t) := by
  have hL : 1 / (4 * x) * M ≤ 2 * (γ - 1 / 8) := by
    rw [show 1 / (4 * x) * M = M / (4 * x) by ring, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨t, ht, hS, hF⟩ := cluster_transfer_gap hγ hSne hSpos hM hσ0 hσ hL (single_gap hxpos)
  exact ⟨t, ht, hS, hF x (Finset.mem_singleton_self x)⟩

theorem fast_pair_far {S : Finset ℝ} {γ M σ a b : ℝ} (hγ : 1 / 8 < γ) (hSne : S.Nonempty) (hSpos : ∀ s ∈ S, 0 < s)
    (hM : ∀ s ∈ S, s ≤ M) (hσ0 : 0 < σ) (hσ : ∀ s ∈ S, γ ≤ distInt (s * σ)) (hab : a ≤ b) (hapos : 0 < a)
    (ha : 3 * M ≤ 8 * (γ - 1 / 8) * a) :
    ∃ t : ℝ, 0 < t ∧ (∀ s ∈ S, (1 / 8 : ℝ) ≤ distInt (s * t)) ∧ (1 / 8 : ℝ) ≤ distInt (a * t) ∧ (1 / 8 : ℝ) ≤ distInt (b * t) := by
  have hL : 3 / (4 * a) * M ≤ 2 * (γ - 1 / 8) := by
    rw [show 3 / (4 * a) * M = 3 * M / (4 * a) by ring, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨t, ht, hS, hF⟩ := cluster_transfer_gap hγ hSne hSpos hM hσ0 hσ hL (pair_gap hapos hab)
  exact ⟨t, ht, hS, hF a (by simp), hF b (by simp)⟩

#print axioms single_gap
#print axioms pair_gap
#print axioms pair_gap_half
#print axioms triple_gap
#print axioms fast_single_far
#print axioms fast_pair_far

end Fresh.FastGaps
