import LonelyRunner.LRC.Spec.OrderSixEightN
import LonelyRunner.LRC.Spec.GlobalIsolationTwoN

/-!
# Order six, BHK §7 (`3 v₁ < v₃`, generic meeting lattice) inside the framework

2026-09-24.  BHK's generic case works on the **meeting times** `τ = k/D`, `D = v₃ − v₂`, where
runners 2 and 3 read the same position — the merge rule, exact.  At such a `τ`:

* runners 2 and 3 stand at a common `x₃`, runner 1 at `x₁`;
* if `x₃ ∈ [1/6, 5/6]` and `x₁` lies in BHK's parallelogram, runners 1–3 are clear across runner
  3's whole clear lap around `τ`, a window of length `2/(3v₃)` (`lonely_of_meeting`);
* the two fast runners cannot block that window: the two-flank window rule (BHK Lemma 4) names a
  lonely instant in it.

Which `k` works comes from global isolation in two dimensions on the orbit
`k ↦ (c₃k mod n, c₁k mod n)` (`GlobalIsolationTwoN.lean`, BHK Main Lemma and Corollary 6).

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.OrderSixN

open MomentIterationN LRC.SpecN ConstructionN

/-- **The meeting-time window (BHK (6) and Corollary 5, framework form).**  At an instant `τ`
where runners 2 and 3 read the same position `x₃ ∈ [1/6, 5/6]` and runner 1 reads `x₁` inside the
parallelogram `1/6 + (x₃ − 1/6)·v₁/v₃ ≤ x₁ ≤ 5/6 − (5/6 − x₃)·v₁/v₃`, runners 1–3 are clear across
runner 3's clear lap around `τ`, and the two fast runners are clear together at a named instant of
it. -/
theorem lonely_of_meeting {v1 v2 v3 v4 v5 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3)
    (h34 : v3 < v4) (h45 : v4 < v5) {τ x3 x1 : ℝ} {q3 q2 q1 : ℤ} (hq3 : 0 ≤ q3)
    (e3 : (v3 : ℝ) * τ = q3 + x3) (e2 : (v2 : ℝ) * τ = q2 + x3) (e1 : (v1 : ℝ) * τ = q1 + x1)
    (hx3a : 1 / 6 ≤ x3) (hx3b : x3 ≤ 5 / 6)
    (hlo : 1 / 6 + (x3 - 1 / 6) * v1 / v3 ≤ x1) (hhi : x1 ≤ 5 / 6 - (5 / 6 - x3) * v1 / v3) :
    ∃ t : ℝ, 0 < t ∧ Lonely6 v1 v2 v3 v4 v5 t := by
  have r1 : (0 : ℝ) < v1 := by exact_mod_cast h0
  have r12 : (v1 : ℝ) < v2 := by exact_mod_cast h12
  have r23 : (v2 : ℝ) < v3 := by exact_mod_cast h23
  have r34 : (v3 : ℝ) < v4 := by exact_mod_cast h34
  have r45 : (v4 : ℝ) < v5 := by exact_mod_cast h45
  have p3 : (0 : ℝ) < v3 := by linarith
  have p4 : (0 : ℝ) < v4 := by linarith
  -- runner 3's clear lap around `τ`
  set A : ℝ := τ - (x3 - 1 / 6) / v3 with hA
  set L : ℝ := 2 / (3 * v3) with hL
  have hAL : A + L = τ + (5 / 6 - x3) / v3 := by rw [hA, hL]; field_simp; ring
  have hLe : 2 / (3 * (v4 : ℝ)) ≤ L := by
    rw [hL, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  obtain ⟨t, ht1, ht2, c4, c5, -⟩ := two_flank_window p4 r45 A hLe
  rw [hAL] at ht2
  -- the slow runners across the lap
  have lap : ∀ (d : ℝ) (q : ℤ) (x : ℝ), 0 ≤ d → d * τ = q + x →
      (q : ℝ) + 1 / 6 ≤ d * A → d * (τ + (5 / 6 - x3) / v3) ≤ (q : ℝ) + 5 / 6 →
      1 / 6 ≤ circDist (d * t) := by
    intro d q x hd _ hA' hB'
    exact clear_of_lap hd q hA' hB' ht1 ht2
  have c3 : 1 / 6 ≤ circDist ((v3 : ℝ) * t) := by
    refine lap v3 q3 x3 p3.le e3 ?_ ?_
    · rw [hA, mul_sub, e3, mul_div_cancel₀ _ p3.ne']; linarith
    · rw [mul_add, e3, mul_div_cancel₀ _ p3.ne']; linarith
  have c2 : 1 / 6 ≤ circDist ((v2 : ℝ) * t) := by
    refine lap v2 q2 x3 (by linarith) e2 ?_ ?_
    · rw [hA, mul_sub, e2, show (v2 : ℝ) * ((x3 - 1 / 6) / v3) = (x3 - 1 / 6) * (v2 / v3) by ring]
      have : (v2 : ℝ) / v3 ≤ 1 := by rw [div_le_one p3]; linarith
      nlinarith
    · rw [mul_add, e2, show (v2 : ℝ) * ((5 / 6 - x3) / v3) = (5 / 6 - x3) * (v2 / v3) by ring]
      have : (v2 : ℝ) / v3 ≤ 1 := by rw [div_le_one p3]; linarith
      nlinarith
  have c1 : 1 / 6 ≤ circDist ((v1 : ℝ) * t) := by
    refine lap v1 q1 x1 r1.le e1 ?_ ?_
    · rw [hA, mul_sub, e1, show (v1 : ℝ) * ((x3 - 1 / 6) / v3) = (x3 - 1 / 6) * v1 / v3 by ring]
      linarith
    · rw [mul_add, e1, show (v1 : ℝ) * ((5 / 6 - x3) / v3) = (5 / 6 - x3) * v1 / v3 by ring]
      linarith
  have hApos : 0 < A := by
    have : A = ((q3 : ℝ) + 1 / 6) / v3 := by
      rw [hA]; field_simp; linarith
    rw [this]
    have : (0 : ℝ) ≤ q3 := by exact_mod_cast hq3
    positivity
  exact ⟨t, lt_of_lt_of_le hApos ht1, c1, c2, c3, by simpa [one_div] using c4,
    by simpa [one_div] using c5⟩

/-- **Meeting times, in whole numbers.**  With `D = v₃ − v₂ = g·n`, `v₃ = g·c₃`, `v₁ = g·c₁`, the
meeting time `τ = k/D` reads runners 2 and 3 at `(c₃k mod n)/n` and runner 1 at `(c₁k mod n)/n`.
If those readings satisfy BHK's window conditions (in whole numbers), the set is lonely. -/
theorem lonely_of_meeting_nat {v1 v2 v3 v4 v5 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3)
    (h34 : v3 < v4) (h45 : v4 < v5) {g n c3 c1 k : ℕ} (hg : 0 < g) (hn : 0 < n)
    (hD : g * n = v3 - v2) (hc3 : g * c3 = v3) (hc1 : g * c1 = v1)
    (hu1 : n ≤ 6 * ((c3 * k) % n)) (hu2 : 6 * ((c3 * k) % n) ≤ 5 * n)
    (hw1 : (n : ℤ) * v3 + (6 * ((c3 * k) % n : ℕ) - n) * v1 ≤ 6 * ((c1 * k) % n : ℕ) * v3)
    (hw2 : 6 * ((c1 * k) % n : ℕ) * (v3 : ℤ) ≤ 5 * n * v3 - (5 * n - 6 * ((c3 * k) % n : ℕ)) * v1) :
    ∃ t : ℝ, 0 < t ∧ Lonely6 v1 v2 v3 v4 v5 t := by
  have gR : (0 : ℝ) < g := by exact_mod_cast hg
  have nR : (0 : ℝ) < n := by exact_mod_cast hn
  have v3R : (0 : ℝ) < v3 := by exact_mod_cast (show 0 < v3 by omega)
  set U := (c3 * k) % n with hU
  set W := (c1 * k) % n with hW
  set τ : ℝ := (k : ℝ) / (g * n) with hτ
  have hDR : ((g * n : ℕ) : ℝ) = (v3 : ℝ) - v2 := by
    rw [hD, Nat.cast_sub h23.le]
  have e3 : (v3 : ℝ) * τ = (((c3 * k / n : ℕ) : ℤ) : ℝ) + (U : ℝ) / n := by
    have hdm : ((c3 * k : ℕ) : ℝ) = n * ((c3 * k / n : ℕ) : ℝ) + U := by
      exact_mod_cast (Nat.div_add_mod (c3 * k) n).symm
    rw [hτ, ← hc3, Int.cast_natCast]; push_cast at hdm ⊢
    field_simp; linarith
  have e1 : (v1 : ℝ) * τ = (((c1 * k / n : ℕ) : ℤ) : ℝ) + (W : ℝ) / n := by
    have hdm : ((c1 * k : ℕ) : ℝ) = n * ((c1 * k / n : ℕ) : ℝ) + W := by
      exact_mod_cast (Nat.div_add_mod (c1 * k) n).symm
    rw [hτ, ← hc1, Int.cast_natCast]; push_cast at hdm ⊢
    field_simp; linarith
  have e2 : (v2 : ℝ) * τ = ((((c3 * k / n : ℕ) : ℤ) - k : ℤ) : ℝ) + (U : ℝ) / n := by
    have hv2 : (v2 : ℝ) = v3 - g * n := by
      have := hDR; push_cast at this; linarith
    rw [hv2, sub_mul, e3, hτ]
    push_cast
    field_simp
    ring
  have hU1 : (1 : ℝ) / 6 ≤ (U : ℝ) / n := by
    rw [div_le_div_iff₀ (by norm_num) nR]; have : (n : ℝ) ≤ 6 * U := by exact_mod_cast hu1
    linarith
  have hU2 : (U : ℝ) / n ≤ 5 / 6 := by
    rw [div_le_div_iff₀ nR (by norm_num)]; have : 6 * (U : ℝ) ≤ 5 * n := by exact_mod_cast hu2
    linarith
  have hw1R : (n : ℝ) * v3 + (6 * (U : ℝ) - n) * v1 ≤ 6 * (W : ℝ) * v3 := by exact_mod_cast hw1
  have hw2R : 6 * (W : ℝ) * v3 ≤ 5 * n * v3 - (5 * n - 6 * (U : ℝ)) * v1 := by exact_mod_cast hw2
  refine lonely_of_meeting h0 h12 h23 h34 h45 (by positivity) e3 e2 e1 hU1 hU2 ?_ ?_
  · rw [show 1 / 6 + ((U : ℝ) / n - 1 / 6) * v1 / v3 = (n * v3 + (6 * U - n) * v1) / (6 * n * v3) by
      field_simp, div_le_div_iff₀ (by positivity) nR]
    nlinarith
  · rw [show 5 / 6 - (5 / 6 - (U : ℝ) / n) * v1 / v3 = (5 * n * v3 - (5 * n - 6 * U) * v1) / (6 * n * v3) by
      field_simp, div_le_div_iff₀ nR (by positivity)]
    nlinarith

end LRC.OrderSixN
