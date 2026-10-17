import LonelyRunner.LRC.Spec.OrderSevenSplitN
import LonelyRunner.LRC.ConstructionN.Band

/-!
# Order seven: nested band stretches

* `full_stretch_in`: an interval of length `≥ 12/(7u)` contains a full band stretch of speed `u`
  (`[(m + 1/7)/u, (m + 6/7)/u]`, length `5/(7u)`).
* `hit_in`: an interval of length `≥ 2/(7u)` contains an instant at which `u` reads inside `[1/7, 6/7]`.

Chaining them: if each speed is at least `12/5` times the previous, every band stretch of one contains a full band
stretch of the next (the lacunary case of first-stretch localisation).

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.O7Nest

open LRC.MirrorCentre LRC.O7Split

/-- A full band stretch of `u` inside any interval of length `≥ 12/(7u)`. -/
theorem full_stretch_in {u : ℕ} (hu : 0 < u) {a b : ℝ} (hab : 12 / (7 * (u : ℝ)) ≤ b - a) :
    ∃ m : ℤ, a ≤ ((m : ℝ) + 1 / 7) / u ∧ ((m : ℝ) + 6 / 7) / u ≤ b := by
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  refine ⟨⌈(u : ℝ) * a - 1 / 7⌉, ?_, ?_⟩
  · rw [le_div_iff₀ hu']; have := Int.le_ceil ((u : ℝ) * a - 1 / 7); linarith
  · rw [div_le_iff₀ hu']
    have h1 := Int.ceil_lt_add_one ((u : ℝ) * a - 1 / 7)
    have h2 : (12 : ℝ) / 7 ≤ (b - a) * u := by
      have := mul_le_mul_of_nonneg_right hab hu'.le
      rwa [show 12 / (7 * (u : ℝ)) * u = 12 / 7 by field_simp] at this
    nlinarith

/-- Speed `u` is in band on its full stretch `m`. -/
theorem band_on_stretch {u : ℕ} (hu : 0 < u) (m : ℤ) :
    InBandOn {u} (Set.Icc (((m : ℝ) + 1 / 7) / u) (((m : ℝ) + 6 / 7) / u)) :=
  inBand_stretch hu m le_rfl le_rfl

/-- An instant with `u` in band inside any interval of length `≥ 2/(7u)`. -/
theorem hit_in {u : ℕ} (hu : 0 < u) {a b : ℝ} (hab : 2 / (7 * (u : ℝ)) ≤ b - a) :
    ∃ t : ℝ, a ≤ t ∧ t ≤ b ∧ (1 : ℝ) / 7 ≤ circDist ((u : ℝ) * t) := by
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  by_cases hc : (1 : ℝ) / 7 ≤ circDist ((u : ℝ) * a)
  · exact ⟨a, le_rfl, by linarith [show (0 : ℝ) ≤ 2 / (7 * u) by positivity], hc⟩
  · rw [not_le] at hc
    obtain ⟨N, hN⟩ := ConstructionN.circDist_eq_abs_sub_some_int ((u : ℝ) * a)
    rw [hN] at hc
    have hlo : (N : ℝ) - 1 / 7 < u * a := by have := neg_abs_le ((u : ℝ) * a - N); linarith
    have hhi : (u : ℝ) * a < N + 1 / 7 := by have := le_abs_self ((u : ℝ) * a - N); linarith
    refine ⟨((N : ℝ) + 1 / 7) / u, ?_, ?_, ?_⟩
    · rw [le_div_iff₀ hu']; linarith
    · rw [div_le_iff₀ hu']
      have h2 : (2 : ℝ) / 7 ≤ (b - a) * u := by
        have := mul_le_mul_of_nonneg_right hab hu'.le
        rwa [show 2 / (7 * (u : ℝ)) * u = 2 / 7 by field_simp] at this
      nlinarith
    · rw [show (u : ℝ) * (((N : ℝ) + 1 / 7) / u) = (N : ℝ) + 1 / 7 by field_simp]
      exact circDist_ge_of_window (m := N) le_rfl (by linarith) (by norm_num)

/-- One nesting step: a full stretch of `u` (`m`) contains a full stretch of `u'` when `5 u' ≥ 12 u`. -/
theorem nest_step {u u' : ℕ} (hu : 0 < u) (hu' : 0 < u') (h : 12 * u ≤ 5 * u') (m : ℤ) :
    ∃ m' : ℤ, ((m : ℝ) + 1 / 7) / u ≤ ((m' : ℝ) + 1 / 7) / u' ∧ ((m' : ℝ) + 6 / 7) / u' ≤ ((m : ℝ) + 6 / 7) / u := by
  apply full_stretch_in hu'
  have hur : (0 : ℝ) < u := by exact_mod_cast hu
  have hur' : (0 : ℝ) < u' := by exact_mod_cast hu'
  have hh : (12 : ℝ) * u ≤ 5 * u' := by exact_mod_cast h
  rw [show ((m : ℝ) + 6 / 7) / u - ((m : ℝ) + 1 / 7) / u = 5 / (7 * u) by field_simp; ring,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **Lacunary first-stretch localisation.**  `0 < v1 < … < v6` with `5 v_{k+1} ≥ 12 v_k` for `k = 1..4`: some instant in
the first band stretch of `v1` has all six in band. -/
theorem lonely7_lacunary {v1 v2 v3 v4 v5 v6 : ℕ} (h0 : 0 < v1) (h12 : 12 * v1 ≤ 5 * v2) (h23 : 12 * v2 ≤ 5 * v3)
    (h34 : 12 * v3 ≤ 5 * v4) (h45 : 12 * v4 ≤ 5 * v5) (h56 : v5 < v6) :
    ∃ t : ℝ, 1 / (7 * (v1 : ℝ)) ≤ t ∧ t ≤ 6 / (7 * (v1 : ℝ)) ∧
      ∀ d ∈ ({v1, v2, v3, v4, v5, v6} : Finset ℕ), (1 : ℝ) / 7 ≤ circDist ((d : ℝ) * t) := by
  have p2 : 0 < v2 := by omega
  have p3 : 0 < v3 := by omega
  have p4 : 0 < v4 := by omega
  have p5 : 0 < v5 := by omega
  have p6 : 0 < v6 := by omega
  obtain ⟨m2, a2, b2⟩ := nest_step h0 p2 h12 0
  obtain ⟨m3, a3, b3⟩ := nest_step p2 p3 h23 m2
  obtain ⟨m4, a4, b4⟩ := nest_step p3 p4 h34 m3
  obtain ⟨m5, a5, b5⟩ := nest_step p4 p5 h45 m4
  have hr5 : (0 : ℝ) < v5 := by exact_mod_cast p5
  have hr6 : (0 : ℝ) < v6 := by exact_mod_cast p6
  have hlen : 2 / (7 * (v6 : ℝ)) ≤ ((m5 : ℝ) + 6 / 7) / v5 - ((m5 : ℝ) + 1 / 7) / v5 := by
    have h56r : (v5 : ℝ) < v6 := by exact_mod_cast h56
    rw [show ((m5 : ℝ) + 6 / 7) / v5 - ((m5 : ℝ) + 1 / 7) / v5 = 5 / (7 * v5) by field_simp; ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  obtain ⟨t, ht1, ht2, h6⟩ := hit_in p6 hlen
  have c0 : (0 : ℝ) = ((0 : ℤ) : ℝ) := by norm_num
  have in1 := band_on_stretch h0 0
  have in2 := band_on_stretch p2 m2
  have in3 := band_on_stretch p3 m3
  have in4 := band_on_stretch p4 m4
  have in5 := band_on_stretch p5 m5
  push_cast at a2 b2 in1
  refine ⟨t, ?_, ?_, ?_⟩
  · have := le_trans a2 (le_trans a3 (le_trans a4 (le_trans a5 ht1)))
    rw [show (1 : ℝ) / (7 * v1) = (0 + 1 / 7) / v1 by ring]; exact this
  · have := le_trans ht2 (le_trans b5 (le_trans b4 (le_trans b3 b2)))
    rw [show (6 : ℝ) / (7 * v1) = (0 + 6 / 7) / v1 by ring]; exact this
  · intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have t5 : t ∈ Set.Icc (((m5 : ℝ) + 1 / 7) / v5) (((m5 : ℝ) + 6 / 7) / v5) := ⟨ht1, ht2⟩
    have t4 : t ∈ Set.Icc (((m4 : ℝ) + 1 / 7) / v4) (((m4 : ℝ) + 6 / 7) / v4) :=
      ⟨le_trans a5 ht1, le_trans ht2 b5⟩
    have t3 : t ∈ Set.Icc (((m3 : ℝ) + 1 / 7) / v3) (((m3 : ℝ) + 6 / 7) / v3) :=
      ⟨le_trans a4 t4.1, le_trans t4.2 b4⟩
    have t2 : t ∈ Set.Icc (((m2 : ℝ) + 1 / 7) / v2) (((m2 : ℝ) + 6 / 7) / v2) :=
      ⟨le_trans a3 t3.1, le_trans t3.2 b3⟩
    have t1 : t ∈ Set.Icc ((0 + 1 / 7) / (v1 : ℝ)) ((0 + 6 / 7) / v1) := ⟨le_trans a2 t2.1, le_trans t2.2 b2⟩
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    · exact in1 t t1 d (Finset.mem_singleton_self _)
    · exact in2 t t2 d (Finset.mem_singleton_self _)
    · exact in3 t t3 d (Finset.mem_singleton_self _)
    · exact in4 t t4 d (Finset.mem_singleton_self _)
    · exact in5 t t5 d (Finset.mem_singleton_self _)
    · exact h6

end LRC.O7Nest
