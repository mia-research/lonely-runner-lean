import LonelyRunner.LRC.Spec.MirrorCentreN

/-!
# Loneliness in log-time: scale invariance made exact

2026-09-25.  Write `x = log t` for the time and `log d` for a disparity.  A disparity `d` is clear
at `t` exactly when `d·t` lies in a band `[M + 1/n, M + 1 − 1/n]`, `M` a whole number; taking logs,
exactly when `log t + log d` lies in the fixed set

    G n  =  ⋃_{M ≥ 0} [ log (M + 1/n) , log (M + 1 − 1/n) ].

So a subject is lonely **iff some translate of its configuration `{log d}` lies inside `G n`**
(`lonely_iff_translate_mem`).  The speeds enter only through the configuration, and scaling every
speed by `λ` translates the configuration by `log λ`: scale invariance is translation invariance, and
there is no lattice and no divisibility in the statement.  The first tooth
`[log (1/n), log (1 − 1/n)]` has length exactly `log (n − 1)`, which is R1's `n − 1`.

Real disparities, every order `n ≥ 2`.  Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.LogTime

open LRC.MirrorCentre

/-- **The clear set in log-time**: the union of the teeth `[log (M + 1/n), log (M + 1 − 1/n)]`. -/
def G (n : ℕ) : Set ℝ :=
  {y | ∃ M : ℕ, Real.log ((M : ℝ) + (n : ℝ)⁻¹) ≤ y ∧ y ≤ Real.log ((M : ℝ) + 1 - (n : ℝ)⁻¹)}

/-- A positive reading is clear exactly when it lies in some band `[M + a, M + 1 − a]`, `M ≥ 0`. -/
theorem clear_iff_band {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    a ≤ circDist x ↔ ∃ M : ℕ, (M : ℝ) + a ≤ x ∧ x ≤ (M : ℝ) + 1 - a := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := fract_bounds_of_circDist h
    have hfl : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx.le
    refine ⟨⌊x⌋.toNat, ?_, ?_⟩
    · have : ((⌊x⌋.toNat : ℕ) : ℝ) = (⌊x⌋ : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hfl
      rw [this]; have := Int.floor_add_fract x; linarith
    · have : ((⌊x⌋.toNat : ℕ) : ℝ) = (⌊x⌋ : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hfl
      rw [this]; have := Int.floor_add_fract x; linarith
  · rintro ⟨M, h1, h2⟩
    exact circDist_ge_of_window (m := (M : ℤ)) (by exact_mod_cast h1) (by exact_mod_cast h2) ha

/-- **One runner in log-time.**  For `d, t > 0`, `d` is clear at `t` iff `log t + log d ∈ G n`. -/
theorem clear_iff_mem_G {n : ℕ} (hn : 2 ≤ n) {d t : ℝ} (hd : 0 < d) (ht : 0 < t) :
    (n : ℝ)⁻¹ ≤ circDist (d * t) ↔ Real.log t + Real.log d ∈ G n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
  have hahalf : (n : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hn'
  have hdt : 0 < d * t := mul_pos hd ht
  have hlog : Real.log t + Real.log d = Real.log (d * t) := by
    rw [Real.log_mul hd.ne' ht.ne', add_comm]
  rw [clear_iff_band hdt ha, hlog]
  constructor
  · rintro ⟨M, h1, h2⟩
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    exact ⟨M, Real.log_le_log (by positivity) h1, Real.log_le_log hdt h2⟩
  · rintro ⟨M, h1, h2⟩
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have hlo : 0 < (M : ℝ) + (n : ℝ)⁻¹ := by positivity
    have hhi : 0 < (M : ℝ) + 1 - (n : ℝ)⁻¹ := by linarith
    exact ⟨M, (Real.log_le_log_iff hlo hdt).mp h1, (Real.log_le_log_iff hdt hhi).mp h2⟩

/-- **Loneliness is a translate of the configuration fitting inside `G n`.**  For a finite set of
positive disparities, the subject is lonely at some positive time iff some `x` puts every
`x + log d` in `G n`. -/
theorem lonely_iff_translate_mem {n : ℕ} (hn : 2 ≤ n) {S : Finset ℝ} (hpos : ∀ d ∈ S, 0 < d) :
    (∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (n : ℝ)⁻¹ ≤ circDist (d * t)) ↔
      ∃ x : ℝ, ∀ d ∈ S, x + Real.log d ∈ G n := by
  constructor
  · rintro ⟨t, ht, hl⟩
    exact ⟨Real.log t, fun d hd => (clear_iff_mem_G hn (hpos d hd) ht).mp (hl d hd)⟩
  · rintro ⟨x, hx⟩
    refine ⟨Real.exp x, Real.exp_pos x, fun d hd => ?_⟩
    rw [clear_iff_mem_G hn (hpos d hd) (Real.exp_pos x), Real.log_exp]
    exact hx d hd

/-- **Scale invariance is translation.**  Scaling every disparity by `λ > 0` moves the configuration
by `log λ` and leaves loneliness unchanged. -/
theorem translate_scale {n : ℕ} {S : Finset ℝ} (hpos : ∀ d ∈ S, 0 < d) {lam x : ℝ} (hlam : 0 < lam)
    (h : ∀ d ∈ S, x + Real.log d ∈ G n) :
    ∀ d ∈ S, (x - Real.log lam) + Real.log (lam * d) ∈ G n := by
  intro d hd
  rw [Real.log_mul hlam.ne' (hpos d hd).ne']
  have e : x - Real.log lam + (Real.log lam + Real.log d) = x + Real.log d := by ring
  rw [e]; exact h d hd

end LRC.LogTime
