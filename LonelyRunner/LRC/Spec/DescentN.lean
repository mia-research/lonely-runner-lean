import LonelyRunner.LRC.Spec.SelfSimilarN
import LonelyRunner.LRC.ConstructionN.Band
import LonelyRunner.LRC.ConstructionN.LemmaPass

/-!
# The self-similar end of the trichotomy, discharged by descent

2026-09-24.  Write `M` for the number of disparities divisible by `n` and `c` for their number.
`flankWorks_of_multiples` reduces the case `M = c − 1` to a sub-problem that it takes as a
hypothesis, and the lone non-multiple flank does fail (for example `{1, 4, 8}` at `n = 4`).
This file discharges the case without choosing a flank.

**The descent** (`lonely_descent_iff`).  Let `n ≥ 3`, `n ∤ e`, and let every other disparity be
`n·m` for `m ∈ M`.  Then the set `{e} ∪ n·M` is lonely at threshold `1/n` exactly when `M` is
lonely at the **same** threshold `1/n`.  This is the same obligation with one disparity fewer,
not a lower-order conjecture.

* (⇒) At a lonely `t`, the instant `τ = n·t` clears every `m`.
* (⇐) At an instant `τ` clearing `M`, try `t = (τ + k)/n` for whole `k`.  Each multiple reads
  `m·(τ + k)`, unchanged mod 1.  The reading of `e` moves by `e·k/n`, and three consecutive
  shifts cannot all fall in the open arc of width `2/n` around the integers, because `n ∤ e`
  and `n ≥ 3` (`exists_clear_shift`).  A pigeonhole used as a tool; nothing is covered.

**All multiples** (`lonely_scale_iff`).  When every disparity is `n·m`, dividing by `n` changes
nothing.

So a counterexample with fewest disparities, and then smallest ones, has `1 ≤ M ≤ c − 2`.
Theorem 9 (`Flanks.lonely_iff_exists_flank`) turns each lonely instant here into a certificate.

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option linter.style.longLine false

namespace LRC.Descent

open ConstructionN

/-- Two points each within `1/n` of an integer are within `2/n` of each other, scaled by `n`. -/
theorem scaled_sub_lt_two {n : ℝ} (hn : 0 < n) {a b : ℝ} (ha : |a| < n⁻¹) (hb : |b| < n⁻¹) :
    |n * (a - b)| < 2 := by
  rw [abs_mul, abs_of_pos hn]
  have hab : |a - b| ≤ |a| + |b| := abs_sub a b
  have hinv : n * n⁻¹ = 1 := mul_inv_cancel₀ hn.ne'
  nlinarith [abs_nonneg (a - b)]

/-- **Three consecutive shifts by a non-multiple of `1/n`: one is clear.**  With `n ≥ 3` and
`n ∤ r`, one of `x`, `x + r/n`, `x + 2r/n` is at distance at least `1/n` from the integers. -/
theorem exists_clear_shift {n : ℕ} (hn : 3 ≤ n) (x : ℝ) {r : ℤ} (hr : ¬ (n : ℤ) ∣ r) :
    ∃ k : ℕ, k ≤ 2 ∧ (n : ℝ)⁻¹ ≤ circDist (x + (r : ℝ) * (k : ℝ) / n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn3 : (3 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  by_contra hcon
  push Not at hcon
  have c0 : circDist x < (n : ℝ)⁻¹ := by simpa using hcon 0 (by norm_num)
  have c1 : circDist (x + (r : ℝ) / n) < (n : ℝ)⁻¹ := by simpa using hcon 1 (by norm_num)
  have c2 : circDist (x + 2 * (r : ℝ) / n) < (n : ℝ)⁻¹ := by
    have h := hcon 2 (by norm_num)
    have heq : x + (r : ℝ) * ((2 : ℕ) : ℝ) / n = x + 2 * (r : ℝ) / n := by push_cast; ring
    rwa [heq] at h
  obtain ⟨K0, hK0⟩ := circDist_eq_abs_sub_some_int x
  obtain ⟨K1, hK1⟩ := circDist_eq_abs_sub_some_int (x + (r : ℝ) / n)
  obtain ⟨K2, hK2⟩ := circDist_eq_abs_sub_some_int (x + 2 * (r : ℝ) / n)
  rw [hK0] at c0
  rw [hK1] at c1
  rw [hK2] at c2
  -- the three integer steps
  set s : ℤ := r - n * (K1 - K0) with hs
  set s' : ℤ := r - n * (K2 - K1) with hs'
  have hnn : (n : ℝ) ≠ 0 := hnpos.ne'
  have es : (s : ℝ) = n * ((x + (r : ℝ) / n - K1) - (x - K0)) := by
    rw [hs]; push_cast; field_simp; ring
  have es' : (s' : ℝ) = n * ((x + 2 * (r : ℝ) / n - K2) - (x + (r : ℝ) / n - K1)) := by
    rw [hs']; push_cast; field_simp; ring
  have ess : ((s + s' : ℤ) : ℝ) = n * ((x + 2 * (r : ℝ) / n - K2) - (x - K0)) := by
    rw [hs, hs']; push_cast; field_simp; ring
  have bs : |(s : ℝ)| < 2 := by rw [es]; exact scaled_sub_lt_two hnpos c1 c0
  have bs' : |(s' : ℝ)| < 2 := by rw [es']; exact scaled_sub_lt_two hnpos c2 c1
  have bss : |((s + s' : ℤ) : ℝ)| < 2 := by rw [ess]; exact scaled_sub_lt_two hnpos c2 c0
  have is : |s| < 2 := by exact_mod_cast bs
  have is' : |s'| < 2 := by exact_mod_cast bs'
  have iss : |s + s'| < 2 := by exact_mod_cast bss
  rw [abs_lt] at is is' iss
  -- neither step is zero, since `n ∤ r`
  have hs0 : s ≠ 0 := by
    intro h; apply hr; exact ⟨K1 - K0, by rw [hs] at h; linarith⟩
  have hs'0 : s' ≠ 0 := by
    intro h; apply hr; exact ⟨K2 - K1, by rw [hs'] at h; linarith⟩
  -- so the steps are `±1` with opposite signs, and `n` divides their difference `±2`
  have hdiff : n * ((K2 - K1) - (K1 - K0)) = s - s' := by rw [hs, hs']; ring
  have hss : s - s' = 2 ∨ s - s' = -2 := by omega
  set D : ℤ := (K2 - K1) - (K1 - K0) with hD
  rcases lt_trichotomy D 0 with h | h | h
  · have : (n : ℤ) * D ≤ -3 := by nlinarith
    omega
  · rw [h, mul_zero] at hdiff; omega
  · have : 3 ≤ (n : ℤ) * D := by nlinarith
    omega

variable {n : ℕ}

/-- **The descent.**  With `n ≥ 3` and `n ∤ e`, the set `{e} ∪ n·M` is lonely at threshold `1/n`
exactly when `M` is lonely at the same threshold. -/
theorem lonely_descent_iff (hn : 3 ≤ n) (M : List ℕ) (e : ℕ) (he : ¬ n ∣ e) :
    (∃ t : ℝ, 0 < t ∧ (n : ℝ)⁻¹ ≤ circDist ((e : ℝ) * t) ∧
        ∀ m ∈ M, (n : ℝ)⁻¹ ≤ circDist (((n * m : ℕ) : ℝ) * t)) ↔
      (∃ τ : ℝ, 0 < τ ∧ ∀ m ∈ M, (n : ℝ)⁻¹ ≤ circDist ((m : ℝ) * τ)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnn : (n : ℝ) ≠ 0 := hnpos.ne'
  constructor
  · rintro ⟨t, ht, -, hM⟩
    refine ⟨n * t, mul_pos hnpos ht, fun m hm => ?_⟩
    have h := hM m hm
    have heq : ((n * m : ℕ) : ℝ) * t = (m : ℝ) * (n * t) := by push_cast; ring
    rwa [heq] at h
  · rintro ⟨τ, hτ, hM⟩
    have hr : ¬ (n : ℤ) ∣ (e : ℤ) := by exact_mod_cast he
    obtain ⟨k, -, hk⟩ := exists_clear_shift hn ((e : ℝ) * τ / n) hr
    refine ⟨(τ + k) / n, by positivity, ?_, fun m hm => ?_⟩
    · have heq : (e : ℝ) * ((τ + k) / n) = (e : ℝ) * τ / n + ((e : ℤ) : ℝ) * (k : ℝ) / n := by
        push_cast; ring
      rwa [heq]
    · have heq : ((n * m : ℕ) : ℝ) * ((τ + k) / n) = (m : ℝ) * τ + (((m * k : ℕ) : ℤ) : ℝ) := by
        push_cast; field_simp
      rw [heq, circDist_add_int]
      exact hM m hm

/-- **All multiples.**  Dividing every disparity by `n` changes nothing. -/
theorem lonely_scale_iff (hn : 0 < n) (θ : ℝ) (M : List ℕ) :
    (∃ t : ℝ, 0 < t ∧ ∀ m ∈ M, θ ≤ circDist (((n * m : ℕ) : ℝ) * t)) ↔
      (∃ τ : ℝ, 0 < τ ∧ ∀ m ∈ M, θ ≤ circDist ((m : ℝ) * τ)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · rintro ⟨t, ht, hM⟩
    refine ⟨n * t, mul_pos hnpos ht, fun m hm => ?_⟩
    have h := hM m hm
    have heq : ((n * m : ℕ) : ℝ) * t = (m : ℝ) * (n * t) := by push_cast; ring
    rwa [heq] at h
  · rintro ⟨τ, hτ, hM⟩
    refine ⟨τ / n, by positivity, fun m hm => ?_⟩
    have heq : ((n * m : ℕ) : ℝ) * (τ / n) = (m : ℝ) * τ := by
      push_cast; field_simp
    rw [heq]
    exact hM m hm

end LRC.Descent
