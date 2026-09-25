import LonelyRunner.LRC.Spec.OrderSixEightN
import LonelyRunner.LRC.Spec.GlobalIsolationTwoN

/-!
# Order six, BHK §6 (`v₃ − v₂ ∣ v₃`, `v₃ − v₂ ∤ v₁`, `3v₁ < v₃`) inside the framework

2026-09-24.  Write `D = v₃ − v₂`.  When `D ∣ v₃`, runners 2 and 3 meet **at the origin**: at every
meeting time `k/D` both read whole numbers (`v₂ = K·D`, `v₃ = (K + 1)·D`).  BHK §6 argues by
contradiction from these meeting times.  In the framework each step names its instant.

* **Readings on the orbit.**  With `g = gcd(D, v₁, v₄)`, `D = g·n`, `v₁ = g·c₁`, `v₄ = g·c₄`, at the
  meeting time `k/D` runners 1 and 4 read `(c₁k mod n)/n` and `(c₄k mod n)/n` past a whole number
  (`meeting_of_orbit`): the orbit `k ↦ ((c₁k) % n, (c₄k) % n)` of `GlobalIsolationTwoN`, with
  `gcd(n, c₁, c₄) = 1` by construction (no primitivity of the five speeds is needed).
* **One-dimensional global isolation** (`orbit_window_one`): as `n ∤ c₁`, the orbit of runner 1 is a
  grid of spacing `gcd(c₁, n)/n ≤ 1/2` and meets BHK's window (59), at a named multiple of a named
  unit step.  After that meeting time, runners 1–3 are clear across `[τ + 1/(3v₃), τ + 5/(6v₃)]`
  (`clear123_after`); if `4v₃ ≤ 3v₄` the two-flank window rule (BHK Lemma 4) names a lonely
  instant in it (`lonely_at_meeting_wide`).  This is BHK's reduction to `3v₄ < 4v₃`.
* **R6 at `q = 2`** (`half_lap_window`, BHK Lemma 22): a runner at its half lap is clear for
  `1/(3e)` on either side, so a 123-window through that instant, longer than one blocked zone of
  `v₅`, holds a named instant where `v₄` and `v₅` are clear too (`lonely_at_meeting`, BHK (59) and
  (60)).
* **Two-dimensional global isolation** (`orbit_isolation_two`, BHK Corollary 6): the orbit meets
  BHK's box `R` (then `lonely_at_orbit`), or it has a short step `(1, e)` with `|e| ≤ 3`
  (`lonely_6_narrow`).  Each step is a named case:
  - `e = 0`, Case 6.1 (`case_6_1`); `e = −1`, 6.3; `e = 2`, 6.4; `e = −2`, 6.5 (`n = 5`: 6.5.1,
    `n = 7`: 6.5.2); `e = ±3` (`case_6_6a`, `case_6_6b`, reachable, and omitted from BHK's list):
    a named multiple of the step lands in BHK (61) (`lonely_of_step`);
  - `e = 1`, Case 6.2 (`case_6_2`): at the meeting times with runners 1 and 4 reading alike,
    windows with a flank clear at a named instant, or sitting in one blocked zone
    (`flank_after`, `flank_at`): §6.2.1 (`s621_x1`, `s621_x5`, `s621_kernel`) and §6.2.2
    (`s622_flank`, `s622_final`, `s622_final_half`);
  - Case 6.5.1's chain (62)–(64) is four whole-number windows from the start (`s651_kernel`,
    `step4` of §8), the last one `v₅`'s opening `13/(6v₅)`, where every runner is clear.

The only arguments by contradiction left are the whole-number kernels saying that a window
cannot sit inside one blocked zone.  `lonely_6` assembles the section.

Everything here is proved; no `sorry`, no `native_decide`, no measure theory.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.OrderSixN

open MomentIterationN LRC.SpecN ConstructionN

/-! ## 0. tools: the mirror, readings after a meeting instant, the half lap -/

/-- **The mirror instant.**  Lonely at `t` is lonely at `−t`. -/
theorem lonely6_neg {v1 v2 v3 v4 v5 : ℕ} {t : ℝ} (h : Lonely6 v1 v2 v3 v4 v5 t) :
    Lonely6 v1 v2 v3 v4 v5 (-t) := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [mul_neg, circDist.symm_neg] <;> assumption

/-- A lonely instant is never `0`, so its mirror or itself is positive. -/
theorem lonely6_pos {v1 v2 v3 v4 v5 : ℕ} {t : ℝ} (h : Lonely6 v1 v2 v3 v4 v5 t) :
    ∃ t : ℝ, 0 < t ∧ Lonely6 v1 v2 v3 v4 v5 t := by
  have ht : t ≠ 0 := by
    rintro rfl
    have := h.1
    rw [mul_zero] at this
    have h0 : circDist 0 = 0 := by simp [circDist]
    linarith
  rcases lt_or_gt_of_ne ht with h' | h'
  · exact ⟨-t, by linarith, lonely6_neg h⟩
  · exact ⟨t, h', h⟩

/-- **A runner read after a meeting instant.**  If at the instant `τ` the runner `d` reads
`q + ρ`, and on `[τ + x₁/w, τ + x₂/w]` its reading `ρ + (d/w)·x` stays in `[m + 1/6, m + 5/6]`, it is
clear there (lap `q + m`).  Here `w` is the time unit, `x` counts laps of the runner `w`. -/
theorem clear_after {d w τ ρ x1 x2 t : ℝ} (hd : 0 ≤ d) (q m : ℤ)
    (hτ : d * τ = q + ρ) (h1 : (m : ℝ) + 1 / 6 ≤ ρ + d / w * x1)
    (h2 : ρ + d / w * x2 ≤ (m : ℝ) + 5 / 6) (ht1 : τ + x1 / w ≤ t) (ht2 : t ≤ τ + x2 / w) :
    1 / 6 ≤ circDist (d * t) := by
  have e1 : d * (τ + x1 / w) = d * τ + d / w * x1 := by ring
  have e2 : d * (τ + x2 / w) = d * τ + d / w * x2 := by ring
  refine clear_of_lap hd (q + m) ?_ ?_ ht1 ht2
  · rw [e1, hτ]; push_cast; linarith
  · rw [e2, hτ]; push_cast; linarith

/-- **The window of a flank, in units of `w`.**  On `[τ + x₁/w, τ + x₂/w]` where `P` holds, the flank
`f` is clear at a named instant with `P`, or the window sits in one blocked zone of `f`, so that
`(f/w)·(x₂ − x₁) < 1/3`. -/
theorem flank_after {f w τ x1 x2 : ℝ} (hf : 0 < f) (hw : 0 < w) (hx : x1 ≤ x2) (P : ℝ → Prop)
    (hP : ∀ t, τ + x1 / w ≤ t → t ≤ τ + x2 / w → P t) :
    (∃ t, P t ∧ 1 / 6 ≤ circDist (f * t)) ∨ f / w * (x2 - x1) < 1 / 3 := by
  have hAB : τ + x1 / w ≤ τ + x2 / w := by
    have := div_le_div_of_nonneg_right hx hw.le
    linarith
  rcases window_or_inside hf hAB P hP with ⟨t, -, -, hPt, hft⟩ | ⟨k, hk1, hk2⟩
  · exact Or.inl ⟨t, hPt, hft⟩
  · right
    have e : f / w * (x2 - x1) = f * (τ + x2 / w) - f * (τ + x1 / w) := by ring
    rw [e]; linarith

/-- **The flank at one instant.**  At `τ + x/w` the flank `f` is clear, or it sits in the blocked
zone `K`: `K − 1/6 < f·τ + (f/w)·x < K + 1/6`. -/
theorem flank_at (f w τ x : ℝ) :
    1 / 6 ≤ circDist (f * (τ + x / w)) ∨
      ∃ K : ℤ, (K : ℝ) - 1 / 6 < f * τ + f / w * x ∧ f * τ + f / w * x < (K : ℝ) + 1 / 6 := by
  by_cases h : 1 / 6 ≤ circDist (f * (τ + x / w))
  · exact Or.inl h
  · right
    push Not at h
    obtain ⟨K, hK⟩ := circDist_eq_abs_sub_some_int (f * (τ + x / w))
    rw [hK] at h
    have e : f * (τ + x / w) = f * τ + f / w * x := by ring
    rw [e] at h
    obtain ⟨h1, h2⟩ := abs_lt.mp h
    exact ⟨K, by linarith, by linarith⟩

/-- **R6 at `q = 2`: a runner at its half lap.**  If `e·t₀ = m + 1/2`, the runner `e` is clear for
`1/(3e)` on either side of `t₀`.  In a window `[A, B] ∋ t₀` longer than one blocked zone `1/(3f)`
of a faster flank `f`, some stretch clear for `e` is also longer than `1/(3f)`, so `f` is clear at a
named instant of it (its start or `f`'s opening) where `e` is clear too. -/
theorem half_lap_window {e f A B t0 : ℝ} (he : 0 < e) (hef : e < f) (hA : A ≤ t0) (hB : t0 ≤ B)
    (hlen : 1 / (3 * f) < B - A) (m : ℤ) (h0 : e * t0 = m + 1 / 2) :
    ∃ t, A ≤ t ∧ t ≤ B ∧ 1 / 6 ≤ circDist (e * t) ∧ 1 / 6 ≤ circDist (f * t) := by
  have hf : 0 < f := he.trans hef
  have hfe : 1 / (3 * f) < 1 / (3 * e) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]; linarith
  have hep : 0 < 1 / (3 * e) := by positivity
  have hee : e * (1 / (3 * e)) = 1 / 3 := by field_simp
  have hff : f * (1 / (3 * f)) = 1 / 3 := by field_simp
  -- a stretch `[c, d]` inside `[A, B]` and inside `e`'s clear stretch around `t₀`
  obtain ⟨c, d, hAc, hdB, hc, hd, hcd⟩ : ∃ c d : ℝ, A ≤ c ∧ d ≤ B ∧ t0 - 1 / (3 * e) ≤ c ∧
      d ≤ t0 + 1 / (3 * e) ∧ 1 / (3 * f) < d - c := by
    by_cases h1 : t0 + 1 / (3 * e) ≤ B
    · exact ⟨t0, t0 + 1 / (3 * e), hA, h1, by linarith [hfe], le_rfl, by linarith⟩
    by_cases h2 : A ≤ t0 - 1 / (3 * e)
    · exact ⟨t0 - 1 / (3 * e), t0, h2, hB, le_rfl, by linarith [hfe], by linarith⟩
    push Not at h1 h2
    exact ⟨A, B, le_rfl, le_rfl, by linarith, by linarith, hlen⟩
  have hce : ∀ t, c ≤ t → t ≤ d → 1 / 6 ≤ circDist (e * t) := by
    intro t h1 h2
    refine clear_of_lap he.le m ?_ ?_ h1 h2
    · have := mul_le_mul_of_nonneg_left hc he.le
      rw [mul_sub, hee, h0] at this; linarith
    · have := mul_le_mul_of_nonneg_left hd he.le
      rw [mul_add, hee, h0] at this; linarith
  have hcd' : c ≤ d := by
    have : 0 < 1 / (3 * f) := by positivity
    linarith
  rcases window_or_inside hf hcd' (fun t => 1 / 6 ≤ circDist (e * t)) hce with
    ⟨t, h1, h2, hPt, hft⟩ | ⟨k, hk1, hk2⟩
  · exact ⟨t, by linarith, by linarith, hPt, hft⟩
  · exfalso
    have := mul_lt_mul_of_pos_left hcd hf
    rw [mul_sub] at this
    linarith

/-! ## 1. the 123-window after a meeting of runners 2 and 3 -/

section Meeting

variable {v1 v2 v3 v4 v5 : ℕ}

/-- **The 123-window.**  At a meeting instant `τ` of runners 2 and 3 (both read whole numbers), with
runner 1 reading `q₁ + ρ₁` inside BHK's window (59), `1/6 − v₁/(3v₃) ≤ ρ₁ ≤ 5/6 − 5v₁/(6v₃)`,
runners 1–3 are clear across `[τ + 1/(3v₃), τ + 5/(6v₃)]` (`v₃ ≤ 2 v₂`). -/
theorem clear123_after (h0 : 0 < v1) (h23 : v2 < v3) (hsmall : 3 * v1 < v3)
    (h2v2 : v3 ≤ 2 * v2) {τ ρ1 : ℝ} (q1 q2 q3 : ℤ) (e1 : (v1 : ℝ) * τ = q1 + ρ1)
    (e2 : (v2 : ℝ) * τ = q2) (e3 : (v3 : ℝ) * τ = q3)
    (h59a : 1 / 6 - (v1 : ℝ) / (3 * v3) ≤ ρ1) (h59b : ρ1 ≤ 5 / 6 - 5 * (v1 : ℝ) / (6 * v3))
    {t : ℝ} (ht1 : τ + (1 / 3) / (v3 : ℝ) ≤ t) (ht2 : t ≤ τ + (5 / 6) / (v3 : ℝ)) :
    1 / 6 ≤ circDist ((v1 : ℝ) * t) ∧ 1 / 6 ≤ circDist ((v2 : ℝ) * t) ∧
      1 / 6 ≤ circDist ((v3 : ℝ) * t) := by
  have p3 : (0 : ℝ) < v3 := by exact_mod_cast (show 0 < v3 by omega)
  have l1 : (v1 : ℝ) / v3 < 1 / 3 := by
    rw [div_lt_iff₀ p3]; have : 3 * (v1 : ℝ) < v3 := by exact_mod_cast hsmall
    linarith
  have l1' : 0 ≤ (v1 : ℝ) / v3 := by positivity
  have l2 : 1 / 2 ≤ (v2 : ℝ) / v3 := by
    rw [le_div_iff₀ p3]; have : (v3 : ℝ) ≤ 2 * v2 := by exact_mod_cast h2v2
    linarith
  have l2' : (v2 : ℝ) / v3 < 1 := by
    rw [div_lt_one p3]; exact_mod_cast h23
  have l3 : (v3 : ℝ) / v3 = 1 := div_self p3.ne'
  have f1 : (v1 : ℝ) / (3 * v3) = (v1 : ℝ) / v3 / 3 := by ring
  have f2 : 5 * (v1 : ℝ) / (6 * v3) = 5 / 6 * ((v1 : ℝ) / v3) := by ring
  rw [f1] at h59a
  rw [f2] at h59b
  refine ⟨?_, ?_, ?_⟩
  · refine clear_after (by positivity) q1 0 e1 ?_ ?_ ht1 ht2 <;> push_cast <;> nlinarith
  · refine clear_after (ρ := 0) (by positivity) q2 0 (by rw [e2, add_zero]) ?_ ?_ ht1 ht2 <;>
      push_cast <;> nlinarith
  · refine clear_after (ρ := 0) (by positivity) q3 0 (by rw [e3, add_zero]) ?_ ?_ ht1 ht2 <;>
      rw [l3] <;> norm_num

/-- **BHK's reduction `3 v₄ < 4 v₃`, by the two-flank window.**  If `4 v₃ ≤ 3 v₄`, the 123-window
`[τ + 1/(3v₃), τ + 5/(6v₃)]` has length `1/(2v₃) ≥ 2/(3v₄)`, so the two-flank window rule
(`two_flank_window`, BHK Lemma 4) names an instant in it where runners 4 and 5 are clear too. -/
theorem lonely_at_meeting_wide (h0 : 0 < v1) (h23 : v2 < v3) (h34 : v3 < v4)
    (h45 : v4 < v5) (hsmall : 3 * v1 < v3) (h2v2 : v3 ≤ 2 * v2) (hwide : 4 * v3 ≤ 3 * v4)
    {τ ρ1 : ℝ} (q1 q2 q3 : ℤ) (e1 : (v1 : ℝ) * τ = q1 + ρ1)
    (e2 : (v2 : ℝ) * τ = q2) (e3 : (v3 : ℝ) * τ = q3)
    (h59a : 1 / 6 - (v1 : ℝ) / (3 * v3) ≤ ρ1) (h59b : ρ1 ≤ 5 / 6 - 5 * (v1 : ℝ) / (6 * v3)) :
    ∃ t : ℝ, Lonely6 v1 v2 v3 v4 v5 t := by
  have p3 : (0 : ℝ) < v3 := by exact_mod_cast (show 0 < v3 by omega)
  have p4 : (0 : ℝ) < v4 := by exact_mod_cast (show 0 < v4 by omega)
  have r45 : (v4 : ℝ) < v5 := by exact_mod_cast h45
  have hL : 2 / (3 * (v4 : ℝ)) ≤ (5 / 6) / (v3 : ℝ) - (1 / 3) / v3 := by
    rw [show (5 / 6) / (v3 : ℝ) - (1 / 3) / v3 = 1 / (2 * v3) by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have : 4 * (v3 : ℝ) ≤ 3 * v4 := by exact_mod_cast hwide
    linarith
  obtain ⟨t, h1, h2, c4, c5, -⟩ := two_flank_window p4 r45 (τ + (1 / 3) / (v3 : ℝ)) hL
  obtain ⟨c1, c2, c3⟩ := clear123_after h0 h23 hsmall h2v2 q1 q2 q3 e1 e2 e3 h59a h59b h1
    (by linarith)
  exact ⟨t, c1, c2, c3, by simpa [one_div] using c4, by simpa [one_div] using c5⟩

/-- **The meeting instant with runner 4 across its half lap (BHK Lemma 22 with (59), (60)).**  At a
meeting instant `τ` of runners 2 and 3, runner 1 reads inside (59) and runner 4 reads `q₄ + ρ₄` with
(60): `ρ₄ ≤ 1/2 − v₄/(3v₃)` or `3/2 − 5v₄/(6v₃) ≤ ρ₄`.  Then runner 4 passes its half lap at a named
instant `t₀` of the 123-window, and R6 at `q = 2` (`half_lap_window`) names a lonely instant. -/
theorem lonely_at_meeting (h0 : 0 < v1) (h23 : v2 < v3) (h34 : v3 < v4)
    (h45 : v4 < v5) (hsmall : 3 * v1 < v3) (h2v2 : v3 ≤ 2 * v2) (h43 : 3 * v4 < 4 * v3)
    {τ ρ1 ρ4 : ℝ} (q1 q2 q3 q4 : ℤ) (e1 : (v1 : ℝ) * τ = q1 + ρ1)
    (e2 : (v2 : ℝ) * τ = q2) (e3 : (v3 : ℝ) * τ = q3) (e4 : (v4 : ℝ) * τ = q4 + ρ4)
    (hρ0 : 0 ≤ ρ4) (hρ1 : ρ4 < 1)
    (h59a : 1 / 6 - (v1 : ℝ) / (3 * v3) ≤ ρ1) (h59b : ρ1 ≤ 5 / 6 - 5 * (v1 : ℝ) / (6 * v3))
    (h60 : ρ4 ≤ 1 / 2 - (v4 : ℝ) / (3 * v3) ∨ 3 / 2 - 5 * (v4 : ℝ) / (6 * v3) ≤ ρ4) :
    ∃ t : ℝ, Lonely6 v1 v2 v3 v4 v5 t := by
  have p3 : (0 : ℝ) < v3 := by exact_mod_cast (show 0 < v3 by omega)
  have p4 : (0 : ℝ) < v4 := by exact_mod_cast (show 0 < v4 by omega)
  have r45 : (v4 : ℝ) < v5 := by exact_mod_cast h45
  have r35 : (v3 : ℝ) < v5 := by exact_mod_cast (show v3 < v5 by omega)
  have p5 : (0 : ℝ) < v5 := by linarith
  have l4 : 1 < (v4 : ℝ) / v3 := by rw [one_lt_div p3]; exact_mod_cast h34
  have l4' : (v4 : ℝ) / v3 < 4 / 3 := by
    rw [div_lt_iff₀ p3]; have : 3 * (v4 : ℝ) < 4 * v3 := by exact_mod_cast h43
    linarith
  have f1 : (v4 : ℝ) / (3 * v3) = (v4 : ℝ) / v3 / 3 := by ring
  have f2 : 5 * (v4 : ℝ) / (6 * v3) = 5 / 6 * ((v4 : ℝ) / v3) := by ring
  rw [f1, f2] at h60
  set lam : ℝ := (v4 : ℝ) / v3 with hlam
  have hlam0 : 0 < lam := by linarith
  -- the half-lap instant `t₀ = τ + x₀/v₃` of runner 4
  obtain ⟨x0, m, hx1, hx2, hm⟩ : ∃ x0 : ℝ, ∃ m : ℤ, 1 / 3 ≤ x0 ∧ x0 ≤ 5 / 6 ∧
      (v4 : ℝ) * (τ + x0 / v3) = m + 1 / 2 := by
    have key : ∀ y : ℝ, (v4 : ℝ) * (τ + y / lam / v3) = q4 + ρ4 + y := by
      intro y
      have : (v4 : ℝ) * (y / lam / v3) = y := by rw [hlam]; field_simp
      rw [mul_add, e4, this]
    rcases h60 with h | h
    · refine ⟨(1 / 2 - ρ4) / lam, q4, ?_, ?_, ?_⟩
      · rw [le_div_iff₀ hlam0]; linarith
      · rw [div_le_iff₀ hlam0]; linarith
      · rw [key]; ring
    · refine ⟨(3 / 2 - ρ4) / lam, q4 + 1, ?_, ?_, ?_⟩
      · rw [le_div_iff₀ hlam0]; linarith
      · rw [div_le_iff₀ hlam0]; linarith
      · rw [key]; push_cast; ring
  have hA : τ + (1 / 3) / (v3 : ℝ) ≤ τ + x0 / v3 := by
    have := div_le_div_of_nonneg_right hx1 p3.le; linarith
  have hB : τ + x0 / (v3 : ℝ) ≤ τ + (5 / 6) / v3 := by
    have := div_le_div_of_nonneg_right hx2 p3.le; linarith
  have hlen : 1 / (3 * (v5 : ℝ)) < τ + (5 / 6) / (v3 : ℝ) - (τ + (1 / 3) / v3) := by
    rw [show τ + (5 / 6) / (v3 : ℝ) - (τ + (1 / 3) / v3) = 1 / (2 * v3) by ring,
      div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith
  obtain ⟨t, h1, h2, c4, c5⟩ := half_lap_window p4 r45 hA hB hlen m hm
  obtain ⟨c1, c2, c3⟩ := clear123_after h0 h23 hsmall h2v2 q1 q2 q3 e1 e2 e3 h59a h59b h1 h2
  exact ⟨t, c1, c2, c3, c4, c5⟩

/-! ## 2. §6.2: runners 1 and 4 read alike at the meeting instant

In Case 6.2 the orbit steps by `(1, 1)`, so at the chosen meeting instant runners 1 and 4 read
the same fraction `ρ`.  Everything below is at one meeting instant `τ`, in units `x` of runner 3's
lap: the instant `τ + x/v₃`, where runner `d` reads `(its reading at τ) + (v_d/v₃)·x`. -/

set_option maxHeartbeats 1000000 in
-- many window readings (`clear_after`, `linarith`) in one declaration
/-- **§6.2.1, the bound `v₅ < 2 v₃` (BHK p. 42).**  With `v₃ = 2v₂`, `7v₁ < v₃`, `7v₄ < 8v₃` and
`ρ ∈ [1/3, 1/2]`: on the two windows `[−5/6, x_L]` and `[x_R, 5/6]` (with `(v₄/v₃)·x_L = −(ρ + 1/6)`,
`(v₄/v₃)·x_R = 7/6 − ρ`, the edges of runner 4's clear laps) runners 1–4 are clear, so the flank
`v₅` is clear at a named instant of each, or each sits in one blocked zone of `v₅`.  Two zones span
at most `2/3` of `v₅`'s lap, which is `v₅ < 2v₃`. -/
theorem s621_x5 (h0 : 0 < v1) (h23 : v2 < v3) (h34 : v3 < v4) (h45 : v4 < v5)
    (h32 : v3 = 2 * v2) (hx1 : 7 * v1 < v3) (h74 : 7 * v4 < 8 * v3)
    {τ ρ : ℝ} (q1 q2 q3 q4 : ℤ) (e1 : (v1 : ℝ) * τ = q1 + ρ) (e2 : (v2 : ℝ) * τ = q2)
    (e3 : (v3 : ℝ) * τ = q3) (e4 : (v4 : ℝ) * τ = q4 + ρ) (hρ1 : 1 / 3 ≤ ρ) (hρ2 : ρ ≤ 1 / 2) :
    (∃ t : ℝ, Lonely6 v1 v2 v3 v4 v5 t) ∨ v5 < 2 * v3 := by
  have p3 : (0 : ℝ) < v3 := by exact_mod_cast (show 0 < v3 by omega)
  have p4 : (0 : ℝ) < v4 := by exact_mod_cast (show 0 < v4 by omega)
  have p5 : (0 : ℝ) < v5 := by exact_mod_cast (show 0 < v5 by omega)
  have l1 : (v1 : ℝ) / v3 < 1 / 7 := by
    rw [div_lt_iff₀ p3]; have : 7 * (v1 : ℝ) < v3 := by exact_mod_cast hx1
    linarith
  have l1' : 0 ≤ (v1 : ℝ) / v3 := by positivity
  have l2 : (v2 : ℝ) / v3 = 1 / 2 := by
    rw [div_eq_iff p3.ne']; have : (v3 : ℝ) = 2 * v2 := by exact_mod_cast h32
    linarith
  have l3 : (v3 : ℝ) / v3 = 1 := div_self p3.ne'
  have l4 : 1 < (v4 : ℝ) / v3 := by rw [one_lt_div p3]; exact_mod_cast h34
  have l4' : (v4 : ℝ) / v3 < 8 / 7 := by
    rw [div_lt_iff₀ p3]; have : 7 * (v4 : ℝ) < 8 * v3 := by exact_mod_cast h74
    linarith
  have l5 : 0 < (v5 : ℝ) / v3 := by positivity
  obtain ⟨xL, exL⟩ : ∃ x : ℝ, (v4 : ℝ) / v3 * x = -(ρ + 1 / 6) :=
    ⟨-(ρ + 1 / 6) / ((v4 : ℝ) / v3), by field_simp⟩
  obtain ⟨xR, exR⟩ : ∃ x : ℝ, (v4 : ℝ) / v3 * x = 7 / 6 - ρ :=
    ⟨(7 / 6 - ρ) / ((v4 : ℝ) / v3), by field_simp⟩
  have bL1 : xL ≤ -7 / 16 := by
    by_contra h; push Not at h
    have := mul_lt_mul_of_pos_left h (show (0 : ℝ) < (v4 : ℝ) / v3 by linarith)
    linarith
  have bL2 : -2 / 3 ≤ xL := by
    have h' := mul_neg_of_pos_of_neg (show (0 : ℝ) < (v4 : ℝ) / v3 - 1 by linarith)
      (show xL < 0 by linarith)
    rw [sub_mul, one_mul] at h'
    linarith
  have bR1 : 7 / 12 ≤ xR := by
    by_contra h; push Not at h
    have := mul_lt_mul_of_pos_left h (show (0 : ℝ) < (v4 : ℝ) / v3 by linarith)
    linarith
  have bR2 : xR ≤ 5 / 6 := by
    have h' := mul_pos (show (0 : ℝ) < (v4 : ℝ) / v3 - 1 by linarith)
      (show 0 < xR by linarith)
    rw [sub_mul, one_mul] at h'
    linarith
  have m1L : (v1 : ℝ) / v3 * xL ≤ 0 := mul_nonpos_of_nonneg_of_nonpos l1' (by linarith)
  have m1R : 0 ≤ (v1 : ℝ) / v3 * xR := mul_nonneg l1' (by linarith)
  -- left window: runners 1, 2, 3, 4 in laps 0, −1, −1, −1
  rcases flank_after (f := (v5 : ℝ)) (τ := τ) p5 p3 (show (-5 / 6 : ℝ) ≤ xL by linarith)
      (fun t => 1 / 6 ≤ circDist ((v1 : ℝ) * t) ∧ 1 / 6 ≤ circDist ((v2 : ℝ) * t) ∧
        1 / 6 ≤ circDist ((v3 : ℝ) * t) ∧ 1 / 6 ≤ circDist ((v4 : ℝ) * t))
      (fun t h1 h2 => ⟨
        clear_after (by positivity) q1 0 e1 (by push_cast; linarith) (by push_cast; linarith) h1 h2,
        clear_after (ρ := 0) (by positivity) q2 (-1) (by rw [e2, add_zero])
          (by rw [l2]; push_cast; linarith) (by rw [l2]; push_cast; linarith) h1 h2,
        clear_after (ρ := 0) (by positivity) q3 (-1) (by rw [e3, add_zero])
          (by rw [l3]; push_cast; linarith) (by rw [l3]; push_cast; linarith) h1 h2,
        clear_after (by positivity) q4 (-1) e4 (by push_cast; linarith)
          (by rw [exL]; push_cast; linarith) h1 h2⟩) with
    ⟨t, ⟨c1, c2, c3, c4⟩, c5⟩ | hL
  · exact Or.inl ⟨t, c1, c2, c3, c4, c5⟩
  -- right window: runners 1, 2, 3, 4 in laps 0, 0, 0, 1
  rcases flank_after (f := (v5 : ℝ)) (τ := τ) p5 p3 (show xR ≤ (5 / 6 : ℝ) by linarith)
      (fun t => 1 / 6 ≤ circDist ((v1 : ℝ) * t) ∧ 1 / 6 ≤ circDist ((v2 : ℝ) * t) ∧
        1 / 6 ≤ circDist ((v3 : ℝ) * t) ∧ 1 / 6 ≤ circDist ((v4 : ℝ) * t))
      (fun t h1 h2 => ⟨
        clear_after (by positivity) q1 0 e1 (by push_cast; linarith) (by push_cast; linarith) h1 h2,
        clear_after (ρ := 0) (by positivity) q2 0 (by rw [e2, add_zero])
          (by rw [l2]; push_cast; linarith) (by rw [l2]; push_cast; linarith) h1 h2,
        clear_after (ρ := 0) (by positivity) q3 0 (by rw [e3, add_zero])
          (by rw [l3]; push_cast; linarith) (by rw [l3]; push_cast; linarith) h1 h2,
        clear_after (by positivity) q4 1 e4 (by rw [exR]; push_cast; linarith)
          (by push_cast; linarith) h1 h2⟩) with
    ⟨t, ⟨c1, c2, c3, c4⟩, c5⟩ | hR
  · exact Or.inl ⟨t, c1, c2, c3, c4, c5⟩
  right
  have hsep : xR - xL < 4 / 3 := by
    have h' := mul_pos (show (0 : ℝ) < (v4 : ℝ) / v3 - 1 by linarith)
      (show 0 < xR - xL by linarith)
    have e : ((v4 : ℝ) / v3 - 1) * (xR - xL) = (v4 : ℝ) / v3 * xR - (v4 : ℝ) / v3 * xL - (xR - xL) := by
      ring
    rw [e, exR, exL] at h'
    linarith
  have hsep' : 1 / 3 < 5 / 3 - (xR - xL) := by linarith
  have key : (v5 : ℝ) / v3 * (1 / 3) < 2 / 3 := by
    have h1 := mul_lt_mul_of_pos_left hsep' l5
    have e : (v5 : ℝ) / v3 * (5 / 3 - (xR - xL)) =
        (v5 : ℝ) / v3 * (xL - -5 / 6) + (v5 : ℝ) / v3 * (5 / 6 - xR) := by ring
    rw [e] at h1
    linarith
  have : (v5 : ℝ) < 2 * v3 := by
    rw [show (v5 : ℝ) / v3 * (1 / 3) = v5 / (3 * v3) by ring, div_lt_iff₀ (by positivity)] at key
    linarith
  exact_mod_cast this

set_option maxHeartbeats 1000000 in
-- many window readings (`clear_after`, `linarith`) in one declaration
/-- **§6.2.1, the two instants (BHK p. 42).**  With `v₃ = 2v₂`, `7v₁ < v₃`, `7v₄ < 8v₃`,
`v₅ < 2v₃` and `ρ ∈ [1/3, 1/2]`, runners 1–4 are clear at `τ + 5/(6v₃)` and `τ + 7/(6v₃)`, and the
flank `v₅` is clear at one of them: were it blocked at both, its zones `K₁, K₂` would satisfy
`0 < K₂ − K₁ < 1`, since `v₅` advances `v₅/(3v₃) ∈ (1/3, 2/3)` between the two. -/
theorem s621_kernel (h0 : 0 < v1) (h23 : v2 < v3) (h34 : v3 < v4) (h45 : v4 < v5)
    (h32 : v3 = 2 * v2) (hx1 : 7 * v1 < v3) (h74 : 7 * v4 < 8 * v3) (hx5 : v5 < 2 * v3)
    {τ ρ : ℝ} (q1 q2 q3 q4 : ℤ) (e1 : (v1 : ℝ) * τ = q1 + ρ) (e2 : (v2 : ℝ) * τ = q2)
    (e3 : (v3 : ℝ) * τ = q3) (e4 : (v4 : ℝ) * τ = q4 + ρ) (hρ1 : 1 / 3 ≤ ρ) (hρ2 : ρ ≤ 1 / 2) :
    ∃ t : ℝ, Lonely6 v1 v2 v3 v4 v5 t := by
  have p3 : (0 : ℝ) < v3 := by exact_mod_cast (show 0 < v3 by omega)
  have l1 : (v1 : ℝ) / v3 < 1 / 7 := by
    rw [div_lt_iff₀ p3]; have : 7 * (v1 : ℝ) < v3 := by exact_mod_cast hx1
    linarith
  have l1' : 0 ≤ (v1 : ℝ) / v3 := by positivity
  have l2 : (v2 : ℝ) / v3 = 1 / 2 := by
    rw [div_eq_iff p3.ne']; have : (v3 : ℝ) = 2 * v2 := by exact_mod_cast h32
    linarith
  have l3 : (v3 : ℝ) / v3 = 1 := div_self p3.ne'
  have l4 : 1 < (v4 : ℝ) / v3 := by rw [one_lt_div p3]; exact_mod_cast h34
  have l4' : (v4 : ℝ) / v3 < 8 / 7 := by
    rw [div_lt_iff₀ p3]; have : 7 * (v4 : ℝ) < 8 * v3 := by exact_mod_cast h74
    linarith
  have l5 : 1 < (v5 : ℝ) / v3 := by rw [one_lt_div p3]; exact_mod_cast (show v3 < v5 by omega)
  have l5' : (v5 : ℝ) / v3 < 2 := by
    rw [div_lt_iff₀ p3]; have : (v5 : ℝ) < 2 * v3 := by exact_mod_cast hx5
    linarith
  -- the instant `τ + 5/(6v₃)`: laps 0, 0, 0, 1
  rcases flank_at (v5 : ℝ) v3 τ (5 / 6) with c5 | ⟨K1, hK1a, hK1b⟩
  · exact ⟨τ + (5 / 6) / v3,
      clear_after (by positivity) q1 0 e1 (by push_cast; linarith) (by push_cast; linarith) le_rfl le_rfl,
      clear_after (ρ := 0) (by positivity) q2 0 (by rw [e2, add_zero])
        (by rw [l2]; push_cast; linarith) (by rw [l2]; push_cast; linarith) le_rfl le_rfl,
      clear_after (ρ := 0) (by positivity) q3 0 (by rw [e3, add_zero])
        (by rw [l3]; push_cast; linarith) (by rw [l3]; push_cast; linarith) le_rfl le_rfl,
      clear_after (by positivity) q4 1 e4 (by push_cast; linarith) (by push_cast; linarith) le_rfl le_rfl,
      c5⟩
  -- the instant `τ + 7/(6v₃)`: laps 0, 0, 1, 1
  rcases flank_at (v5 : ℝ) v3 τ (7 / 6) with c5 | ⟨K2, hK2a, hK2b⟩
  · exact ⟨τ + (7 / 6) / v3,
      clear_after (by positivity) q1 0 e1 (by push_cast; linarith) (by push_cast; linarith) le_rfl le_rfl,
      clear_after (ρ := 0) (by positivity) q2 0 (by rw [e2, add_zero])
        (by rw [l2]; push_cast; linarith) (by rw [l2]; push_cast; linarith) le_rfl le_rfl,
      clear_after (ρ := 0) (by positivity) q3 1 (by rw [e3, add_zero])
        (by rw [l3]; push_cast; linarith) (by rw [l3]; push_cast; linarith) le_rfl le_rfl,
      clear_after (by positivity) q4 1 e4 (by push_cast; linarith) (by push_cast; linarith) le_rfl le_rfl,
      c5⟩
  exfalso
  have k1 : (K1 : ℝ) < K2 := by linarith
  have k2 : (K2 : ℝ) < K1 + 1 := by linarith
  have k1' : K1 < K2 := by exact_mod_cast k1
  have k2' : K2 < K1 + 1 := by exact_mod_cast k2
  omega

/-- **§6.2.2, the 123-window from a quarter lap (BHK p. 42).**  With `2v₃ ≤ 3v₂` (`K ≥ 2`) and runner 1
reading `ρ₁ ∈ [1/6, 1/2]` at the meeting instant, runners 1–3 are clear across
`[τ + 1/(4v₃), τ + 5/(6v₃)]`. -/
theorem clear123_quarter (h0 : 0 < v1) (h23 : v2 < v3) (hsmall : 3 * v1 < v3)
    (h32 : 2 * v3 ≤ 3 * v2) {τ ρ1 : ℝ} (q1 q2 q3 : ℤ) (e1 : (v1 : ℝ) * τ = q1 + ρ1)
    (e2 : (v2 : ℝ) * τ = q2) (e3 : (v3 : ℝ) * τ = q3) (hρ1 : 1 / 6 ≤ ρ1) (hρ2 : ρ1 ≤ 1 / 2)
    {t : ℝ} (ht1 : τ + (1 / 4) / (v3 : ℝ) ≤ t) (ht2 : t ≤ τ + (5 / 6) / (v3 : ℝ)) :
    1 / 6 ≤ circDist ((v1 : ℝ) * t) ∧ 1 / 6 ≤ circDist ((v2 : ℝ) * t) ∧
      1 / 6 ≤ circDist ((v3 : ℝ) * t) := by
  have p3 : (0 : ℝ) < v3 := by exact_mod_cast (show 0 < v3 by omega)
  have l1 : (v1 : ℝ) / v3 < 1 / 3 := by
    rw [div_lt_iff₀ p3]; have : 3 * (v1 : ℝ) < v3 := by exact_mod_cast hsmall
    linarith
  have l1' : 0 ≤ (v1 : ℝ) / v3 := by positivity
  have l2 : 2 / 3 ≤ (v2 : ℝ) / v3 := by
    rw [le_div_iff₀ p3]; have : 2 * (v3 : ℝ) ≤ 3 * v2 := by exact_mod_cast h32
    linarith
  have l2' : (v2 : ℝ) / v3 < 1 := by
    rw [div_lt_one p3]; exact_mod_cast h23
  have l3 : (v3 : ℝ) / v3 = 1 := div_self p3.ne'
  refine ⟨?_, ?_, ?_⟩
  · exact clear_after (by positivity) q1 0 e1 (by push_cast; linarith) (by push_cast; linarith) ht1 ht2
  · exact clear_after (ρ := 0) (by positivity) q2 0 (by rw [e2, add_zero])
      (by push_cast; linarith) (by push_cast; linarith) ht1 ht2
  · exact clear_after (ρ := 0) (by positivity) q3 0 (by rw [e3, add_zero])
      (by rw [l3]; push_cast; linarith) (by rw [l3]; push_cast; linarith) ht1 ht2

set_option maxHeartbeats 1000000 in
-- many window readings (`clear_after`, `linarith`) in one declaration
/-- **§6.2.2, the flank bound `2v₄ < v₅` (BHK p. 42).**  With `K ≥ 2` and `ρ ∈ [1/3, 1/2]`, runner 4
is clear at both ends of the 123-window `[τ + 1/(4v₃), τ + 5/(6v₃)]`.  The flank `v₅` is clear at
one end (lonely there), or blocked at both, in zones `K₁ < K₂`; then `v₅`'s whole clear lap
`[(K₁ + 1/6)/v₅, (K₁ + 5/6)/v₅]` lies in the window, and on it runner 4 is clear at a named
instant (lonely), or the lap sits in one blocked zone of runner 4: `2v₄ < v₅`. -/
theorem s622_flank (h0 : 0 < v1) (h23 : v2 < v3) (h34 : v3 < v4) (h45 : v4 < v5)
    (hsmall : 3 * v1 < v3) (h32 : 2 * v3 ≤ 3 * v2) (h43 : 3 * v4 < 4 * v3)
    {τ ρ : ℝ} (q1 q2 q3 q4 : ℤ) (e1 : (v1 : ℝ) * τ = q1 + ρ) (e2 : (v2 : ℝ) * τ = q2)
    (e3 : (v3 : ℝ) * τ = q3) (e4 : (v4 : ℝ) * τ = q4 + ρ) (hρ1 : 1 / 3 ≤ ρ) (hρ2 : ρ ≤ 1 / 2) :
    (∃ t : ℝ, Lonely6 v1 v2 v3 v4 v5 t) ∨ 2 * v4 < v5 := by
  have p3 : (0 : ℝ) < v3 := by exact_mod_cast (show 0 < v3 by omega)
  have p4 : (0 : ℝ) < v4 := by exact_mod_cast (show 0 < v4 by omega)
  have p5 : (0 : ℝ) < v5 := by exact_mod_cast (show 0 < v5 by omega)
  have l4 : 1 < (v4 : ℝ) / v3 := by rw [one_lt_div p3]; exact_mod_cast h34
  have l4' : (v4 : ℝ) / v3 < 4 / 3 := by
    rw [div_lt_iff₀ p3]; have : 3 * (v4 : ℝ) < 4 * v3 := by exact_mod_cast h43
    linarith
  have l5 : 1 < (v5 : ℝ) / v3 := by rw [one_lt_div p3]; exact_mod_cast (show v3 < v5 by omega)
  have c123 := fun t (h1 : τ + (1 / 4) / (v3 : ℝ) ≤ t) (h2 : t ≤ τ + (5 / 6) / (v3 : ℝ)) =>
    clear123_quarter h0 h23 hsmall h32 q1 q2 q3 e1 e2 e3 (by linarith) hρ2 h1 h2
  have hq : (1 / 4) / (v3 : ℝ) ≤ (5 / 6) / v3 := div_le_div_of_nonneg_right (by norm_num) p3.le
  -- the window's start: runner 4 in lap 0
  rcases flank_at (v5 : ℝ) v3 τ (1 / 4) with c5 | ⟨K1, hK1a, hK1b⟩
  · obtain ⟨c1, c2, c3⟩ := c123 _ le_rfl (by linarith)
    exact Or.inl ⟨_, c1, c2, c3,
      clear_after (by positivity) q4 0 e4 (by push_cast; linarith) (by push_cast; linarith)
        le_rfl le_rfl, c5⟩
  -- the window's end: runner 4 in lap 1
  rcases flank_at (v5 : ℝ) v3 τ (5 / 6) with c5 | ⟨K2, hK2a, hK2b⟩
  · obtain ⟨c1, c2, c3⟩ := c123 _ (by linarith) le_rfl
    exact Or.inl ⟨_, c1, c2, c3,
      clear_after (by positivity) q4 1 e4 (by push_cast; linarith) (by push_cast; linarith)
        le_rfl le_rfl, c5⟩
  -- two different zones: `v₅`'s clear lap `K₁` lies inside the window
  have hK : (K1 : ℝ) + 1 ≤ K2 := by
    have : (K1 : ℝ) < K2 := by linarith
    have : K1 < K2 := by exact_mod_cast this
    exact_mod_cast (show K1 + 1 ≤ K2 by omega)
  set T1 : ℝ := ((K1 : ℝ) + 1 / 6) / v5 with hT1
  set T2 : ℝ := ((K1 : ℝ) + 5 / 6) / v5 with hT2
  have eA : (v5 : ℝ) * (τ + (1 / 4) / v3) = v5 * τ + v5 / v3 * (1 / 4) := by ring
  have eB : (v5 : ℝ) * (τ + (5 / 6) / v3) = v5 * τ + v5 / v3 * (5 / 6) := by ring
  have hAT : τ + (1 / 4) / (v3 : ℝ) ≤ T1 := by
    rw [hT1, le_div_iff₀ p5, mul_comm, eA]; linarith
  have hTB : T2 ≤ τ + (5 / 6) / (v3 : ℝ) := by
    rw [hT2, div_le_iff₀ p5, mul_comm, eB]; linarith
  have hT12 : T1 ≤ T2 := by rw [hT1, hT2]; exact div_le_div_of_nonneg_right (by linarith) p5.le
  have e5 : ∀ t, T1 ≤ t → t ≤ T2 → 1 / 6 ≤ circDist ((v5 : ℝ) * t) := by
    intro t h1 h2
    refine clear_of_lap p5.le K1 ?_ ?_ h1 h2
    · rw [hT1, mul_div_cancel₀ _ p5.ne']
    · rw [hT2, mul_div_cancel₀ _ p5.ne']
  rcases window_or_inside p4 hT12
      (fun t => 1 / 6 ≤ circDist ((v1 : ℝ) * t) ∧ 1 / 6 ≤ circDist ((v2 : ℝ) * t) ∧
        1 / 6 ≤ circDist ((v3 : ℝ) * t) ∧ 1 / 6 ≤ circDist ((v5 : ℝ) * t))
      (fun t h1 h2 => by
        obtain ⟨c1, c2, c3⟩ := c123 t (by linarith) (by linarith)
        exact ⟨c1, c2, c3, e5 t h1 h2⟩) with
    ⟨t, -, -, ⟨c1, c2, c3, c5⟩, c4⟩ | ⟨k, hk1, hk2⟩
  · exact Or.inl ⟨t, c1, c2, c3, c4, c5⟩
  · right
    have hlen : (v4 : ℝ) * T2 - v4 * T1 = 2 * v4 / (3 * v5) := by
      rw [hT1, hT2]; field_simp; ring
    have : 2 * (v4 : ℝ) / (3 * v5) < 1 / 3 := by linarith
    rw [div_lt_iff₀ (by positivity)] at this
    have : 2 * (v4 : ℝ) < v5 := by linarith
    exact_mod_cast this

set_option maxHeartbeats 1000000 in
-- many window readings (`clear_after`, `linarith`) in one declaration
/-- **§6.2.2, the 1234-window (BHK pp. 42–43), `ρ ∈ [1/6, 1/3]`.**  With `2v₄ < v₅`: runners 1–4 are
clear across `[τ + 1/(4v₃), τ + x_E/v₃]`, `(v₄/v₃)·x_E = 5/6 − ρ` (the end of runner 4's clear lap),
which is longer than one blocked zone of `v₅`; so `v₅` is clear at a named instant of it. -/
theorem s622_final (h0 : 0 < v1) (h23 : v2 < v3) (h34 : v3 < v4) (h45 : 2 * v4 < v5)
    (hsmall : 3 * v1 < v3) (h32 : 2 * v3 ≤ 3 * v2) (h43 : 3 * v4 < 4 * v3)
    {τ ρ : ℝ} (q1 q2 q3 q4 : ℤ) (e1 : (v1 : ℝ) * τ = q1 + ρ) (e2 : (v2 : ℝ) * τ = q2)
    (e3 : (v3 : ℝ) * τ = q3) (e4 : (v4 : ℝ) * τ = q4 + ρ) (hρ1 : 1 / 6 ≤ ρ) (hρ2 : ρ ≤ 1 / 3) :
    ∃ t : ℝ, Lonely6 v1 v2 v3 v4 v5 t := by
  have p3 : (0 : ℝ) < v3 := by exact_mod_cast (show 0 < v3 by omega)
  have p4 : (0 : ℝ) < v4 := by exact_mod_cast (show 0 < v4 by omega)
  have p5 : (0 : ℝ) < v5 := by exact_mod_cast (show 0 < v5 by omega)
  have l4 : 1 < (v4 : ℝ) / v3 := by rw [one_lt_div p3]; exact_mod_cast h34
  have l4' : (v4 : ℝ) / v3 < 4 / 3 := by
    rw [div_lt_iff₀ p3]; have : 3 * (v4 : ℝ) < 4 * v3 := by exact_mod_cast h43
    linarith
  have l5 : 2 * ((v4 : ℝ) / v3) < (v5 : ℝ) / v3 := by
    rw [← mul_div_assoc, div_lt_div_iff_of_pos_right p3]; exact_mod_cast h45
  obtain ⟨xE, exE⟩ : ∃ x : ℝ, (v4 : ℝ) / v3 * x = 5 / 6 - ρ :=
    ⟨(5 / 6 - ρ) / ((v4 : ℝ) / v3), by field_simp⟩
  have bE1 : 3 / 8 ≤ xE := by
    by_contra h; push Not at h
    have := mul_lt_mul_of_pos_left h (show (0 : ℝ) < (v4 : ℝ) / v3 by linarith)
    linarith
  have bE2 : xE ≤ 5 / 6 := by
    have h' := mul_pos (show (0 : ℝ) < (v4 : ℝ) / v3 - 1 by linarith) (show 0 < xE by linarith)
    rw [sub_mul, one_mul] at h'
    linarith
  rcases flank_after (f := (v5 : ℝ)) (τ := τ) p5 p3 (show (1 / 4 : ℝ) ≤ xE by linarith)
      (fun t => 1 / 6 ≤ circDist ((v1 : ℝ) * t) ∧ 1 / 6 ≤ circDist ((v2 : ℝ) * t) ∧
        1 / 6 ≤ circDist ((v3 : ℝ) * t) ∧ 1 / 6 ≤ circDist ((v4 : ℝ) * t))
      (fun t h1 h2 => by
        have h2' : t ≤ τ + (5 / 6) / (v3 : ℝ) := by
          have := div_le_div_of_nonneg_right bE2 p3.le; linarith
        obtain ⟨c1, c2, c3⟩ := clear123_quarter h0 h23 hsmall h32 q1 q2 q3 e1 e2 e3 hρ1
          (by linarith) h1 h2'
        exact ⟨c1, c2, c3, clear_after (by positivity) q4 0 e4 (by push_cast; linarith)
          (by rw [exE]; push_cast; linarith) h1 h2⟩) with
    ⟨t, ⟨c1, c2, c3, c4⟩, c5⟩ | hL
  · exact ⟨t, c1, c2, c3, c4, c5⟩
  · exfalso
    have h1 := mul_lt_mul_of_pos_right l5 (show (0 : ℝ) < xE - 1 / 4 by linarith)
    have e : 2 * ((v4 : ℝ) / v3) * (xE - 1 / 4) = 2 * ((v4 : ℝ) / v3 * xE) - (v4 : ℝ) / v3 / 2 := by
      ring
    rw [e, exE] at h1
    linarith

set_option maxHeartbeats 1000000 in
-- many window readings (`clear_after`, `linarith`) in one declaration
/-- **§6.2.2, the 1234-window (BHK p. 43), `ρ = 1/2` (`n = 2`).**  With `2v₄ < v₅`: runners 1–4
are clear across `[τ + x_O/v₃, τ + 5/(6v₃)]`, `(v₄/v₃)·x_O = 2/3` (runner 4's opening of lap 1), which
is longer than one blocked zone of `v₅`; so `v₅` is clear at a named instant of it. -/
theorem s622_final_half (h0 : 0 < v1) (h23 : v2 < v3) (h34 : v3 < v4) (h45 : 2 * v4 < v5)
    (hsmall : 3 * v1 < v3) (h32 : 2 * v3 ≤ 3 * v2) (h43 : 3 * v4 < 4 * v3)
    {τ : ℝ} (q1 q2 q3 q4 : ℤ) (e1 : (v1 : ℝ) * τ = q1 + 1 / 2) (e2 : (v2 : ℝ) * τ = q2)
    (e3 : (v3 : ℝ) * τ = q3) (e4 : (v4 : ℝ) * τ = q4 + 1 / 2) :
    ∃ t : ℝ, Lonely6 v1 v2 v3 v4 v5 t := by
  have p3 : (0 : ℝ) < v3 := by exact_mod_cast (show 0 < v3 by omega)
  have p4 : (0 : ℝ) < v4 := by exact_mod_cast (show 0 < v4 by omega)
  have p5 : (0 : ℝ) < v5 := by exact_mod_cast (show 0 < v5 by omega)
  have l4 : 1 < (v4 : ℝ) / v3 := by rw [one_lt_div p3]; exact_mod_cast h34
  have l4' : (v4 : ℝ) / v3 < 4 / 3 := by
    rw [div_lt_iff₀ p3]; have : 3 * (v4 : ℝ) < 4 * v3 := by exact_mod_cast h43
    linarith
  have l5 : 2 * ((v4 : ℝ) / v3) < (v5 : ℝ) / v3 := by
    rw [← mul_div_assoc, div_lt_div_iff_of_pos_right p3]; exact_mod_cast h45
  obtain ⟨xO, exO⟩ : ∃ x : ℝ, (v4 : ℝ) / v3 * x = 2 / 3 :=
    ⟨(2 / 3) / ((v4 : ℝ) / v3), by field_simp⟩
  have bO1 : 1 / 2 ≤ xO := by
    by_contra h; push Not at h
    have := mul_lt_mul_of_pos_left h (show (0 : ℝ) < (v4 : ℝ) / v3 by linarith)
    linarith
  have bO2 : xO ≤ 2 / 3 := by
    have h' := mul_pos (show (0 : ℝ) < (v4 : ℝ) / v3 - 1 by linarith) (show 0 < xO by linarith)
    rw [sub_mul, one_mul] at h'
    linarith
  rcases flank_after (f := (v5 : ℝ)) (τ := τ) p5 p3 (show xO ≤ (5 / 6 : ℝ) by linarith)
      (fun t => 1 / 6 ≤ circDist ((v1 : ℝ) * t) ∧ 1 / 6 ≤ circDist ((v2 : ℝ) * t) ∧
        1 / 6 ≤ circDist ((v3 : ℝ) * t) ∧ 1 / 6 ≤ circDist ((v4 : ℝ) * t))
      (fun t h1 h2 => by
        have h1' : τ + (1 / 4) / (v3 : ℝ) ≤ t := by
          have := div_le_div_of_nonneg_right (show (1 / 4 : ℝ) ≤ xO by linarith) p3.le; linarith
        obtain ⟨c1, c2, c3⟩ := clear123_quarter h0 h23 hsmall h32 q1 q2 q3 e1 e2 e3 (by norm_num)
          le_rfl h1' h2
        exact ⟨c1, c2, c3, clear_after (by positivity) q4 1 e4 (by rw [exO]; push_cast; linarith)
          (by push_cast; linarith) h1 h2⟩) with
    ⟨t, ⟨c1, c2, c3, c4⟩, c5⟩ | hL
  · exact ⟨t, c1, c2, c3, c4, c5⟩
  · exfalso
    have h1 := mul_lt_mul_of_pos_right l5 (show (0 : ℝ) < 5 / 6 - xO by linarith)
    have e : 2 * ((v4 : ℝ) / v3) * (5 / 6 - xO) = 5 / 3 * ((v4 : ℝ) / v3) - 2 * ((v4 : ℝ) / v3 * xO) := by
      ring
    rw [e, exO] at h1
    linarith

end Meeting

/-! ## 3. windows from the start: §6.2.1's `7v₁ < v₃` and §6.5.1's chain

These steps are at the meeting instant `0` itself, so they are the whole-number windows of §8
(`step4`): four runners in named laps across `[p/(6a), q/(6b)]`, and a flank that is clear at a
named instant there, or else sits in one blocked zone. -/

section Start

variable {v1 v2 v3 v4 v5 : ℕ}

set_option maxHeartbeats 1000000 in
-- many window readings (`clear_after`, `linarith`) in one declaration
/-- **§6.2.1, `7v₁ < v₃` (BHK Lemma 23, p. 42).**  With `v₃ = 2v₂`, `v₄ = v₁ + v₃` and `3v₄ < 4v₃`:
if `v₃ ≤ 7v₁`, runners 1–3 are clear across `[7/(6v₃), 10/(6v₃)]`.  If `10v₄ ≤ 11v₃` runner 4 is too,
and the flank `v₅` is clear at a named instant (one zone cannot hold the window).  Otherwise the
window `[7/(6v₃), 11/(6v₄)]` puts `v₅`'s zone at `2` (`11v₃ < 7v₅`, `11v₅ < 13v₄`); then either
`13v₃ ≤ 10v₄` and runner 4's opening `13/(6v₄)` is lonely (the flank `v₅` has no zone there), or
`10v₄ < 13v₃`, which contradicts the zone.  So a lonely instant is named, or `7v₁ < v₃`. -/
theorem s621_x1 (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3) (h34 : v3 < v4) (h45 : v4 < v5)
    (hsmall : 3 * v1 < v3) (h32 : v3 = 2 * v2) (h41 : v4 = v1 + v3) (h43 : 3 * v4 < 4 * v3) :
    (∃ t : ℝ, 0 < t ∧ Lonely6 v1 v2 v3 v4 v5 t) ∨ 7 * v1 < v3 := by
  by_cases hx : 7 * v1 < v3
  · exact Or.inr hx
  left
  push Not at hx
  have z0 : (0 : ℤ) < v1 := by exact_mod_cast h0
  have z12 : (v1 : ℤ) < v2 := by exact_mod_cast h12
  have z23 : (v2 : ℤ) < v3 := by exact_mod_cast h23
  have z34 : (v3 : ℤ) < v4 := by exact_mod_cast h34
  have z45 : (v4 : ℤ) < v5 := by exact_mod_cast h45
  have zs : 3 * (v1 : ℤ) < v3 := by exact_mod_cast hsmall
  have z32 : (v3 : ℤ) = 2 * v2 := by exact_mod_cast h32
  have z41 : (v4 : ℤ) = v1 + v3 := by exact_mod_cast h41
  have z43 : 3 * (v4 : ℤ) < 4 * v3 := by exact_mod_cast h43
  have zx : (v3 : ℤ) ≤ 7 * v1 := by exact_mod_cast hx
  by_cases hA : 10 * v4 ≤ 11 * v3
  · have zA : 10 * (v4 : ℤ) ≤ 11 * v3 := by exact_mod_cast hA
    -- the 1234-window `[7/(6v₃), 10/(6v₃)]`, flank `v₅`
    rcases step4 (x := v5) (a := v3) (b := v3) (p := 7) (q := 10) (d1 := v1) (d2 := v2) (d3 := v3)
        (d4 := v4) (by omega) (by omega) (by omega) (by norm_num) (by push_cast; linarith) 0 0 1 1
        (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith) with
      ⟨t, ht, c1, c2, c3, c4, c5⟩ | ⟨k, hkL, hkR⟩
    · exact ⟨t, ht, c1, c2, c3, c4, c5⟩
    exfalso
    push_cast at hkL hkR
    have hk : k ≤ 0 := by
      by_contra hc; push Not at hc
      have : (6 * 1 - 1) * (v3 : ℤ) ≤ (6 * k - 1) * v3 := mul_le_mul_of_nonneg_right (by omega) (by omega)
      nlinarith
    have : (6 * k + 1) * (v3 : ℤ) ≤ 1 * v3 := mul_le_mul_of_nonneg_right (by omega) (by omega)
    linarith
  · have zA : 11 * (v3 : ℤ) < 10 * v4 := by push Not at hA; exact_mod_cast hA
    -- the window `[7/(6v₃), 11/(6v₄)]`, flank `v₅`
    rcases step4 (x := v5) (a := v3) (b := v4) (p := 7) (q := 11) (d1 := v1) (d2 := v2) (d3 := v3)
        (d4 := v4) (by omega) (by omega) (by omega) (by norm_num) (by push_cast; linarith) 0 0 1 1
        (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) (by push_cast; linarith) with
      ⟨t, ht, c1, c2, c3, c4, c5⟩ | ⟨k, hkL, hkR⟩
    · exact ⟨t, ht, c1, c2, c3, c4, c5⟩
    push_cast at hkL hkR
    have hk2 : 2 ≤ k := by
      by_contra hc; push Not at hc
      have : (6 * k + 1) * (v4 : ℤ) ≤ 7 * v4 := mul_le_mul_of_nonneg_right (by omega) (by omega)
      nlinarith
    have hk : k = 2 := by
      by_contra hc
      have : 17 * (v3 : ℤ) ≤ (6 * k - 1) * v3 := mul_le_mul_of_nonneg_right (by omega) (by omega)
      have e : (6 * k + 1) * (3 * (v4 : ℤ)) < (6 * k + 1) * (4 * v3) :=
        mul_lt_mul_of_pos_left z43 (by omega)
      nlinarith
    subst hk
    by_cases hB : 13 * v3 ≤ 10 * v4
    · have zB : 13 * (v3 : ℤ) ≤ 10 * v4 := by exact_mod_cast hB
      -- runner 4's opening `13/(6v₄)`, flank `v₅`
      rcases step4 (x := v5) (a := v4) (b := v4) (p := 13) (q := 13) (d1 := v1) (d2 := v2)
          (d3 := v3) (d4 := v4) (by omega) (by omega) (by omega) (by norm_num) le_rfl 0 0 1 2
          (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
          (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
          (by push_cast; linarith) (by push_cast; linarith) with
        ⟨t, ht, c1, c2, c3, c4, c5⟩ | ⟨k, hkL', hkR'⟩
      · exact ⟨t, ht, c1, c2, c3, c4, c5⟩
      exfalso
      push_cast at hkL' hkR'
      rcases le_or_gt k 2 with hc | hc
      · have : (6 * k + 1) * (v4 : ℤ) ≤ 13 * v4 := mul_le_mul_of_nonneg_right (by omega) (by omega)
        linarith
      · have : 17 * (v4 : ℤ) ≤ (6 * k - 1) * v4 := mul_le_mul_of_nonneg_right (by omega) (by omega)
        linarith
    · exfalso
      push Not at hB
      have zB : 10 * (v4 : ℤ) < 13 * v3 := by exact_mod_cast hB
      linarith

set_option maxHeartbeats 1000000 in
-- many window readings (`clear_after`, `linarith`) in one declaration
/-- **§6.5.1, the chain (62)–(64) (BHK p. 43).**  With `v₃ ≤ 2v₂`, (62) `25v₄ < 27v₃` and
(63) `7v₃ < 25v₁`:
1. the 1234-window `[1/(6v₁), 5/(6v₄)]`, flank `v₅`: lonely, or zone `1`: `5v₁ < v₅`, `5v₅ < 7v₄`;
2. the instant `7/(6v₃)`, flank `v₂`: lonely, or zone `1`: `5v₃ < 7v₂`;
3. the instant `7/(6v₂)`, flank `v₅`: lonely, or zone `2`: `11v₂ < 7v₅ < 13v₂`;
4. then `v₅`'s opening `13/(6v₅)` is lonely: every runner is in a clear lap there. -/
theorem s651_kernel (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3) (h34 : v3 < v4) (h45 : v4 < v5)
    (hsmall : 3 * v1 < v3) (h2v2 : v3 ≤ 2 * v2) (h62 : 25 * v4 < 27 * v3)
    (h63 : 7 * v3 < 25 * v1) :
    ∃ t : ℝ, 0 < t ∧ Lonely6 v1 v2 v3 v4 v5 t := by
  have z0 : (0 : ℤ) < v1 := by exact_mod_cast h0
  have z12 : (v1 : ℤ) < v2 := by exact_mod_cast h12
  have z23 : (v2 : ℤ) < v3 := by exact_mod_cast h23
  have z34 : (v3 : ℤ) < v4 := by exact_mod_cast h34
  have z45 : (v4 : ℤ) < v5 := by exact_mod_cast h45
  have zs : 3 * (v1 : ℤ) < v3 := by exact_mod_cast hsmall
  have z2 : (v3 : ℤ) ≤ 2 * v2 := by exact_mod_cast h2v2
  have z62 : 25 * (v4 : ℤ) < 27 * v3 := by exact_mod_cast h62
  have z63 : 7 * (v3 : ℤ) < 25 * v1 := by exact_mod_cast h63
  -- step 1: the 1234-window, flank `v₅`
  rcases step4 (x := v5) (a := v1) (b := v4) (p := 1) (q := 5) (d1 := v1) (d2 := v2) (d3 := v3)
      (d4 := v4) (by omega) h0 (by omega) one_pos (by push_cast; linarith) 0 0 0 0
      (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith) (by push_cast; linarith) with
    ⟨t, ht, c1, c2, c3, c4, c5⟩ | ⟨j, hjL, hjR⟩
  · exact ⟨t, ht, c1, c2, c3, c4, c5⟩
  push_cast at hjL hjR
  have hj1 : 1 ≤ j := by
    by_contra hc; push Not at hc
    have : (6 * j + 1) * (v4 : ℤ) ≤ 1 * v4 := mul_le_mul_of_nonneg_right (by omega) (by omega)
    nlinarith
  have hj : j = 1 := by
    by_contra hc
    have hj2 : 2 ≤ j := by omega
    have e : (6 * j + 1) * (175 * (v4 : ℤ)) < (6 * j + 1) * (675 * v1) :=
      mul_lt_mul_of_pos_left (by linarith) (by omega)
    have e2 : 11 * (v1 : ℤ) ≤ (6 * j - 1) * v1 := mul_le_mul_of_nonneg_right (by omega) (by omega)
    nlinarith
  subst hj
  have z64a : 5 * (v1 : ℤ) < v5 := by linarith
  have z64b : 5 * (v5 : ℤ) < 7 * v4 := by linarith
  -- step 2: the instant `7/(6v₃)`, flank `v₂`
  rcases step4 (x := v2) (a := v3) (b := v3) (p := 7) (q := 7) (d1 := v1) (d2 := v3) (d3 := v4)
      (d4 := v5) (by omega) (by omega) (by omega) (by norm_num) le_rfl 0 1 1 1
      (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith) (by push_cast; linarith) with
    ⟨t, ht, c1, c3, c4, c5, c2⟩ | ⟨k, hkL, hkR⟩
  · exact ⟨t, ht, c1, c2, c3, c4, c5⟩
  push_cast at hkL hkR
  have hk : k = 1 := by
    rcases lt_trichotomy k 1 with h | h | h
    · have : (6 * k + 1) * (v3 : ℤ) ≤ 1 * v3 := mul_le_mul_of_nonneg_right (by omega) (by omega)
      linarith
    · exact h
    · have : 11 * (v3 : ℤ) ≤ (6 * k - 1) * v3 := mul_le_mul_of_nonneg_right (by omega) (by omega)
      linarith
  subst hk
  have z2b : 5 * (v3 : ℤ) < 7 * v2 := by linarith
  -- step 3: the instant `7/(6v₂)`, flank `v₅`
  rcases step4 (x := v5) (a := v2) (b := v2) (p := 7) (q := 7) (d1 := v1) (d2 := v2) (d3 := v3)
      (d4 := v4) (by omega) (by omega) (by omega) (by norm_num) le_rfl 0 1 1 1
      (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith) (by push_cast; linarith) with
    ⟨t, ht, c1, c2, c3, c4, c5⟩ | ⟨k, hkL, hkR⟩
  · exact ⟨t, ht, c1, c2, c3, c4, c5⟩
  push_cast at hkL hkR
  have hk : k = 2 := by
    rcases lt_trichotomy k 2 with h | h | h
    · have : (6 * k + 1) * (v2 : ℤ) ≤ 7 * v2 := mul_le_mul_of_nonneg_right (by omega) (by omega)
      linarith
    · exact h
    · have : 17 * (v2 : ℤ) ≤ (6 * k - 1) * v2 := mul_le_mul_of_nonneg_right (by omega) (by omega)
      linarith
  subst hk
  have zC1 : 11 * (v2 : ℤ) < 7 * v5 := by linarith
  have zC2 : 7 * (v5 : ℤ) < 13 * v2 := by linarith
  -- step 4: `v₅`'s opening `13/(6v₅)`: every runner is clear
  have p5 : 0 < v5 := by omega
  refine ⟨(13 : ℕ) / (6 * (v5 : ℝ)), window_pos (by norm_num) p5 le_rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact clear_window (p := 13) (q := 13) p5 p5 0 (by push_cast; linarith) (by push_cast; linarith)
      le_rfl le_rfl
  · exact clear_window (p := 13) (q := 13) p5 p5 1 (by push_cast; linarith) (by push_cast; linarith)
      le_rfl le_rfl
  · exact clear_window (p := 13) (q := 13) p5 p5 1 (by push_cast; linarith) (by push_cast; linarith)
      le_rfl le_rfl
  · exact clear_window (p := 13) (q := 13) p5 p5 1 (by push_cast; linarith) (by push_cast; linarith)
      le_rfl le_rfl
  · exact clear_window (p := 13) (q := 13) p5 p5 2 (by push_cast; linarith) (by push_cast; linarith)
      le_rfl le_rfl

end Start

/-! ## 4. the meeting times `k/D` of runners 2 and 3, read on the orbit

Write `D = v₃ − v₂`, `v₂ = K·D`, `v₃ = (K + 1)·D`, and `g = gcd(D, v₁, v₄)`, `D = g·n`, `v₁ = g·c₁`,
`v₄ = g·c₄`.  At the meeting time `k/D` runners 2 and 3 read whole numbers, and runners 1 and 4
read `(c₁k mod n)/n` and `(c₄k mod n)/n` past a whole number: the orbit
`k ↦ ((c₁k) % n, (c₄k) % n)` of `GlobalIsolationTwoN`. -/

/-- At the meeting time `k/(g·n)`, the runner `g·c` reads `⌊ck/n⌋ + (ck mod n)/n`. -/
theorem reading_meeting (g n c k : ℕ) (hg : 0 < g) (hn : 0 < n) :
    ((g * c : ℕ) : ℝ) * ((k : ℝ) / ((g * n : ℕ) : ℝ)) =
      (((c * k / n : ℕ) : ℤ) : ℝ) + ((c * k % n : ℕ) : ℝ) / n := by
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨Q, R, hQ, hR⟩ : ∃ Q R : ℕ, c * k / n = Q ∧ c * k % n = R := ⟨_, _, rfl, rfl⟩
  have h := Nat.div_add_mod (c * k) n
  rw [hQ, hR] at h ⊢
  have hr : (n : ℝ) * Q + R = c * k := by exact_mod_cast h
  push_cast
  calc (g : ℝ) * c * (k / (g * n)) = c * k / n := by field_simp
    _ = (n * Q + R) / n := by rw [hr]
    _ = Q + R / n := by field_simp

/-- At the meeting time `k/D`, the runner `M·D` reads the whole number `M·k`. -/
theorem reading_whole (M D k : ℕ) (hD : 0 < D) :
    ((M * D : ℕ) : ℝ) * ((k : ℝ) / (D : ℝ)) = (((M * k : ℕ) : ℤ) : ℝ) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  push_cast
  field_simp

/-- **The readings at a meeting time.** -/
theorem meeting_of_orbit {v1 v2 v3 v4 D K g n c1 c4 : ℕ} (hv2 : v2 = K * D)
    (hv3 : v3 = (K + 1) * D) (hD : D = g * n) (hc1 : v1 = g * c1) (hc4 : v4 = g * c4)
    (hg : 0 < g) (hn : 0 < n) (k : ℕ) :
    ∃ τ : ℝ, ∃ q1 q2 q3 q4 : ℤ, (v1 : ℝ) * τ = q1 + ((c1 * k % n : ℕ) : ℝ) / n ∧
      (v2 : ℝ) * τ = q2 ∧ (v3 : ℝ) * τ = q3 ∧ (v4 : ℝ) * τ = q4 + ((c4 * k % n : ℕ) : ℝ) / n := by
  subst hv2 hv3 hc1 hc4
  subst hD
  exact ⟨(k : ℝ) / ((g * n : ℕ) : ℝ), _, _, _, _, reading_meeting g n c1 k hg hn,
    reading_whole K (g * n) k (by positivity), reading_whole (K + 1) (g * n) k (by positivity),
    reading_meeting g n c4 k hg hn⟩

/-- **The orbit steps by `(1, e)`**: its `m`-th multiple reads `(m, e·m mod n)`. -/
theorem orbit_step {n c1 c4 k e : ℕ} (hk1 : c1 * k % n = 1) (hk4 : c4 * k % n = e) (m : ℕ)
    (hm : m < n) : c1 * (k * m) % n = m ∧ c4 * (k * m) % n = e * m % n := by
  refine ⟨?_, ?_⟩
  · rw [← mul_assoc, ← Nat.mod_mul_mod, hk1, one_mul, Nat.mod_eq_of_lt hm]
  · rw [← mul_assoc, ← Nat.mod_mul_mod, hk4]

/-- **One-dimensional global isolation.**  If `n ∤ c`, the orbit `j ↦ (c·j mod n)/n` is the grid of
spacing `gcd(c, n)/n ≤ 1/2` (a named unit step: `c·m ≡ gcd(c, n)`), so it meets every window
`[lo, hi] ⊆ [0, 1)` of length `≥ 1/2`, at a named multiple. -/
theorem orbit_window_one {n c : ℕ} (hn : 0 < n) (hc : ¬ n ∣ c) {lo hi : ℝ} (hlo : 0 ≤ lo)
    (hhi : hi < 1) (hlen : 1 / 2 ≤ hi - lo) :
    ∃ j : ℕ, lo ≤ ((c * j % n : ℕ) : ℝ) / n ∧ ((c * j % n : ℕ) : ℝ) / n ≤ hi := by
  set g1 : ℕ := Nat.gcd c n with hg1
  have hg1pos : 0 < g1 := Nat.gcd_pos_of_pos_right _ hn
  have hg1n : g1 ∣ n := Nat.gcd_dvd_right c n
  have hg1lt : g1 < n := by
    rcases lt_or_eq_of_le (Nat.le_of_dvd hn hg1n) with h | h
    · exact h
    · exact absurd (h ▸ Nat.gcd_dvd_left c n) hc
  obtain ⟨r, hr⟩ := hg1n
  have h2g : 2 * g1 ≤ n := by
    rcases (by omega : r = 0 ∨ r = 1 ∨ 2 ≤ r) with rfl | rfl | h
    · omega
    · omega
    · rw [hr]; nlinarith
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_gcd (k := n) (n := c) hg1lt
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hgR : (0 : ℝ) < g1 := by exact_mod_cast hg1pos
  set u : ℕ := ⌈lo * n / g1⌉₊ with hu
  have hu1 : lo * n / g1 ≤ u := Nat.le_ceil _
  have hu2 : (u : ℝ) < lo * n / g1 + 1 := Nat.ceil_lt_add_one (by positivity)
  have e1 : lo * n ≤ u * g1 := by rw [div_le_iff₀ hgR] at hu1; linarith
  have e2 : (u : ℝ) * g1 < lo * n + g1 := by
    have := mul_lt_mul_of_pos_right hu2 hgR
    rw [add_mul, div_mul_cancel₀ _ hgR.ne', one_mul] at this; linarith
  have e3 : 2 * (g1 : ℝ) ≤ n := by exact_mod_cast h2g
  have e5 : (u : ℝ) * g1 ≤ hi * n := by nlinarith
  have hlt : g1 * u < n := by
    have : ((g1 * u : ℕ) : ℝ) < n := by push_cast; nlinarith
    exact_mod_cast this
  refine ⟨m * u, ?_, ?_⟩
  · rw [← mul_assoc, ← Nat.mod_mul_mod, hm, Nat.mod_eq_of_lt hlt, le_div_iff₀ hnR]
    push_cast; linarith
  · rw [← mul_assoc, ← Nat.mod_mul_mod, hm, Nat.mod_eq_of_lt hlt, div_le_iff₀ hnR]
    push_cast; linarith

/-- A reading in `[0, 1)` within `L` forward of `c ∈ [0, 1)`, on a window that may pass `1`. -/
theorem window_wrap (ρ c L : ℝ) (hρ0 : 0 ≤ ρ) (hc1 : c < 1)
    (h : Int.fract (ρ - c) ≤ L) : c ≤ ρ ∨ ρ ≤ c + L - 1 := by
  rcases le_or_gt c ρ with hge | hlt
  · exact Or.inl hge
  · right
    have hin : Int.fract (ρ - c) = ρ - c + 1 := by
      rw [← Int.fract_add_one, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    rw [hin] at h
    linarith

theorem emod_neg_nat {n a : ℕ} (h0 : 0 < a) (h : a ≤ n) : (-(a : ℤ)) % n = n - a := by
  have e : (-(a : ℤ)) = ((n : ℤ) - a) + n * (-1) := by ring
  rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]

theorem mod_of_eq {x n q b : ℕ} (h : x = n * q + b) (hb : b < n) : x % n = b := by
  rw [h, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]

section Orbit

variable {v1 v2 v3 v4 v5 D K g n c1 c4 : ℕ}
  (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3) (h34 : v3 < v4) (h45 : v4 < v5)
  (hsmall : 3 * v1 < v3) (hK : 1 ≤ K) (hv2 : v2 = K * D) (hv3 : v3 = (K + 1) * D)
  (hD : D = g * n) (hc1 : v1 = g * c1) (hc4 : v4 = g * c4) (hg : 0 < g) (hn : 0 < n)
include h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn

/-- **A meeting time on the orbit, inside (59) and (60), is lonely nearby** (`lonely_at_meeting`). -/
theorem lonely_at_orbit (h43 : 3 * v4 < 4 * v3) (k : ℕ)
    (h59a : 1 / 6 - (v1 : ℝ) / (3 * v3) ≤ ((c1 * k % n : ℕ) : ℝ) / n)
    (h59b : ((c1 * k % n : ℕ) : ℝ) / n ≤ 5 / 6 - 5 * (v1 : ℝ) / (6 * v3))
    (h60 : ((c4 * k % n : ℕ) : ℝ) / n ≤ 1 / 2 - (v4 : ℝ) / (3 * v3) ∨
      3 / 2 - 5 * (v4 : ℝ) / (6 * v3) ≤ ((c4 * k % n : ℕ) : ℝ) / n) :
    ∃ t : ℝ, Lonely6 v1 v2 v3 v4 v5 t := by
  obtain ⟨τ, q1, q2, q3, q4, e1, e2, e3, e4⟩ := meeting_of_orbit hv2 hv3 hD hc1 hc4 hg hn k
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h2v2 : v3 ≤ 2 * v2 := by rw [hv2, hv3]; nlinarith
  exact lonely_at_meeting h0 h23 h34 h45 hsmall h2v2 h43 q1 q2 q3 q4 e1 e2 e3 e4
    (by positivity) (by rw [div_lt_one hn']; exact_mod_cast Nat.mod_lt _ hn) h59a h59b h60

/-- **BHK (61), in whole numbers.**  A meeting time whose residues satisfy `n ≤ 6a`, `9a ≤ 5n`
and (`2n ≤ 3b` or `b = 0`) lies inside (59) and (60), so it is lonely nearby. -/
theorem lonely_of_residues (h43 : 3 * v4 < 4 * v3) (k a b : ℕ) (ha : c1 * k % n = a)
    (hb : c4 * k % n = b) (h1 : n ≤ 6 * a) (h2 : 9 * a ≤ 5 * n) (h3 : 2 * n ≤ 3 * b ∨ b = 0) :
    ∃ t : ℝ, Lonely6 v1 v2 v3 v4 v5 t := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have p3 : (0 : ℝ) < v3 := by exact_mod_cast (show 0 < v3 by omega)
  have r1 : (0 : ℝ) < v1 := by exact_mod_cast h0
  have rs : 3 * (v1 : ℝ) < v3 := by exact_mod_cast hsmall
  have r34 : (v3 : ℝ) < v4 := by exact_mod_cast h34
  have r43 : 3 * (v4 : ℝ) < 4 * v3 := by exact_mod_cast h43
  have f1 : 0 ≤ (v1 : ℝ) / (3 * v3) := by positivity
  have f2 : 5 * (v1 : ℝ) / (6 * v3) ≤ 5 / 18 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have f3 : (v4 : ℝ) / (3 * v3) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have f4 : 5 / 6 ≤ 5 * (v4 : ℝ) / (6 * v3) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  refine lonely_at_orbit h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 k ?_ ?_ ?_
  · rw [ha, le_div_iff₀ hn']
    have : (n : ℝ) ≤ 6 * a := by exact_mod_cast h1
    nlinarith
  · rw [ha, div_le_iff₀ hn']
    have : 9 * (a : ℝ) ≤ 5 * n := by exact_mod_cast h2
    nlinarith
  · rw [hb]
    rcases h3 with h | h
    · right
      rw [le_div_iff₀ hn']
      have : 2 * (n : ℝ) ≤ 3 * b := by exact_mod_cast h
      nlinarith
    · left
      rw [h]; simp only [CharP.cast_eq_zero, zero_div]; linarith

/-- **A step `(1, e)` of the orbit and a multiple `m` landing in BHK (61).** -/
theorem lonely_of_step (h43 : 3 * v4 < 4 * v3) {k e : ℕ} (hk1 : c1 * k % n = 1)
    (hk4 : c4 * k % n = e) (m q b : ℕ) (hm : m < n) (hq : e * m = n * q + b) (hb : b < n)
    (h1 : n ≤ 6 * m) (h2 : 9 * m ≤ 5 * n) (h3 : 2 * n ≤ 3 * b ∨ b = 0) :
    ∃ t : ℝ, Lonely6 v1 v2 v3 v4 v5 t := by
  obtain ⟨s1, s4⟩ := orbit_step hk1 hk4 m hm
  exact lonely_of_residues h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 (k * m) m b
    s1 (by rw [s4]; exact mod_of_eq hq hb) h1 h2 h3

/-- **Case 6.1: `n ∣ c₄`** (runner 4 reads `0` at every meeting time).  Then `c₁` is a unit mod
`n`, and the meeting time with `c₁k ≡ ⌈n/6⌉` lands in (61). -/
theorem case_6_1 (h43 : 3 * v4 < 4 * v3) (hn2 : 2 ≤ n)
    (hcop : Nat.gcd n (Nat.gcd c1 c4) = 1) (hdvd : n ∣ c4) :
    ∃ t : ℝ, Lonely6 v1 v2 v3 v4 v5 t := by
  have hg1 : Nat.Coprime c1 n := by
    have h1 : Nat.gcd c1 n ∣ Nat.gcd n (Nat.gcd c1 c4) :=
      Nat.dvd_gcd (Nat.gcd_dvd_right c1 n)
        (Nat.dvd_gcd (Nat.gcd_dvd_left c1 n) ((Nat.gcd_dvd_right c1 n).trans hdvd))
    rw [hcop] at h1
    exact Nat.dvd_one.mp h1
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_of_coprime ((n + 5) / 6) hg1 (by omega)
  obtain ⟨q, rfl⟩ := hdvd
  refine lonely_of_residues h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 k
    ((n + 5) / 6) 0 (by rw [hk]; exact Nat.mod_eq_of_lt (by omega)) ?_ (by omega) (by omega)
    (Or.inr rfl)
  rw [mul_assoc]; exact Nat.mul_mod_right _ _

/-- **Case 6.3: step `(1, −1)`**, `n ≥ 3`: the multiple `⌈n/6⌉`. -/
theorem case_6_3 (h43 : 3 * v4 < 4 * v3) (hn3 : 3 ≤ n) {k : ℕ} (hk1 : c1 * k % n = 1)
    (hk4 : c4 * k % n = n - 1) : ∃ t : ℝ, Lonely6 v1 v2 v3 v4 v5 t := by
  refine lonely_of_step h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 hk1 hk4
    ((n + 5) / 6) ((n + 5) / 6 - 1) (n - (n + 5) / 6) (by omega) ?_ (by omega) (by omega)
    (by omega) (by omega)
  have h1 : 1 ≤ (n + 5) / 6 := by omega
  have h2 : (n + 5) / 6 ≤ n := by omega
  zify [h1, h2, (show 1 ≤ n by omega)]
  ring

/-- **Case 6.4: step `(1, 2)`**, `n ≥ 4`: the multiple `⌈n/3⌉`. -/
theorem case_6_4 (h43 : 3 * v4 < 4 * v3) (hn4 : 4 ≤ n) {k : ℕ} (hk1 : c1 * k % n = 1)
    (hk4 : c4 * k % n = 2) : ∃ t : ℝ, Lonely6 v1 v2 v3 v4 v5 t := by
  rcases (by omega : 2 * ((n + 2) / 3) < n ∨ 2 * ((n + 2) / 3) = n) with h | h
  · exact lonely_of_step h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 hk1 hk4
      ((n + 2) / 3) 0 (2 * ((n + 2) / 3)) (by omega) (by ring) h (by omega) (by omega) (by omega)
  · exact lonely_of_step h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 hk1 hk4
      ((n + 2) / 3) 1 0 (by omega) (by rw [mul_one, add_zero, h]) (by omega) (by omega)
      (by omega) (by omega)

/-- **Case 6.5: step `(1, −2)`**, `n ≥ 4`, `n` even or `n ≥ 9`: the multiple `⌈n/2⌉`. -/
theorem case_6_5 (h43 : 3 * v4 < 4 * v3) (hn4 : 4 ≤ n) (hn' : n % 2 = 0 ∨ 9 ≤ n) {k : ℕ}
    (hk1 : c1 * k % n = 1) (hk4 : c4 * k % n = n - 2) : ∃ t : ℝ, Lonely6 v1 v2 v3 v4 v5 t := by
  obtain ⟨m, hm⟩ : ∃ m, m = (n + 1) / 2 := ⟨_, rfl⟩
  rcases (by omega : n = 2 * m ∨ n + 1 = 2 * m) with h | h
  · refine lonely_of_step h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 hk1 hk4
      m (m - 1) 0 (by omega) ?_ (by omega) (by omega) (by omega) (Or.inr rfl)
    subst h
    have h1 : 1 ≤ m := by omega
    have h2 : 2 ≤ 2 * m := by omega
    zify [h1, h2]
    ring
  · refine lonely_of_step h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 hk1 hk4
      m (m - 2) (n - 1) (by omega) ?_ (by omega) (by omega) (by omega) (by omega)
    have hn2 : n = 2 * m - 1 := by omega
    subst hn2
    have h1 : 2 ≤ m := by omega
    have h2 : 2 ≤ 2 * m - 1 := by omega
    have h3 : 1 ≤ 2 * m := by omega
    have h4 : 1 ≤ 2 * m - 1 := by omega
    zify [h1, h2, h3, h4]
    ring

/-- **The step `(1, 3)`**, `n ≥ 6`: the multiple `⌊n/3⌋`. -/
theorem case_6_6a (h43 : 3 * v4 < 4 * v3) (hn6 : 6 ≤ n) {k : ℕ} (hk1 : c1 * k % n = 1)
    (hk4 : c4 * k % n = 3) : ∃ t : ℝ, Lonely6 v1 v2 v3 v4 v5 t := by
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h
  · exact lonely_of_step h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 hk1 hk4
      (n / 3) 1 0 (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inr rfl)
  · exact lonely_of_step h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 hk1 hk4
      (n / 3) 0 (n - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · exact lonely_of_step h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 hk1 hk4
      (n / 3) 0 (n - 2) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- **The step `(1, −3)`**, `n ≥ 6`: the multiple `⌈n/3⌉`. -/
theorem case_6_6b (h43 : 3 * v4 < 4 * v3) (hn6 : 6 ≤ n) {k : ℕ} (hk1 : c1 * k % n = 1)
    (hk4 : c4 * k % n = n - 3) : ∃ t : ℝ, Lonely6 v1 v2 v3 v4 v5 t := by
  obtain ⟨r, s, hr, hs⟩ : ∃ r s, n = 3 * r + s ∧ s < 3 := ⟨n / 3, n % 3, by omega, by omega⟩
  have hr1 : 2 ≤ r := by omega
  rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2) with rfl | rfl | rfl
  · refine lonely_of_step h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 hk1 hk4
      r (r - 1) 0 (by omega) ?_ (by omega) (by omega) (by omega) (Or.inr rfl)
    subst hr
    have h1 : 1 ≤ r := by omega
    have h2 : 3 ≤ 3 * r + 0 := by omega
    zify [h1, h2]
    ring
  · refine lonely_of_step h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 hk1 hk4
      (r + 1) (r - 1) (n - 2) (by omega) ?_ (by omega) (by omega) (by omega) (by omega)
    subst hr
    have h1 : 1 ≤ r := by omega
    have h2 : 3 ≤ 3 * r + 1 := by omega
    have h3 : 2 ≤ 3 * r + 1 := by omega
    zify [h1, h2, h3]
    ring
  · refine lonely_of_step h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 hk1 hk4
      (r + 1) (r - 1) (n - 1) (by omega) ?_ (by omega) (by omega) (by omega) (by omega)
    subst hr
    have h1 : 1 ≤ r := by omega
    have h2 : 3 ≤ 3 * r + 2 := by omega
    have h3 : 1 ≤ 3 * r + 2 := by omega
    zify [h1, h2, h3]
    ring

/-- **Case 6.5.1: step `(1, −2)`, `n = 5`** (BHK p. 43).  The orbit is `(1,3), (2,1), (3,4), (4,2)`
(fifths).  The meeting time at `(1/5, 3/5)` is inside (59), (60) when `27v₃ ≤ 25v₄`; the one at
`(3/5, 4/5)` when `25v₁ ≤ 7v₃`; otherwise (62), (63) hold and the chain `s651_kernel` names the
lonely instant. -/
theorem case_6_5_1 (h43 : 3 * v4 < 4 * v3) (hn5 : n = 5) {k : ℕ} (hk1 : c1 * k % n = 1)
    (hk4 : c4 * k % n = 3) : ∃ t : ℝ, Lonely6 v1 v2 v3 v4 v5 t := by
  have p3 : (0 : ℝ) < v3 := by exact_mod_cast (show 0 < v3 by omega)
  have r1 : (0 : ℝ) < v1 := by exact_mod_cast h0
  have rs : 3 * (v1 : ℝ) < v3 := by exact_mod_cast hsmall
  have r34 : (v3 : ℝ) < v4 := by exact_mod_cast h34
  have f1 : 0 ≤ (v1 : ℝ) / (3 * v3) := by positivity
  have f2 : 5 * (v1 : ℝ) / (6 * v3) ≤ 5 / 18 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have f4 : 5 / 6 ≤ 5 * (v4 : ℝ) / (6 * v3) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  by_cases h62 : 27 * v3 ≤ 25 * v4
  · -- the meeting time at `(1/5, 3/5)`
    have r62 : 27 * (v3 : ℝ) ≤ 25 * v4 := by exact_mod_cast h62
    refine lonely_at_orbit h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 k ?_ ?_ ?_
    · rw [hk1, hn5]; norm_num; linarith
    · rw [hk1, hn5]; norm_num; linarith
    · right; rw [hk4, hn5]
      have : 9 / 10 ≤ 5 * (v4 : ℝ) / (6 * v3) := by rw [le_div_iff₀ (by positivity)]; linarith
      norm_num; linarith
  by_cases h63 : 25 * v1 ≤ 7 * v3
  · -- the meeting time at `(3/5, 4/5)`
    have r63 : 25 * (v1 : ℝ) ≤ 7 * v3 := by exact_mod_cast h63
    obtain ⟨s1, s4⟩ := orbit_step hk1 hk4 3 (by omega)
    refine lonely_at_orbit h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 (k * 3) ?_ ?_ ?_
    · rw [s1, hn5]; norm_num; linarith
    · have : 5 * (v1 : ℝ) / (6 * v3) ≤ 7 / 30 := by rw [div_le_iff₀ (by positivity)]; linarith
      rw [s1, hn5]; norm_num; linarith
    · right; rw [s4, hn5]; norm_num; linarith
  -- (62) and (63): the chain
  push Not at h62 h63
  have h2v2 : v3 ≤ 2 * v2 := by rw [hv2, hv3]; nlinarith
  obtain ⟨t, -, ht⟩ := s651_kernel h0 h12 h23 h34 h45 hsmall h2v2 h62 h63
  exact ⟨t, ht⟩

/-- **Case 6.5.2: step `(1, −2)`, `n = 7`** (BHK p. 43).  The meeting time at `(1/7, 5/7)` is inside
(59), (60) when `v₃ ≤ 14v₁`, the one at `(4/7, 6/7)` otherwise. -/
theorem case_6_5_2 (h43 : 3 * v4 < 4 * v3) (hn7 : n = 7) {k : ℕ} (hk1 : c1 * k % n = 1)
    (hk4 : c4 * k % n = 5) : ∃ t : ℝ, Lonely6 v1 v2 v3 v4 v5 t := by
  have p3 : (0 : ℝ) < v3 := by exact_mod_cast (show 0 < v3 by omega)
  have r1 : (0 : ℝ) < v1 := by exact_mod_cast h0
  have rs : 3 * (v1 : ℝ) < v3 := by exact_mod_cast hsmall
  have r34 : (v3 : ℝ) < v4 := by exact_mod_cast h34
  have f1 : 0 ≤ (v1 : ℝ) / (3 * v3) := by positivity
  have f2 : 5 * (v1 : ℝ) / (6 * v3) ≤ 5 / 18 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have f4 : 5 / 6 ≤ 5 * (v4 : ℝ) / (6 * v3) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  by_cases h14 : v3 ≤ 14 * v1
  · -- the meeting time at `(1/7, 5/7)`
    have r14 : (v3 : ℝ) ≤ 14 * v1 := by exact_mod_cast h14
    have : 1 / 42 ≤ (v1 : ℝ) / (3 * v3) := by rw [le_div_iff₀ (by positivity)]; linarith
    refine lonely_at_orbit h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 k ?_ ?_ ?_
    · rw [hk1, hn7]; norm_num; linarith
    · rw [hk1, hn7]; norm_num; linarith
    · right; rw [hk4, hn7]; norm_num; linarith
  · -- the meeting time at `(4/7, 6/7)`
    push Not at h14
    have r14 : 14 * (v1 : ℝ) < v3 := by exact_mod_cast h14
    have : 5 * (v1 : ℝ) / (6 * v3) ≤ 5 / 84 := by rw [div_le_iff₀ (by positivity)]; linarith
    obtain ⟨s1, s4⟩ := orbit_step hk1 hk4 4 (by omega)
    refine lonely_at_orbit h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 (k * 4) ?_ ?_ ?_
    · rw [s1, hn7]; norm_num; linarith
    · rw [s1, hn7]; norm_num; linarith
    · right; rw [s4, hn7]; norm_num; linarith

set_option maxHeartbeats 1000000 in
-- many window readings (`clear_after`, `linarith`) in one declaration
/-- **Case 6.2: step `(1, 1)`** (BHK pp. 41–43).  Runners 1 and 4 read alike at every meeting time.
The meeting time with reading `⌈n/3⌉/n ∈ [1/3, 1/2]` carries the windows of §6.2.1 (`K = 1`, where
also `v₄ = v₁ + v₃`) and §6.2.2 (`K ≥ 2`); in §6.2.2 with `n ≥ 3` the meeting time with reading
`⌈n/6⌉/n ∈ [1/6, 1/3]` carries the last window. -/
theorem case_6_2 (h43 : 3 * v4 < 4 * v3) (hn2 : 2 ≤ n) {k : ℕ} (hk1 : c1 * k % n = 1)
    (hk4 : c4 * k % n = 1) : ∃ t : ℝ, Lonely6 v1 v2 v3 v4 v5 t := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- the γ-meeting time
  obtain ⟨s1, s4⟩ := orbit_step hk1 hk4 ((n + 2) / 3) (by omega)
  rw [one_mul, Nat.mod_eq_of_lt (show (n + 2) / 3 < n by omega)] at s4
  obtain ⟨τ, q1, q2, q3, q4, e1, e2, e3, e4⟩ := meeting_of_orbit hv2 hv3 hD hc1 hc4 hg hn
    (k * ((n + 2) / 3))
  rw [s1] at e1
  rw [s4] at e4
  have hρ1 : 1 / 3 ≤ (((n + 2) / 3 : ℕ) : ℝ) / n := by
    rw [le_div_iff₀ hn']
    have : (n : ℝ) ≤ 3 * (((n + 2) / 3 : ℕ) : ℝ) := by exact_mod_cast (show n ≤ 3 * ((n + 2) / 3) by omega)
    linarith
  have hρ2 : (((n + 2) / 3 : ℕ) : ℝ) / n ≤ 1 / 2 := by
    rw [div_le_iff₀ hn']
    have : 2 * (((n + 2) / 3 : ℕ) : ℝ) ≤ n := by exact_mod_cast (show 2 * ((n + 2) / 3) ≤ n by omega)
    linarith
  rcases (by omega : K = 1 ∨ 2 ≤ K) with rfl | hK2
  · -- §6.2.1: `v₃ = 2v₂`
    have h32 : v3 = 2 * v2 := by rw [hv2, hv3]; ring
    -- `c₁ ≡ c₄ (mod n)`, so `D ∣ v₄ − v₁`, and the bounds give `v₄ = v₁ + v₃`
    have hmod : c1 % n = c4 % n := by
      have A : c1 * (c4 * k) % n = c1 % n := by rw [Nat.mul_mod, hk4, mul_one, Nat.mod_mod]
      have B : c4 * (c1 * k) % n = c4 % n := by rw [Nat.mul_mod, hk1, mul_one, Nat.mod_mod]
      rw [← A, ← B, show c1 * (c4 * k) = c4 * (c1 * k) by ring]
    obtain ⟨m, hm⟩ := (show c1 ≡ c4 [MOD n] from hmod).dvd
    have zD : (0 : ℤ) < D := by exact_mod_cast (show 0 < D by rw [hD]; positivity)
    have hdiff : (v4 : ℤ) - v1 = D * m := by
      rw [hc4, hc1, hD]; push_cast
      rw [show (g : ℤ) * c4 - g * c1 = g * (c4 - c1) by ring, hm]; ring
    have z3 : (v3 : ℤ) = 2 * D := by rw [hv3]; push_cast; ring
    have zs : 3 * (v1 : ℤ) < v3 := by exact_mod_cast hsmall
    have z34 : (v3 : ℤ) < v4 := by exact_mod_cast h34
    have z43 : 3 * (v4 : ℤ) < 4 * v3 := by exact_mod_cast h43
    have z1 : (0 : ℤ) < v1 := by exact_mod_cast h0
    have hm2 : m = 2 := by
      rcases lt_trichotomy m 2 with h | h | h
      · have : (D : ℤ) * m ≤ D * 1 := mul_le_mul_of_nonneg_left (by omega) zD.le
        nlinarith
      · exact h
      · have : (D : ℤ) * 3 ≤ D * m := mul_le_mul_of_nonneg_left (by omega) zD.le
        nlinarith
    subst hm2
    have h41 : v4 = v1 + v3 := by
      have : (v4 : ℤ) = v1 + v3 := by linarith
      exact_mod_cast this
    rcases s621_x1 h0 h12 h23 h34 h45 hsmall h32 h41 h43 with ⟨t, -, ht⟩ | hx1
    · exact ⟨t, ht⟩
    have h74 : 7 * v4 < 8 * v3 := by omega
    rcases s621_x5 h0 h23 h34 h45 h32 hx1 h74 q1 q2 q3 q4 e1 e2 e3 e4 hρ1 hρ2 with h | hx5
    · exact h
    exact s621_kernel h0 h23 h34 h45 h32 hx1 h74 hx5 q1 q2 q3 q4 e1 e2 e3 e4 hρ1 hρ2
  · -- §6.2.2: `2v₃ ≤ 3v₂`
    have h32 : 2 * v3 ≤ 3 * v2 := by rw [hv2, hv3]; nlinarith
    rcases s622_flank h0 h23 h34 h45 hsmall h32 h43 q1 q2 q3 q4 e1 e2 e3 e4 hρ1 hρ2 with h | h54
    · exact h
    rcases (by omega : n = 2 ∨ 3 ≤ n) with hn2' | hn3
    · -- `n = 2`: the γ-meeting time reads `1/2`
      subst hn2'
      norm_num at e1 e4
      exact s622_final_half h0 h23 h34 h54 hsmall h32 h43 q1 q2 q3 q4 e1 e2 e3 e4
    · -- `n ≥ 3`: the β-meeting time, reading `⌈n/6⌉/n ∈ [1/6, 1/3]`
      obtain ⟨t1, t4⟩ := orbit_step hk1 hk4 ((n + 5) / 6) (by omega)
      rw [one_mul, Nat.mod_eq_of_lt (show (n + 5) / 6 < n by omega)] at t4
      obtain ⟨τ', r1, r2, r3, r4, f1, f2, f3, f4⟩ := meeting_of_orbit hv2 hv3 hD hc1 hc4 hg hn
        (k * ((n + 5) / 6))
      rw [t1] at f1
      rw [t4] at f4
      refine s622_final h0 h23 h34 h54 hsmall h32 h43 r1 r2 r3 r4 f1 f2 f3 f4 ?_ ?_
      · rw [le_div_iff₀ hn']
        have : (n : ℝ) ≤ 6 * (((n + 5) / 6 : ℕ) : ℝ) := by
          exact_mod_cast (show n ≤ 6 * ((n + 5) / 6) by omega)
        linarith
      · rw [div_le_iff₀ hn']
        have : 3 * (((n + 5) / 6 : ℕ) : ℝ) ≤ n := by
          exact_mod_cast (show 3 * ((n + 5) / 6) ≤ n by omega)
        linarith

set_option maxHeartbeats 2000000 in
-- many window readings (`clear_after`, `linarith`) in one declaration
/-- **§6 with `3v₄ < 4v₃`: global isolation in two dimensions.**  With `gcd(n, c₁, c₄) = 1` and
`n ∤ c₁`, read the orbit `k ↦ ((c₁k) % n, (c₄k) % n)` of meeting times against BHK's box
`R = [1/6 − v₁/(3v₃), 5/6 − 5v₁/(6v₃)] × [3/2 − 5v₄/(6v₃), 3/2 − v₄/(3v₃)]` (width `α > 1/2`, height
`β > 1/2`).  Either the orbit meets it (`orbit_isolation_two`; for `n ≤ 3` by hand), and that
meeting time is lonely nearby (`lonely_at_orbit`), or the orbit has a short step `(1, e)`, `|e| ≤ 3`,
and the cases 6.1–6.5 and `(1, ±3)` name the lonely instant. -/
theorem lonely_6_narrow (h43 : 3 * v4 < 4 * v3) (hcop : Nat.gcd n (Nat.gcd c1 c4) = 1)
    (hnc1 : ¬ n ∣ c1) : ∃ t : ℝ, Lonely6 v1 v2 v3 v4 v5 t := by
  have hn2 : 2 ≤ n := by
    by_contra h
    exact hnc1 (by rw [show n = 1 by omega]; exact one_dvd _)
  by_cases h61 : n ∣ c4
  · exact case_6_1 h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 hn2 hcop h61
  have hc1m : c1 % n ≠ 0 := fun h => hnc1 (Nat.dvd_of_mod_eq_zero h)
  have hc4m : c4 % n ≠ 0 := fun h => h61 (Nat.dvd_of_mod_eq_zero h)
  rcases (by omega : n = 2 ∨ n = 3 ∨ 4 ≤ n) with hn' | hn' | hn4
  · -- `n = 2`: the step `(1, 1)`
    exact case_6_2 h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 hn2 (k := 1)
      (by rw [hn'] at hc1m ⊢; omega) (by rw [hn'] at hc4m ⊢; omega)
  · -- `n = 3`: the step `(1, 1)` or `(1, −1)`
    rw [hn'] at hc1m hc4m
    rcases (by omega : c1 % 3 = 1 ∨ c1 % 3 = 2) with ha | ha <;>
      rcases (by omega : c4 % 3 = 1 ∨ c4 % 3 = 2) with hb | hb
    · exact case_6_2 h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 hn2 (k := 1)
        (by rw [hn']; omega) (by rw [hn']; omega)
    · exact case_6_3 h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 (by omega) (k := 1)
        (by rw [hn']; omega) (by rw [hn']; omega)
    · exact case_6_3 h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 (by omega) (k := 2)
        (by rw [hn']; omega) (by rw [hn']; omega)
    · exact case_6_2 h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 hn2 (k := 2)
        (by rw [hn']; omega) (by rw [hn']; omega)
  -- `n ≥ 4`: two-dimensional global isolation
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h4R : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have p3 : (0 : ℝ) < v3 := by exact_mod_cast (show 0 < v3 by omega)
  have r1 : (0 : ℝ) < v1 := by exact_mod_cast h0
  have rs : 3 * (v1 : ℝ) < v3 := by exact_mod_cast hsmall
  have r34 : (v3 : ℝ) < v4 := by exact_mod_cast h34
  have r43 : 3 * (v4 : ℝ) < 4 * v3 := by exact_mod_cast h43
  have f1 : (v1 : ℝ) / (2 * v3) < 1 / 6 := by rw [div_lt_iff₀ (by positivity)]; linarith
  have f1' : 0 < (v1 : ℝ) / (2 * v3) := by positivity
  have f4 : 1 / 2 < (v4 : ℝ) / (2 * v3) := by rw [lt_div_iff₀ (by positivity)]; linarith
  have f4' : (v4 : ℝ) / (2 * v3) < 2 / 3 := by rw [div_lt_iff₀ (by positivity)]; linarith
  set α : ℝ := 2 / 3 - (v1 : ℝ) / (2 * v3) with hα
  set β : ℝ := (v4 : ℝ) / (2 * v3) with hβ
  have hα1 : 1 / 2 < α := by rw [hα]; linarith
  have hα2 : α < 1 := by rw [hα]; linarith
  have hαβ : 1 ≤ α * β * n := by
    have h1 : 1 / 4 < α * β := by nlinarith [mul_pos (sub_pos.2 hα1) (sub_pos.2 f4)]
    have h2 : α * β * 4 ≤ α * β * n := mul_le_mul_of_nonneg_left h4R (by linarith)
    linarith
  rcases orbit_isolation_two n c1 c4 (by omega) hcop α β (by linarith) hα2 (by linarith)
      (by linarith) hαβ with hall | ⟨i, j, hne, hon, hi0, hi1, -, -, hc1', hc2', -, -⟩
  · -- the orbit meets the box: a meeting time inside (59) and (60)
    obtain ⟨k, -, hu, hv⟩ := hall (1 / 6 - (v1 : ℝ) / (3 * v3)) (3 / 2 - 5 * (v4 : ℝ) / (6 * v3))
    have hread : ∀ c : ℕ, 0 ≤ ((c * k % n : ℕ) : ℝ) / n ∧ ((c * k % n : ℕ) : ℝ) / n < 1 :=
      fun c => ⟨by positivity, by rw [div_lt_one hnR]; exact_mod_cast Nat.mod_lt _ hn⟩
    have g1 : (v1 : ℝ) / (3 * v3) < 1 / 9 := by rw [div_lt_iff₀ (by positivity)]; linarith
    have g1' : 0 < (v1 : ℝ) / (3 * v3) := by positivity
    have g2 : 5 / 6 < 5 * (v4 : ℝ) / (6 * v3) := by rw [lt_div_iff₀ (by positivity)]; linarith
    have g2' : 5 * (v4 : ℝ) / (6 * v3) < 10 / 9 := by rw [div_lt_iff₀ (by positivity)]; linarith
    have e1 : (1 / 6 - (v1 : ℝ) / (3 * v3)) + α = 5 / 6 - 5 * (v1 : ℝ) / (6 * v3) := by
      rw [hα]; ring
    have e2 : (3 / 2 - 5 * (v4 : ℝ) / (6 * v3)) + β - 1 = 1 / 2 - (v4 : ℝ) / (3 * v3) := by
      rw [hβ]; ring
    obtain ⟨w1, w2⟩ := window_of_fract _ _ _ (hread c1).1 (hread c1).2 (by linarith)
      (by rw [e1]; linarith) hu
    have w3 := window_wrap _ _ _ (hread c4).1 (by linarith) hv
    refine lonely_at_orbit h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 k w1
      (by rw [← e1]; exact w2) ?_
    rcases w3 with h | h
    · exact Or.inr h
    · exact Or.inl (by rw [← e2]; exact h)
  -- the short step `(i, j)`: `i ∈ {0, 1}`, `|j| ≤ 3`
  obtain ⟨k, -, hik, hjk⟩ := hon
  have hiM : i ≡ (c1 : ℤ) * k [ZMOD n] := by
    unfold Int.ModEq; rw [hik]; push_cast; rfl
  have hjM : j ≡ (c4 : ℤ) * k [ZMOD n] := by
    unfold Int.ModEq; rw [hjk]; push_cast; rfl
  have hβi : 1 / β < 2 := by rw [div_lt_iff₀ (by linarith)]; linarith
  have hαi : 1 / α < 2 := by rw [div_lt_iff₀ (by linarith)]; linarith
  have hβα : β / α < 4 / 3 := by rw [div_lt_iff₀ (by linarith)]; linarith
  have hβα0 : 0 ≤ β / α := by positivity
  have hi2 : i < 2 := by
    have : (i : ℝ) < 2 := by linarith
    exact_mod_cast this
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · -- `i = 0`: then `j = ±1` and `n ∣ c₁`, which is excluded
    exfalso
    push_cast at hc1' hc2'
    have hj1 : j < 2 := by
      have : (j : ℝ) < 2 := by linarith
      exact_mod_cast this
    have hj2 : -2 < j := by
      have : (-2 : ℝ) < j := by
        have : -1 / α = -(1 / α) := by ring
        linarith
      exact_mod_cast this
    have hj0 : j ≠ 0 := by rintro rfl; exact hne rfl
    have H : (c1 : ℤ) * j ≡ 0 [ZMOD n] := by
      calc (c1 : ℤ) * j ≡ c1 * (c4 * k) [ZMOD n] := hjM.mul_left _
        _ = c4 * (c1 * k) := by ring
        _ ≡ c4 * 0 [ZMOD n] := hiM.symm.mul_left _
        _ = 0 := by ring
    have H2 : (n : ℤ) ∣ c1 := by
      have := (Int.modEq_zero_iff_dvd.mp H)
      rcases (by omega : j = 1 ∨ j = -1) with rfl | rfl
      · simpa using this
      · simpa using this
    exact hnc1 (Int.natCast_dvd_natCast.mp H2)
  -- `i = 1`
  push_cast at hc1' hc2'
  have hj1 : j ≤ 3 := by
    have : (j : ℝ) < 4 := by linarith
    have : j < 4 := by exact_mod_cast this
    omega
  have hj2 : -3 ≤ j := by
    have : (-4 : ℝ) < j := by
      have : -1 / α = -(1 / α) := by ring
      linarith
    have : -4 < j := by exact_mod_cast this
    omega
  have hk1 : c1 * k % n = 1 := by
    have h1 : ((c1 * k % n : ℕ) : ℤ) = 1 := by
      rw [← hik]; exact Int.emod_eq_of_lt (by norm_num) (by omega)
    exact_mod_cast h1
  interval_cases j
  · -- `j = −3`
    rw [show (-3 : ℤ) = -((3 : ℕ) : ℤ) by norm_num, emod_neg_nat (by norm_num) (by omega)] at hjk
    rcases (by omega : n = 4 ∨ n = 5 ∨ 6 ≤ n) with hn' | hn' | hn6
    · exact case_6_2 h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 hn2 hk1 (by omega)
    · exact case_6_4 h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 hn4 hk1 (by omega)
    · exact case_6_6b h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 hn6 hk1 (by omega)
  · -- `j = −2`
    rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, emod_neg_nat (by norm_num) (by omega)] at hjk
    rcases (by omega : n = 5 ∨ n = 7 ∨ (n % 2 = 0 ∨ 9 ≤ n)) with hn' | hn' | hn''
    · exact case_6_5_1 h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 hn' hk1 (by omega)
    · exact case_6_5_2 h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 hn' hk1 (by omega)
    · exact case_6_5 h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 hn4 hn'' hk1
        (by omega)
  · -- `j = −1`
    rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by norm_num, emod_neg_nat (by norm_num) (by omega)] at hjk
    exact case_6_3 h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 (by omega) hk1
      (by omega)
  · -- `j = 0`: then `n ∣ c₄`, which is excluded
    exfalso
    have H : (c4 : ℤ) ≡ 0 [ZMOD n] := by
      calc (c4 : ℤ) = c4 * 1 := by ring
        _ ≡ c4 * (c1 * k) [ZMOD n] := hiM.mul_left _
        _ = c1 * (c4 * k) := by ring
        _ ≡ c1 * 0 [ZMOD n] := hjM.symm.mul_left _
        _ = 0 := by ring
    exact h61 (Int.natCast_dvd_natCast.mp (Int.modEq_zero_iff_dvd.mp H))
  · -- `j = 1`
    rw [Int.emod_eq_of_lt (by norm_num) (by omega)] at hjk
    exact case_6_2 h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 hn2 hk1 (by omega)
  · -- `j = 2`
    rw [Int.emod_eq_of_lt (by norm_num) (by omega)] at hjk
    exact case_6_4 h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 hn4 hk1 (by omega)
  · -- `j = 3`
    rw [Int.emod_eq_of_lt (by norm_num) (by omega)] at hjk
    rcases (by omega : n = 4 ∨ n = 5 ∨ 6 ≤ n) with hn' | hn' | hn6
    · exact case_6_3 h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 (by omega) hk1
        (by omega)
    · exact case_6_5_1 h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 hn' hk1 (by omega)
    · exact case_6_6a h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn h43 hn6 hk1 (by omega)

end Orbit

/-! ## 5. BHK §6 assembled -/

set_option maxHeartbeats 1000000 in
-- many window readings (`clear_after`, `linarith`) in one declaration
/-- **BHK §6 in the framework** (`D = v₃ − v₂` divides `v₃`, `D ∤ v₁`, `3v₁ < v₃`): five
whole-number disparities are lonely at `1/6`, at a named instant.  Runners 2 and 3 meet at the
origin at the times `k/D`; the orbit of these meeting times, read by runners 1 and 4, is the
one- and two-dimensional global isolation of `GlobalIsolationTwoN`, and each meeting time it
selects carries a window (the two-flank rule, R6 at the half lap, or a flank opening) with the
lonely instant named. -/
theorem lonely_6 {v1 v2 v3 v4 v5 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3)
    (h34 : v3 < v4) (h45 : v4 < v5) (hsmall : 3 * v1 < v3) (hDv3 : (v3 - v2) ∣ v3)
    (hDv1 : ¬ (v3 - v2) ∣ v1) : ∃ t : ℝ, 0 < t ∧ Lonely6 v1 v2 v3 v4 v5 t := by
  set D : ℕ := v3 - v2 with hDdef
  have hDpos : 0 < D := by omega
  -- `v₃ = (K + 1)·D`, `v₂ = K·D`, `K ≥ 1`
  obtain ⟨M, hM⟩ := hDv3
  have hM2 : 2 ≤ M := by
    rcases (by omega : M = 0 ∨ M = 1 ∨ 2 ≤ M) with rfl | rfl | h
    · omega
    · omega
    · exact h
  set K : ℕ := M - 1 with hKdef
  have hK : 1 ≤ K := by omega
  have hv3 : v3 = (K + 1) * D := by rw [hM, show K + 1 = M by omega, mul_comm]
  have hv2 : v2 = K * D := by
    have : v2 = v3 - D := by omega
    rw [this, hv3]
    rw [show (K + 1) * D = K * D + D by ring]
    omega
  -- `g = gcd(D, v₁, v₄)`, `D = g·n`, `v₁ = g·c₁`, `v₄ = g·c₄`
  set g : ℕ := Nat.gcd D (Nat.gcd v1 v4) with hgdef
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hDpos
  obtain ⟨n, hD⟩ : g ∣ D := Nat.gcd_dvd_left _ _
  obtain ⟨c1, hc1⟩ : g ∣ v1 := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  obtain ⟨c4, hc4⟩ : g ∣ v4 := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, mul_zero] at hD; omega
    · exact h
  have hcop : Nat.gcd n (Nat.gcd c1 c4) = 1 := by
    have key : g = g * Nat.gcd n (Nat.gcd c1 c4) := by
      conv_lhs => rw [hgdef, hD, hc1, hc4]
      rw [Nat.gcd_mul_left, Nat.gcd_mul_left]
    have := Nat.eq_of_mul_eq_mul_left hg (show g * 1 = g * Nat.gcd n (Nat.gcd c1 c4) by
      rw [mul_one]; exact key)
    exact this.symm
  have hnc1 : ¬ n ∣ c1 := by
    rintro ⟨q, hq⟩
    exact hDv1 ⟨q, by rw [hc1, hq, hD]; ring⟩
  -- a lonely instant at all, then a positive one
  suffices h : ∃ t : ℝ, Lonely6 v1 v2 v3 v4 v5 t by
    obtain ⟨t, ht⟩ := h
    exact lonely6_pos ht
  have p3 : (0 : ℝ) < v3 := by exact_mod_cast (show 0 < v3 by omega)
  have rs : 3 * (v1 : ℝ) < v3 := by exact_mod_cast hsmall
  have r1 : (0 : ℝ) < v1 := by exact_mod_cast h0
  by_cases hwide : 4 * v3 ≤ 3 * v4
  · -- BHK's reduction: a meeting time inside (59), found by one-dimensional isolation
    have g1 : (v1 : ℝ) / (3 * v3) < 1 / 9 := by rw [div_lt_iff₀ (by positivity)]; linarith
    have g2 : 5 * (v1 : ℝ) / (6 * v3) - (v1 : ℝ) / (3 * v3) = (v1 : ℝ) / (2 * v3) := by ring
    have g3 : (v1 : ℝ) / (2 * v3) ≤ 1 / 6 := by rw [div_le_iff₀ (by positivity)]; linarith
    have g4 : 0 < 5 * (v1 : ℝ) / (6 * v3) := by positivity
    obtain ⟨j, hj1, hj2⟩ := orbit_window_one hn hnc1 (lo := 1 / 6 - (v1 : ℝ) / (3 * v3))
      (hi := 5 / 6 - 5 * (v1 : ℝ) / (6 * v3)) (by linarith) (by linarith) (by linarith)
    obtain ⟨τ, q1, q2, q3, q4, e1, e2, e3, -⟩ := meeting_of_orbit hv2 hv3 hD hc1 hc4 hg hn j
    have h2v2 : v3 ≤ 2 * v2 := by rw [hv2, hv3]; nlinarith
    exact lonely_at_meeting_wide h0 h23 h34 h45 hsmall h2v2 hwide q1 q2 q3 e1 e2 e3 hj1 hj2
  · exact lonely_6_narrow h0 h12 h23 h34 h45 hsmall hK hv2 hv3 hD hc1 hc4 hg hn (by omega) hcop hnc1

end LRC.OrderSixN
