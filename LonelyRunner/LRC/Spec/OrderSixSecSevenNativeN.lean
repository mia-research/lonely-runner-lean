import Mathlib
import LonelyRunner.LRC.Spec.OrderSixN
import LonelyRunner.LRC.Spec.GlobalIsolationTwoN
import LonelyRunner.LRC.Spec.OrderSixEightN

/-!
# BHK §7 natively, from the speeds to a lonely instant

Moved into the tree 2026-10-16 from `experiments/n6_native/S7Complete_v1.lean` (log E56, E58); `lonely_7_native`
replaces `S7.lonely_7` in the order-six dispatch `lonely6_of_lt`.

Combines `WindowTwoRunner_v5.lean` (the two-runner window lemma, the window route, `G₄`/`G₇` closed) and
`S7Orbits_v3.lean` (the main route fails only on `G₄` and `G₇`, every order), and joins them:
`main_route_lonely` (a meeting-time point in BHK's parallelogram gives runner 3's whole clear lap with
runners 1–3 clear, and `window_two_uniform` finds the lonely instant in it) and `s7_lonely` (whole-number
speeds in BHK §7: some instant is lonely).
-/

namespace LRC.S7Native
open LRC.OrderSixN




theorem clear_of_band {z : ℝ} {p : ℤ} (h1 : (p : ℝ) + 1 / 6 ≤ z) (h2 : z ≤ (p : ℝ) + 5 / 6) :
    (6 : ℝ)⁻¹ ≤ circDist z := by
  have hfr : Int.fract z = z - p := by
    rw [Int.fract_eq_iff]; exact ⟨by linarith, by linarith, p, by ring⟩
  unfold circDist; rw [hfr]; exact le_min (by linarith) (by linarith)

theorem blocked_near_int {z : ℝ} (h : ¬ (6 : ℝ)⁻¹ ≤ circDist z) :
    ∃ q : ℤ, (q : ℝ) - 1 / 6 < z ∧ z < (q : ℝ) + 1 / 6 := by
  unfold circDist at h
  have hf0 := Int.fract_nonneg z
  have hf1 := Int.fract_lt_one z
  have hz := Int.floor_add_fract z
  rcases lt_or_ge (Int.fract z) (6⁻¹) with hlt | hge
  · exact ⟨⌊z⌋, by linarith, by norm_num at hlt ⊢; linarith⟩
  · have : 1 - Int.fract z < 6⁻¹ := by
      by_contra hc; push Not at hc; exact h (le_min hge hc)
    refine ⟨⌊z⌋ + 1, ?_, ?_⟩ <;> push_cast <;> norm_num at this ⊢ <;> linarith

/-- `b·x < b·y` with `b > 0` gives `x < y`. -/
theorem lt_of_mul_lt' {b x y : ℝ} (hb : 0 < b) (h : b * x < b * y) : x < y :=
  lt_of_mul_lt_mul_left h hb.le

set_option maxHeartbeats 2000000 in
/-- **The two-runner window lemma.** -/
theorem window_two {a b J₀ ℓ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbase : 1 / (3 * a) + 1 / (3 * b) ≤ ℓ)
    (hres : ∀ m : ℤ, 3 * (m : ℝ) * a < a + b → ((m : ℝ) + 1 / 3) / b ≤ ℓ) :
    ∃ t : ℝ, J₀ ≤ t ∧ t ≤ J₀ + ℓ ∧ (6 : ℝ)⁻¹ ≤ circDist (a * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (b * t) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  -- work in "a-time" A = a·t and "b-time" B = b·t via the quantities u = 1/(3a), v = 1/(3b)
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 1 / (3 * a) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = 1 / (3 * b) := ⟨_, rfl⟩
  have hau : a * u = 1 / 3 := by rw [hu]; field_simp
  have hbv : b * v = 1 / 3 := by rw [hv]; field_simp
  have hu0 : 0 < u := by rw [hu]; positivity
  have hv0 : 0 < v := by rw [hv]; positivity
  have hvu : v ≤ u := by rw [hu, hv]; apply one_div_le_one_div_of_le (by positivity); linarith
  have hbu : b * u ≥ 1 / 3 := by nlinarith
  obtain ⟨p, hp1, hp2⟩ : ∃ p : ℤ, a * J₀ - 5 / 6 ≤ (p : ℝ) ∧ (p : ℝ) < a * J₀ - 5 / 6 + 1 :=
    ⟨⌈a * J₀ - 5 / 6⌉, Int.le_ceil _, Int.ceil_lt_add_one _⟩
  -- t₁: a's first clear point; e: a's exit
  obtain ⟨t₁, ht₁⟩ : ∃ t, a * t = max (a * J₀) ((p : ℝ) + 1 / 6) :=
    ⟨max (a * J₀) ((p : ℝ) + 1 / 6) / a, by field_simp⟩
  obtain ⟨e, he⟩ : ∃ t, a * t = (p : ℝ) + 5 / 6 := ⟨((p : ℝ) + 5 / 6) / a, by field_simp⟩
  have m1 := le_max_left (a * J₀) ((p : ℝ) + 1 / 6)
  have m2 := le_max_right (a * J₀) ((p : ℝ) + 1 / 6)
  have m3 : max (a * J₀) ((p : ℝ) + 1 / 6) < a * J₀ + 1 / 3 := max_lt (by linarith) (by linarith)
  have ht₁J : J₀ ≤ t₁ := by nlinarith
  have ht₁U : t₁ < J₀ + u := lt_of_mul_lt' ha (by rw [mul_add, hau]; linarith)
  have ht₁e : t₁ ≤ e := by
    have : max (a * J₀) ((p : ℝ) + 1 / 6) ≤ (p : ℝ) + 5 / 6 := max_le (by linarith) (by linarith)
    nlinarith
  have hA : ∀ t, t₁ ≤ t → t ≤ e → (6 : ℝ)⁻¹ ≤ circDist (a * t) := fun t h1 h2 =>
    clear_of_band (p := p) (by nlinarith) (by nlinarith)
  by_cases c1 : (6 : ℝ)⁻¹ ≤ circDist (b * t₁)
  · exact ⟨t₁, ht₁J, by linarith, hA t₁ le_rfl ht₁e, c1⟩
  obtain ⟨q, hq1, hq2⟩ := blocked_near_int c1
  obtain ⟨t₂, ht₂⟩ : ∃ t, b * t = (q : ℝ) + 1 / 6 := ⟨((q : ℝ) + 1 / 6) / b, by field_simp⟩
  have ht₂a : t₁ < t₂ := lt_of_mul_lt' hb (by linarith)
  have ht₂b : t₂ < t₁ + v := lt_of_mul_lt' hb (by rw [mul_add, hbv]; linarith)
  have hc5 : (6 : ℝ)⁻¹ ≤ circDist (b * t₂) := by rw [ht₂]; exact clear_of_band (p := q) le_rfl (by linarith)
  by_cases c2 : t₂ ≤ e
  · exact ⟨t₂, by linarith, by linarith, hA t₂ ht₂a.le c2, hc5⟩
  push Not at c2
  -- a started clear: otherwise e - t₁ = 2u > v
  have ht₁eq : t₁ = J₀ := by
    by_contra hne
    have hlt : J₀ < t₁ := lt_of_le_of_ne ht₁J (Ne.symm hne)
    have hmx : max (a * J₀) ((p : ℝ) + 1 / 6) = (p : ℝ) + 1 / 6 := by
      rcases le_total (a * J₀) ((p : ℝ) + 1 / 6) with h | h
      · exact max_eq_right h
      · exfalso; rw [max_eq_left h] at ht₁; nlinarith
    have : a * (e - t₁) = 2 / 3 := by rw [mul_sub, he, ht₁, hmx]; ring
    have : e - t₁ = 2 * u := by nlinarith
    linarith
  obtain ⟨t₃, ht₃⟩ : ∃ t, a * t = (p : ℝ) + 7 / 6 := ⟨((p : ℝ) + 7 / 6) / a, by field_simp⟩
  have ht₃e : t₃ = e + u := by
    have : a * t₃ = a * (e + u) := by rw [mul_add, he, hau, ht₃]; ring
    exact mul_left_cancel₀ ha.ne' this
  by_cases c3 : (6 : ℝ)⁻¹ ≤ circDist (b * t₃)
  · refine ⟨t₃, by linarith, by linarith, ?_, c3⟩
    rw [ht₃]; exact clear_of_band (p := p + 1) (by simp only [Int.cast_add, Int.cast_one]; linarith only [])
      (by simp only [Int.cast_add, Int.cast_one]; linarith only [])
  obtain ⟨q', hq'1, hq'2⟩ := blocked_near_int c3
  obtain ⟨t₄, ht₄⟩ : ∃ t, b * t = (q' : ℝ) + 1 / 6 := ⟨((q' : ℝ) + 1 / 6) / b, by field_simp⟩
  have ht₄a : t₃ < t₄ := lt_of_mul_lt' hb (by linarith)
  have ht₄b : t₄ < t₃ + v := lt_of_mul_lt' hb (by rw [mul_add, hbv]; linarith)
  have hm : b * (t₄ - t₂) = ((q' - q : ℤ) : ℝ) := by rw [mul_sub, ht₄, ht₂]; push_cast; ring
  have hmres : 3 * ((q' - q : ℤ) : ℝ) * a < a + b := by
    -- t₄ - v < t₃ = e + u < t₂ + u, so b(t₄ - t₂) < 1/3 + b u
    have h1 : t₄ - t₂ < v + u := by linarith
    have h2 : b * (t₄ - t₂) < b * v + b * u := by nlinarith
    rw [hm, hbv] at h2
    have h3 : 3 * a * (b * u) = b := by rw [show 3 * a * (b * u) = 3 * b * (a * u) by ring, hau]; ring
    nlinarith
  have hℓ := hres (q' - q) hmres
  have hfin : t₄ < J₀ + (((q' - q : ℤ) : ℝ) + 1 / 3) / b := by
    apply lt_of_mul_lt' hb
    have e2 : b * (J₀ + (((q' - q : ℤ) : ℝ) + 1 / 3) / b) = b * J₀ + ((q' - q : ℤ) : ℝ) + 1 / 3 := by
      field_simp; ring
    rw [e2]
    have : b * t₂ < b * J₀ + 1 / 3 := by
      have := ht₂b; rw [ht₁eq] at this
      have h' : b * t₂ < b * (J₀ + v) := by nlinarith
      rw [mul_add, hbv] at h'; exact h'
    linarith [hm]
  refine ⟨t₄, by linarith, by linarith, ?_, ?_⟩
  · apply clear_of_band (p := p + 1)
    · push_cast; nlinarith
    · push_cast
      have : a * t₄ < a * (t₃ + v) := by nlinarith
      have : a * v ≤ a * u := by nlinarith
      nlinarith
  · rw [ht₄]; exact clear_of_band (p := q') le_rfl (by linarith)

/-- **Uniform form.** A window of length `2/(3a)` always suffices (`L(ρ) ≤ 2/3` in runner-`a` laps). -/
theorem window_two_uniform {a b J₀ ℓ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hℓ : 2 / (3 * a) ≤ ℓ) :
    ∃ t : ℝ, J₀ ≤ t ∧ t ≤ J₀ + ℓ ∧ (6 : ℝ)⁻¹ ≤ circDist (a * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (b * t) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  apply window_two ha hab
  · have : 1 / (3 * b) ≤ 1 / (3 * a) := one_div_le_one_div_of_le (by positivity) (by linarith)
    have e : 2 / (3 * a) = 1 / (3 * a) + 1 / (3 * a) := by ring
    linarith
  · intro m hm
    have key : 3 * a * (m : ℝ) + a ≤ 2 * b := by
      rcases lt_or_ge b (2 * a) with h | h
      · have hm1 : (m : ℝ) < 1 := by nlinarith
        have : m ≤ 0 := by exact_mod_cast (show (m : ℝ) ≤ 0 by
          have := Int.cast_lt (R := ℝ) |>.mp (by simpa using hm1 : (m : ℝ) < ((1 : ℤ) : ℝ)); exact_mod_cast (by omega : m ≤ 0))
        have : (m : ℝ) ≤ 0 := by exact_mod_cast this
        nlinarith
      · nlinarith
    have : ((m : ℝ) + 1 / 3) / b ≤ 2 / (3 * a) := by
      rw [div_le_div_iff₀ hb (by positivity)]; nlinarith
    linarith

/-- **The window route (E51).** If runners `v₁, v₂, v₃` are clear throughout a window `[J₀, J₀ + ℓ]` that
meets `window_two`'s thresholds for the two fast runners `a ≤ b`, then all five are clear at one instant of
it. This is BHK's Corollary 5 with the sharp window in place of Lemma 4, and with no requirement that the
window be a whole clear lap of runner 3. -/
theorem lonely_of_window {v₁ v₂ v₃ a b J₀ ℓ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (h123 : ∀ t, J₀ ≤ t → t ≤ J₀ + ℓ →
      (6 : ℝ)⁻¹ ≤ circDist (v₁ * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v₂ * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v₃ * t))
    (hbase : 1 / (3 * a) + 1 / (3 * b) ≤ ℓ)
    (hres : ∀ m : ℤ, 3 * (m : ℝ) * a < a + b → ((m : ℝ) + 1 / 3) / b ≤ ℓ) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v₁ * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v₂ * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v₃ * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (a * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (b * t) := by
  obtain ⟨t, h0, h1, h4, h5⟩ := window_two (J₀ := J₀) ha hab hbase hres
  obtain ⟨c1, c2, c3⟩ := h123 t h0 h1
  exact ⟨t, c1, c2, c3, h4, h5⟩

/-- A reading `p + r` with `r` in `[1/6, 5/6]`, moved by `δ` with `1/6 ≤ r + δ ≤ 5/6`, stays clear. -/
theorem clear_shift {v t δ r : ℝ} {p : ℤ} (hv : v * t = p + r) (h1 : 1 / 6 ≤ r + v * δ)
    (h2 : r + v * δ ≤ 5 / 6) : (6 : ℝ)⁻¹ ≤ circDist (v * (t + δ)) := by
  apply clear_of_band (p := p) <;> nlinarith

/-- **The `G₄` window.** At a meeting time `t` where runners 2 and 3 read `1/2` and runner 1 reads `1/4`
(BHK's named point of the orbit `⟨(1/2, 1/4)⟩`), with `v₂ < v₃ < 4 v₁` and `v₁ < v₃`, runners 1–3 are clear
on `[t − 1/(12 v₁), t + 1/(3 v₃)]`. -/
theorem g4_window {v₁ v₂ v₃ t : ℝ} {a b c : ℤ} (h1 : 0 < v₁) (h12 : v₁ < v₂) (h23 : v₂ < v₃)
    (h31 : v₃ < 4 * v₁) (ha : v₁ * t = a + 1 / 4) (hb : v₂ * t = b + 1 / 2) (hc : v₃ * t = c + 1 / 2) :
    ∀ s, t - 1 / (12 * v₁) ≤ s → s ≤ t + 1 / (3 * v₃) →
      (6 : ℝ)⁻¹ ≤ circDist (v₁ * s) ∧ (6 : ℝ)⁻¹ ≤ circDist (v₂ * s) ∧ (6 : ℝ)⁻¹ ≤ circDist (v₃ * s) := by
  intro s hs0 hs1
  have h2 : 0 < v₂ := by linarith
  have h3 : 0 < v₃ := by linarith
  obtain ⟨δ, rfl⟩ : ∃ δ, s = t + δ := ⟨s - t, by ring⟩
  have hl : -(1 / (12 * v₁)) ≤ δ := by linarith
  have hr : δ ≤ 1 / (3 * v₃) := by linarith
  have e1 : v₁ * (1 / (12 * v₁)) = 1 / 12 := by field_simp
  have e3 : v₃ * (1 / (3 * v₃)) = 1 / 3 := by field_simp
  have k1 : v₁ * (1 / (3 * v₃)) ≤ 1 / 3 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]; nlinarith
  have k2 : v₂ * (1 / (12 * v₁)) ≤ 1 / 3 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]; nlinarith
  have k2' : v₂ * (1 / (3 * v₃)) ≤ 1 / 3 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]; nlinarith
  have k3 : v₃ * (1 / (12 * v₁)) ≤ 1 / 3 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]; nlinarith
  refine ⟨clear_shift ha ?_ ?_, clear_shift hb ?_ ?_, clear_shift hc ?_ ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hl h1.le]
  · nlinarith [mul_le_mul_of_nonneg_left hr h1.le]
  · nlinarith [mul_le_mul_of_nonneg_left hl h2.le]
  · nlinarith [mul_le_mul_of_nonneg_left hr h2.le]
  · nlinarith [mul_le_mul_of_nonneg_left hl h3.le]
  · nlinarith [mul_le_mul_of_nonneg_left hr h3.le]

/-- **The `G₇` window.** At a meeting time `t` where runners 2 and 3 read `4/7` and runner 1 reads `2/7`
(BHK's named point of `⟨(2/7, 1/7)⟩`), with `v₁ < v₂ < v₃`, runners 1–3 are clear on `[t − l, t + 11/(42 v₃)]`
for any `l ≥ 0` with `l ≤ 17/(42 v₃)` and `l ≤ 5/(42 v₁)` (BHK's `J`, exactly when `l` is the smaller bound). -/
theorem g7_window {v₁ v₂ v₃ t l : ℝ} {a b c : ℤ} (h1 : 0 < v₁) (h12 : v₁ < v₂) (h23 : v₂ < v₃)
    (hl0 : 0 ≤ l) (hl3 : l ≤ 17 / (42 * v₃)) (hl1 : l ≤ 5 / (42 * v₁))
    (ha : v₁ * t = a + 2 / 7) (hb : v₂ * t = b + 4 / 7) (hc : v₃ * t = c + 4 / 7) :
    ∀ s, t - l ≤ s → s ≤ t + 11 / (42 * v₃) →
      (6 : ℝ)⁻¹ ≤ circDist (v₁ * s) ∧ (6 : ℝ)⁻¹ ≤ circDist (v₂ * s) ∧ (6 : ℝ)⁻¹ ≤ circDist (v₃ * s) := by
  intro s hs0 hs1
  have h2 : 0 < v₂ := by linarith
  have h3 : 0 < v₃ := by linarith
  obtain ⟨δ, rfl⟩ : ∃ δ, s = t + δ := ⟨s - t, by ring⟩
  have hl : -l ≤ δ := by linarith
  have hr : δ ≤ 11 / (42 * v₃) := by linarith
  have q1 : v₁ * l ≤ 5 / 42 := by
    have := mul_le_mul_of_nonneg_left hl1 h1.le
    rwa [show v₁ * (5 / (42 * v₁)) = 5 / 42 by field_simp] at this
  have q2 : v₂ * l ≤ 17 / 42 := by
    have := mul_le_mul_of_nonneg_left hl3 h2.le
    have : v₂ * (17 / (42 * v₃)) ≤ 17 / 42 := by
      rw [show v₂ * (17 / (42 * v₃)) = 17 * v₂ / (42 * v₃) by ring, div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have q3 : v₃ * l ≤ 17 / 42 := by
    have := mul_le_mul_of_nonneg_left hl3 h3.le
    rwa [show v₃ * (17 / (42 * v₃)) = 17 / 42 by field_simp] at this
  have r1 : v₁ * (11 / (42 * v₃)) ≤ 11 / 42 := by
    rw [show v₁ * (11 / (42 * v₃)) = 11 * v₁ / (42 * v₃) by ring, div_le_iff₀ (by positivity)]; nlinarith
  have r2 : v₂ * (11 / (42 * v₃)) ≤ 11 / 42 := by
    rw [show v₂ * (11 / (42 * v₃)) = 11 * v₂ / (42 * v₃) by ring, div_le_iff₀ (by positivity)]; nlinarith
  have r3 : v₃ * (11 / (42 * v₃)) = 11 / 42 := by field_simp
  refine ⟨clear_shift ha ?_ ?_, clear_shift hb ?_ ?_, clear_shift hc ?_ ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hl h1.le]
  · nlinarith [mul_le_mul_of_nonneg_left hr h1.le]
  · nlinarith [mul_le_mul_of_nonneg_left hl h2.le]
  · nlinarith [mul_le_mul_of_nonneg_left hr h2.le]
  · nlinarith [mul_le_mul_of_nonneg_left hl h3.le]
  · nlinarith [mul_le_mul_of_nonneg_left hr h3.le]

/-- **`G₄` closes by the sharp window** whenever the window `1/(12 v₁) + 1/(3 v₃)` meets `window_two`'s
thresholds for the fast runners `a ≤ b`. -/
theorem g4_lonely {v₁ v₂ v₃ a b t : ℝ} {p q r : ℤ} (h1 : 0 < v₁) (h12 : v₁ < v₂) (h23 : v₂ < v₃)
    (h31 : v₃ < 4 * v₁) (hp : v₁ * t = p + 1 / 4) (hq : v₂ * t = q + 1 / 2) (hr : v₃ * t = r + 1 / 2)
    (ha : 0 < a) (hab : a ≤ b)
    (hbase : 1 / (3 * a) + 1 / (3 * b) ≤ 1 / (12 * v₁) + 1 / (3 * v₃))
    (hres : ∀ m : ℤ, 3 * (m : ℝ) * a < a + b → ((m : ℝ) + 1 / 3) / b ≤ 1 / (12 * v₁) + 1 / (3 * v₃)) :
    ∃ s : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v₁ * s) ∧ (6 : ℝ)⁻¹ ≤ circDist (v₂ * s) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v₃ * s) ∧ (6 : ℝ)⁻¹ ≤ circDist (a * s) ∧ (6 : ℝ)⁻¹ ≤ circDist (b * s) := by
  apply lonely_of_window (J₀ := t - 1 / (12 * v₁)) (ℓ := 1 / (12 * v₁) + 1 / (3 * v₃)) ha hab _ hbase hres
  intro s h0 h1'
  exact g4_window h1 h12 h23 h31 hp hq hr s h0 (by linarith)

/-- **`G₇` closes by the sharp window** whenever `l + 11/(42 v₃)` meets `window_two`'s thresholds, for
`l = min(17/(42 v₃), 5/(42 v₁))` or any smaller `l ≥ 0`. -/
theorem g7_lonely {v₁ v₂ v₃ a b t l : ℝ} {p q r : ℤ} (h1 : 0 < v₁) (h12 : v₁ < v₂) (h23 : v₂ < v₃)
    (hl0 : 0 ≤ l) (hl3 : l ≤ 17 / (42 * v₃)) (hl1 : l ≤ 5 / (42 * v₁))
    (hp : v₁ * t = p + 2 / 7) (hq : v₂ * t = q + 4 / 7) (hr : v₃ * t = r + 4 / 7)
    (ha : 0 < a) (hab : a ≤ b)
    (hbase : 1 / (3 * a) + 1 / (3 * b) ≤ l + 11 / (42 * v₃))
    (hres : ∀ m : ℤ, 3 * (m : ℝ) * a < a + b → ((m : ℝ) + 1 / 3) / b ≤ l + 11 / (42 * v₃)) :
    ∃ s : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v₁ * s) ∧ (6 : ℝ)⁻¹ ≤ circDist (v₂ * s) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v₃ * s) ∧ (6 : ℝ)⁻¹ ≤ circDist (a * s) ∧ (6 : ℝ)⁻¹ ≤ circDist (b * s) := by
  apply lonely_of_window (J₀ := t - l) (ℓ := l + 11 / (42 * v₃)) ha hab _ hbase hres
  intro s h0 h1'
  exact g7_window h1 h12 h23 hl0 hl3 hl1 hp hq hr s h0 (by linarith)

/-- Five readings in the band at one instant: the conclusion shape used below. -/
def Lonely5 (v₁ v₂ v₃ a b s : ℝ) : Prop :=
  (6 : ℝ)⁻¹ ≤ circDist (v₁ * s) ∧ (6 : ℝ)⁻¹ ≤ circDist (v₂ * s) ∧ (6 : ℝ)⁻¹ ≤ circDist (v₃ * s) ∧
    (6 : ℝ)⁻¹ ≤ circDist (a * s) ∧ (6 : ℝ)⁻¹ ≤ circDist (b * s)

/-- A reading `v·s` with `1/6 ≤ v·s - p ≤ 5/6`. -/
theorem clear_of_lap {v s : ℝ} (p : ℤ) (h1 : (p : ℝ) + 1 / 6 ≤ v * s) (h2 : v * s ≤ (p : ℝ) + 5 / 6) :
    (6 : ℝ)⁻¹ ≤ circDist (v * s) := clear_of_band h1 h2

/-- **The spread instant** (case (i)): every speed in `[v₁, 5 v₁]` reads in the band at `1/(6 v₁)`. -/
theorem spread_clear {v₁ v : ℝ} (h1 : 0 < v₁) (hlo : v₁ ≤ v) (hhi : v ≤ 5 * v₁) :
    (6 : ℝ)⁻¹ ≤ circDist (v * (1 / (6 * v₁))) := by
  apply clear_of_lap 0
  · rw [Int.cast_zero, zero_add, mul_one_div, le_div_iff₀ (by positivity)]; linarith
  · rw [Int.cast_zero, zero_add, mul_one_div, div_le_iff₀ (by positivity)]; linarith

/-- **The box with runner 5 on its second lap** (case (ii)): with `v₁ ≤ v ≤ v₄`, `v₄ ≤ 5 v₁`, `7 v₄ ≤ 5 v₅`,
`v₅ ≤ 11 v₁`, every slow runner reads in `[1/6, 5/6]` and runner 5 in `[7/6, 11/6]` at
`max(1/(6 v₁), 7/(6 v₅))`. -/
theorem box01_slow {v₁ v₄ v₅ v : ℝ} (h1 : 0 < v₁) (hlo : v₁ ≤ v) (hv4 : v ≤ v₄) (h45 : v₄ ≤ 5 * v₁)
    (h75 : 7 * v₄ ≤ 5 * v₅) (h5 : 0 < v₅) :
    (6 : ℝ)⁻¹ ≤ circDist (v * max (1 / (6 * v₁)) (7 / (6 * v₅))) := by
  have hv : 0 < v := by linarith
  apply clear_of_lap 0
  · rw [Int.cast_zero, zero_add]
    have : v * (1 / (6 * v₁)) ≤ v * max (1 / (6 * v₁)) (7 / (6 * v₅)) :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hv.le
    have e : 1 / 6 ≤ v * (1 / (6 * v₁)) := by
      rw [mul_one_div, le_div_iff₀ (by positivity)]; linarith
    linarith
  · rw [Int.cast_zero, zero_add]
    rcases le_total (1 / (6 * v₁)) (7 / (6 * v₅)) with h | h
    · rw [max_eq_right h, show v * (7 / (6 * v₅)) = 7 * v / (6 * v₅) by ring, div_le_iff₀ (by positivity)]
      nlinarith
    · rw [max_eq_left h, mul_one_div, div_le_iff₀ (by positivity)]; linarith

theorem box01_fast {v₁ v₅ : ℝ} (h1 : 0 < v₁) (h5 : 0 < v₅) (h11 : v₅ ≤ 11 * v₁) :
    (6 : ℝ)⁻¹ ≤ circDist (v₅ * max (1 / (6 * v₁)) (7 / (6 * v₅))) := by
  apply clear_of_lap 1
  · push_cast
    have : v₅ * (7 / (6 * v₅)) ≤ v₅ * max (1 / (6 * v₁)) (7 / (6 * v₅)) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) h5.le
    have e : v₅ * (7 / (6 * v₅)) = 7 / 6 := by field_simp
    linarith
  · push_cast
    rcases le_total (1 / (6 * v₁)) (7 / (6 * v₅)) with h | h
    · rw [max_eq_right h, show v₅ * (7 / (6 * v₅)) = 7 / 6 by field_simp]; norm_num
    · rw [max_eq_left h, mul_one_div, div_le_iff₀ (by positivity)]; linarith

/-- The resonant thresholds of `window_two` for `m ≥ 1`, from `v₅ ≥ 8 v₁`-type room: if
`2/3 + v₅/(3 v₄) ≤ W·v₅` then `(m + 1/3)/v₅ ≤ W` for every `m` with `3 m v₄ < v₄ + v₅`. -/
theorem res_of_room {v₄ v₅ W : ℝ} (h4 : 0 < v₄) (h5 : 0 < v₅) (hroom : 2 / 3 + v₅ / (3 * v₄) ≤ W * v₅)
    (m : ℤ) (hm : 3 * (m : ℝ) * v₄ < v₄ + v₅) : ((m : ℝ) + 1 / 3) / v₅ ≤ W := by
  rw [div_le_iff₀ h5]
  have : (m : ℝ) < (v₄ + v₅) / (3 * v₄) := by rw [lt_div_iff₀ (by positivity)]; linarith
  have e : (v₄ + v₅) / (3 * v₄) = 1 / 3 + v₅ / (3 * v₄) := by field_simp
  linarith

/-- **`G₄` closed natively.** Speeds `0 < v₁ < v₂ < v₃ < a < b` with `3 v₁ < v₃ < 4 v₁`, and a meeting time
`t` at BHK's named point of `G₄` (runner 1 reads `1/4`, runners 2 and 3 read `1/2`). Then some instant is
lonely: the spread instant, the second-lap box of runner 5, or the `G₄` window by `window_two`. -/
theorem g4_closed {v₁ v₂ v₃ a b t : ℝ} {p q r : ℤ} (h1 : 0 < v₁) (h12 : v₁ < v₂) (h23 : v₂ < v₃)
    (h3a : v₃ < a) (hab : a < b) (h13 : 3 * v₁ < v₃) (h31 : v₃ < 4 * v₁)
    (hp : v₁ * t = p + 1 / 4) (hq : v₂ * t = q + 1 / 2) (hr : v₃ * t = r + 1 / 2) :
    ∃ s, Lonely5 v₁ v₂ v₃ a b s := by
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  have h3 : 0 < v₃ := by linarith
  have h3n : 0 ≤ 1 / (3 * v₃) := by positivity
  by_cases hi : b ≤ 5 * v₁
  · exact ⟨_, spread_clear h1 le_rfl (by linarith), spread_clear h1 h12.le (by linarith),
      spread_clear h1 (by linarith) (by linarith), spread_clear h1 (by linarith) (by linarith),
      spread_clear h1 (by linarith) hi⟩
  push Not at hi
  by_cases hii : a ≤ 5 * v₁ ∧ 7 * a ≤ 5 * b ∧ b ≤ 11 * v₁
  · obtain ⟨x1, x2, x3⟩ := hii
    exact ⟨_, box01_slow h1 le_rfl (by linarith) x1 x2 hb, box01_slow h1 h12.le (by linarith) x1 x2 hb,
      box01_slow h1 (by linarith) (by linarith) x1 x2 hb, box01_slow h1 (by linarith) le_rfl x1 x2 hb,
      box01_fast h1 hb x3⟩
  have hW1 : 1 / (3 * a) ≤ 1 / (3 * v₃) := one_div_le_one_div_of_le (by positivity) (by linarith)
  have hW2 : 1 / (3 * b) ≤ 1 / (12 * v₁) := one_div_le_one_div_of_le (by positivity) (by linarith)
  obtain ⟨s, hs⟩ := g4_lonely (t := t) h1 h12 h23 h31 hp hq hr ha hab.le (by linarith) (by
    intro m hm
    rcases le_or_gt m 0 with hm0 | hm0
    · have : ((m : ℝ) + 1 / 3) / b ≤ 1 / (3 * b) := by
        rw [div_le_div_iff₀ hb (by positivity)]; have : (m : ℝ) ≤ 0 := by exact_mod_cast hm0
        nlinarith
      linarith
    · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm0
      have h2a : 2 * a < b := by nlinarith
      have h8 : 8 * v₁ ≤ b := by
        rcases not_and_or.mp hii with h | h
        · push Not at h; linarith
        · rcases not_and_or.mp h with h' | h'
          · push Not at h'; linarith
          · push Not at h'; linarith
      apply res_of_room ha hb _ m hm
      have e1 : b / (3 * a) ≤ b / (3 * v₃) := div_le_div_of_nonneg_left hb.le (by positivity) (by linarith)
      have e2 : (1 / (12 * v₁) + 1 / (3 * v₃)) * b = b / (12 * v₁) + b / (3 * v₃) := by ring
      have e3 : 2 / 3 ≤ b / (12 * v₁) := by rw [le_div_iff₀ (by positivity)]; linarith
      linarith)
  exact ⟨s, hs⟩

/-- **`G₇` closed natively.** As `g4_closed`, at BHK's named point of `G₇` (runner 1 reads `2/7`, runners 2
and 3 read `4/7`), with `3 v₁ < v₃`. -/
theorem g7_closed {v₁ v₂ v₃ a b t : ℝ} {p q r : ℤ} (h1 : 0 < v₁) (h12 : v₁ < v₂) (h23 : v₂ < v₃)
    (h3a : v₃ < a) (hab : a < b) (h13 : 3 * v₁ < v₃)
    (hp : v₁ * t = p + 2 / 7) (hq : v₂ * t = q + 4 / 7) (hr : v₃ * t = r + 4 / 7) :
    ∃ s, Lonely5 v₁ v₂ v₃ a b s := by
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  have h3 : 0 < v₃ := by linarith
  by_cases hi : b ≤ 5 * v₁
  · exact ⟨_, spread_clear h1 le_rfl (by linarith), spread_clear h1 h12.le (by linarith),
      spread_clear h1 (by linarith) (by linarith), spread_clear h1 (by linarith) (by linarith),
      spread_clear h1 (by linarith) hi⟩
  push Not at hi
  by_cases hii : a ≤ 5 * v₁ ∧ 7 * a ≤ 5 * b ∧ b ≤ 11 * v₁
  · obtain ⟨x1, x2, x3⟩ := hii
    exact ⟨_, box01_slow h1 le_rfl (by linarith) x1 x2 hb, box01_slow h1 h12.le (by linarith) x1 x2 hb,
      box01_slow h1 (by linarith) (by linarith) x1 x2 hb, box01_slow h1 (by linarith) le_rfl x1 x2 hb,
      box01_fast h1 hb x3⟩
  set l := min (17 / (42 * v₃)) (5 / (42 * v₁)) with hl
  have hl0 : 0 ≤ l := le_min (by positivity) (by positivity)
  have hla := min_le_left (17 / (42 * v₃)) (5 / (42 * v₁))
  have hlb := min_le_right (17 / (42 * v₃)) (5 / (42 * v₁))
  -- the base threshold, in both cases of the minimum
  have hbase : 1 / (3 * a) + 1 / (3 * b) ≤ l + 11 / (42 * v₃) := by
    have hA : 1 / (3 * a) ≤ 14 / (42 * v₃) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    rcases min_choice (17 / (42 * v₃)) (5 / (42 * v₁)) with h | h
    · rw [hl, h]
      have hB : 1 / (3 * b) ≤ 14 / (42 * v₃) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
      have e : 17 / (42 * v₃) + 11 / (42 * v₃) = 28 / (42 * v₃) := by ring
      have e' : 14 / (42 * v₃) + 14 / (42 * v₃) = 28 / (42 * v₃) := by ring
      linarith
    · rw [hl, h]
      have hB : 1 / (3 * b) ≤ 14 / (210 * v₁) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
      have hC : 3 / (42 * v₃) ≤ 1 / (42 * v₁) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
      have e1 : 14 / (42 * v₃) = 11 / (42 * v₃) + 3 / (42 * v₃) := by ring
      have e2 : 14 / (210 * v₁) + 1 / (42 * v₁) ≤ 5 / (42 * v₁) := by
        rw [show 14 / (210 * v₁) + 1 / (42 * v₁) = 19 / (210 * v₁) by field_simp; ring,
          div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
      linarith
  obtain ⟨s, hs⟩ := g7_lonely (t := t) (l := l) h1 h12 h23 hl0 hla hlb hp hq hr ha hab.le hbase (by
    intro m hm
    rcases le_or_gt m 0 with hm0 | hm0
    · have : ((m : ℝ) + 1 / 3) / b ≤ 1 / (3 * b) := by
        rw [div_le_div_iff₀ hb (by positivity)]; have : (m : ℝ) ≤ 0 := by exact_mod_cast hm0
        nlinarith
      have : 0 ≤ 1 / (3 * a) := by positivity
      linarith
    · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm0
      have h2a : 2 * a < b := by nlinarith
      have h8 : 8 * v₁ ≤ b := by
        rcases not_and_or.mp hii with h | h
        · push Not at h; linarith
        · rcases not_and_or.mp h with h' | h'
          · push Not at h'; linarith
          · push Not at h'; linarith
      apply res_of_room ha hb _ m hm
      have e1 : b / (3 * a) ≤ b / (3 * v₃) := div_le_div_of_nonneg_left hb.le (by positivity) (by linarith)
      rcases min_choice (17 / (42 * v₃)) (5 / (42 * v₁)) with h | h
      · rw [hl, h]
        have e2 : (17 / (42 * v₃) + 11 / (42 * v₃)) * b = 2 * b / (3 * v₃) := by field_simp; ring
        have e3 : 2 / 3 ≤ b / (3 * v₃) := by rw [le_div_iff₀ (by positivity)]; nlinarith
        have e4 : 2 * b / (3 * v₃) = b / (3 * v₃) + b / (3 * v₃) := by ring
        linarith
      · rw [hl, h]
        have e2 : (5 / (42 * v₁) + 11 / (42 * v₃)) * b = 5 * b / (42 * v₁) + 11 * b / (42 * v₃) := by ring
        have e3 : b / (3 * v₃) = 11 * b / (42 * v₃) + 3 * b / (42 * v₃) := by field_simp; ring
        have e4 : 3 * b / (42 * v₃) ≤ b / (42 * v₁) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
        have e5 : 2 / 3 + b / (42 * v₁) ≤ 5 * b / (42 * v₁) := by
          rw [show 5 * b / (42 * v₁) = b / (42 * v₁) + 4 * b / (42 * v₁) by ring]
          have : 2 / 3 ≤ 4 * b / (42 * v₁) := by rw [le_div_iff₀ (by positivity)]; linarith
          linarith
        linarith)
  exact ⟨s, hs⟩

/-- `N = 4 q + r` read at `1/4`: `N/4 = q + r/4`. -/
theorem div_four_split (N q r : ℕ) (h : N = 4 * q + r) : (N : ℝ) / 4 = (q : ℤ) + (r : ℝ) / 4 := by
  subst h; push_cast; ring

/-- **`G₄` on whole numbers, end to end.** Speeds `v₁ < … < v₅` with `3 v₁ < v₃ < 4 v₁`, `v₃ − v₂ = 4 g`,
`v₃ = g c₃`, `v₁ = g c₁`, `c₃ ≡ 2` and `c₁ ≡ ±1 (mod 4)` (BHK's orbit `G₄`): some instant is lonely. The
meeting time is `k/(4g)`, `k ∈ {1, 3}`; `g4_closed` does the rest. -/
theorem g4_nat {v₁ v₂ v₃ v₄ v₅ g c₃ c₁ : ℕ} (h1 : 0 < v₁) (h12 : v₁ < v₂) (h23 : v₂ < v₃) (h34 : v₃ < v₄)
    (h45 : v₄ < v₅) (h13 : 3 * v₁ < v₃) (h31 : v₃ < 4 * v₁) (hg : 0 < g) (hD : v₃ = v₂ + 4 * g)
    (hc3 : v₃ = g * c₃) (hc1 : v₁ = g * c₁) (hm3 : c₃ % 4 = 2) (hm1 : c₁ % 4 = 1 ∨ c₁ % 4 = 3) :
    ∃ s, Lonely5 v₁ v₂ v₃ v₄ v₅ s := by
  obtain ⟨k, hk1, hk3⟩ : ∃ k : ℕ, (c₁ * k) % 4 = 1 ∧ (c₃ * k) % 4 = 2 := by
    rcases hm1 with h | h
    · exact ⟨1, by omega, by omega⟩
    · exact ⟨3, by rw [Nat.mul_mod, h], by rw [Nat.mul_mod, hm3]⟩
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  set t : ℝ := (k : ℝ) / (4 * g) with ht
  have r1 : (v₁ : ℝ) * t = ((c₁ * k / 4 : ℕ) : ℤ) + 1 / 4 := by
    have : (v₁ : ℝ) * t = ((c₁ * k : ℕ) : ℝ) / 4 := by rw [ht, hc1]; push_cast; field_simp
    rw [this, div_four_split (c₁ * k) (c₁ * k / 4) 1 (by omega)]; norm_num
  have r3 : (v₃ : ℝ) * t = ((c₃ * k / 4 : ℕ) : ℤ) + 1 / 2 := by
    have : (v₃ : ℝ) * t = ((c₃ * k : ℕ) : ℝ) / 4 := by rw [ht, hc3]; push_cast; field_simp
    rw [this, div_four_split (c₃ * k) (c₃ * k / 4) 2 (by omega)]; norm_num
  have r2 : (v₂ : ℝ) * t = (((c₃ * k / 4 : ℕ) : ℤ) - (k : ℤ) : ℤ) + 1 / 2 := by
    have e : (v₂ : ℝ) = v₃ - 4 * g := by
      have : ((v₃ : ℕ) : ℝ) = v₂ + 4 * g := by exact_mod_cast hD
      linarith
    have e2 : (v₂ : ℝ) * t = (v₃ : ℝ) * t - k := by rw [e, ht]; field_simp
    rw [e2, r3]; push_cast; ring
  exact g4_closed (t := t) (by exact_mod_cast h1) (by exact_mod_cast h12) (by exact_mod_cast h23)
    (by exact_mod_cast h34) (by exact_mod_cast h45) (by exact_mod_cast h13) (by exact_mod_cast h31) r1 r2 r3

/-- `N = 7 q + r` read at `1/7`. -/
theorem div_seven_split (N q r : ℕ) (h : N = 7 * q + r) : (N : ℝ) / 7 = (q : ℤ) + (r : ℝ) / 7 := by
  subst h; push_cast; ring

/-- **`G₇` on whole numbers, end to end.** Speeds as in `g4_nat` with `3 v₁ < v₃`, `v₃ − v₂ = 7 g`,
`v₃ = g c₃`, `v₁ = g c₁`, `c₁ ≢ 0` and `c₃ ≡ 2 c₁ (mod 7)` (BHK's orbit `G₇ = ⟨(2/7, 1/7)⟩`): some instant is
lonely. The meeting time is `k/(7g)` with `c₁ k ≡ 2 (mod 7)`; `g7_closed` does the rest. -/
theorem g7_nat {v₁ v₂ v₃ v₄ v₅ g c₃ c₁ : ℕ} (h1 : 0 < v₁) (h12 : v₁ < v₂) (h23 : v₂ < v₃) (h34 : v₃ < v₄)
    (h45 : v₄ < v₅) (h13 : 3 * v₁ < v₃) (hg : 0 < g) (hD : v₃ = v₂ + 7 * g)
    (hc3 : v₃ = g * c₃) (hc1 : v₁ = g * c₁) (hn : c₁ % 7 ≠ 0) (hm : c₃ % 7 = (2 * c₁) % 7) :
    ∃ s, Lonely5 v₁ v₂ v₃ v₄ v₅ s := by
  obtain ⟨k, hk1, hk3⟩ : ∃ k : ℕ, (c₁ * k) % 7 = 2 ∧ (c₃ * k) % 7 = 4 := by
    have h7 : c₁ % 7 < 7 := Nat.mod_lt _ (by norm_num)
    have key : ∀ k : ℕ, (c₁ * k) % 7 = 2 → (c₃ * k) % 7 = 4 := by
      intro k hk; rw [Nat.mul_mod, hm, ← Nat.mul_mod, show 2 * c₁ * k = 2 * (c₁ * k) by ring,
        Nat.mul_mod, hk]
    interval_cases hc : c₁ % 7
    · exact absurd rfl hn
    · exact ⟨2, by rw [Nat.mul_mod, hc], key 2 (by rw [Nat.mul_mod, hc])⟩
    · exact ⟨1, by rw [Nat.mul_mod, hc], key 1 (by rw [Nat.mul_mod, hc])⟩
    · exact ⟨3, by rw [Nat.mul_mod, hc], key 3 (by rw [Nat.mul_mod, hc])⟩
    · exact ⟨4, by rw [Nat.mul_mod, hc], key 4 (by rw [Nat.mul_mod, hc])⟩
    · exact ⟨6, by rw [Nat.mul_mod, hc], key 6 (by rw [Nat.mul_mod, hc])⟩
    · exact ⟨5, by rw [Nat.mul_mod, hc], key 5 (by rw [Nat.mul_mod, hc])⟩
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  set t : ℝ := (k : ℝ) / (7 * g) with ht
  have r1 : (v₁ : ℝ) * t = ((c₁ * k / 7 : ℕ) : ℤ) + 2 / 7 := by
    have : (v₁ : ℝ) * t = ((c₁ * k : ℕ) : ℝ) / 7 := by rw [ht, hc1]; push_cast; field_simp
    rw [this, div_seven_split (c₁ * k) (c₁ * k / 7) 2 (by omega)]; norm_num
  have r3 : (v₃ : ℝ) * t = ((c₃ * k / 7 : ℕ) : ℤ) + 4 / 7 := by
    have : (v₃ : ℝ) * t = ((c₃ * k : ℕ) : ℝ) / 7 := by rw [ht, hc3]; push_cast; field_simp
    rw [this, div_seven_split (c₃ * k) (c₃ * k / 7) 4 (by omega)]; norm_num
  have r2 : (v₂ : ℝ) * t = (((c₃ * k / 7 : ℕ) : ℤ) - (k : ℤ) : ℤ) + 4 / 7 := by
    have e : (v₂ : ℝ) = v₃ - 7 * g := by
      have : ((v₃ : ℕ) : ℝ) = v₂ + 7 * g := by exact_mod_cast hD
      linarith
    have e2 : (v₂ : ℝ) * t = (v₃ : ℝ) * t - k := by rw [e, ht]; field_simp
    rw [e2, r3]; push_cast; ring
  exact g7_closed (t := t) (by exact_mod_cast h1) (by exact_mod_cast h12) (by exact_mod_cast h23)
    (by exact_mod_cast h34) (by exact_mod_cast h45) (by exact_mod_cast h13) r1 r2 r3







/-- The point `(x/n, y/n)` lies in BHK's parallelogram at ratio `1/3`. -/
def inP (n x y : ℕ) : Bool := n ≤ 6 * x && 6 * x ≤ 5 * n && 6 * x + 2 * n ≤ 18 * y && 18 * y ≤ 10 * n + 6 * x

/-- BHK's two exceptional orbits. -/
def isExc (n a b : ℕ) : Bool :=
  (n == 4 && a % 4 == 2 && b % 2 == 1) || (n == 7 && b % 7 != 0 && a % 7 == (2 * b) % 7)

def orbitHits (n a b : ℕ) : Bool := (List.range n).any fun k => inP n ((a * k) % n) ((b * k) % n)

def check (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => (List.range n).all fun a => (List.range n).all fun b =>
    !(2 ≤ n && 1 ≤ a && 1 ≤ b && Nat.gcd (Nat.gcd a b) n == 1) || isExc n a b || orbitHits n a b

set_option maxHeartbeats 0 in
theorem check_orbits : check 35 = true := by decide +kernel

/-- The finite check, unpacked. -/
theorem orbit_hits_or_exc {n a b : ℕ} (hn2 : 2 ≤ n) (hn : n ≤ 35) (ha : 1 ≤ a) (han : a < n) (hb : 1 ≤ b)
    (hbn : b < n) (hg : Nat.gcd (Nat.gcd a b) n = 1) :
    isExc n a b = true ∨ ∃ k < n, inP n ((a * k) % n) ((b * k) % n) = true := by
  have h := check_orbits
  simp only [check, List.all_eq_true, List.mem_range] at h
  have := h n (by omega) a han b hbn
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    not_le, beq_eq_false_iff_ne, ne_eq] at this
  rcases this with ((((h1 | h1) | h1) | h1) | h1) | h1
  · omega
  · omega
  · omega
  · exact absurd hg h1
  · exact Or.inl h1
  · right
    simp only [orbitHits, List.any_eq_true, List.mem_range] at h1
    obtain ⟨k, hk, hk'⟩ := h1
    exact ⟨k, hk, hk'⟩

/-- The exceptional orbits really miss `P_{1/3}`. -/
theorem g4_misses : orbitHits 4 2 1 = false := by decide
theorem g7_misses : orbitHits 7 2 1 = false := by decide

/-- **The bounded short steps.** For a step `(i, j)` allowed by `orbit_isolation_two_bhk`
(`0 ≤ i ≤ 4`, `|6j| < 9 + 2i`) with `i, j ≠ 0` and `(i, j) ≠ (1, ±1)`, the step inequality
`2/9·i + 2/3·|j| − 2/n·i·|j| < 1` forces `n < 36`. The steps left for `n ≥ 36` are `(1, ±1)`, `(i, 0)`
and the axis steps `(0, ±1)`, `(1, 0)`. -/
theorem short_step_bounded {i j : ℤ} {n : ℝ} (hn : 36 ≤ n) (hi0 : 0 ≤ i) (hi4 : i ≤ 4)
    (hj1 : -(9 + 2 * i) < 6 * j) (hj2 : 6 * j < 9 + 2 * i) (hi : i ≠ 0) (hj : j ≠ 0)
    (hd : ¬ (i = 1 ∧ (j = 1 ∨ j = -1))) :
    1 ≤ 2 / 9 * |(i : ℝ)| + 2 / 3 * |(j : ℝ)| - 2 / n * |(i : ℝ)| * |(j : ℝ)| := by
  have hn0 : 0 < n := by linarith
  have hjb : -2 ≤ j ∧ j ≤ 2 := by constructor <;> omega
  obtain ⟨hjl, hju⟩ := hjb
  interval_cases i <;> interval_cases j <;> simp at hj hi hd ⊢ <;>
    (rw [div_mul_eq_mul_div, div_mul_eq_mul_div]; rw [← sub_nonneg]; field_simp; nlinarith)



/-- A point of the orbit, read back in whole numbers. -/
theorem point_of_mem {n c₃ c₁ x y : ℕ} (hn : 0 < n) (hx : x < n) (hy : y < n)
    (h : ((x : ZMod n), (y : ZMod n)) ∈ meetingOrbit n c₃ c₁) :
    ∃ k < n, (c₃ * k) % n = x ∧ (c₁ * k) % n = y := by
  have h' : (((x : ℤ) : ZMod n), ((y : ℤ) : ZMod n)) ∈ meetingOrbit n c₃ c₁ := by
    simpa only [Int.cast_natCast] using h
  obtain ⟨k, hk, h1, h2⟩ := (mem_meetingOrbit_iff n c₃ c₁ hn x y).mp h'
  have e1 : ((x : ℤ) % n) = x := Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hx)
  have e2 : ((y : ℤ) % n) = y := Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hy)
  refine ⟨k, hk, ?_, ?_⟩
  · have := h1.symm.trans e1; exact_mod_cast this
  · have := h2.symm.trans e2; exact_mod_cast this

/-- An orbit step in `ZMod n` terms. -/
theorem step_of_onOrbit {n c₃ c₁ : ℕ} (hn : 0 < n) {i j : ℤ} (h : OnOrbit n c₃ c₁ i j) :
    ∃ z : ℤ, z * (c₃ : ZMod n) = (i : ZMod n) ∧ z * (c₁ : ZMod n) = (j : ZMod n) := by
  have hm := (mem_meetingOrbit_iff n c₃ c₁ hn i j).mpr h
  obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
  refine ⟨z, ?_, ?_⟩
  · have := congrArg Prod.fst hz; simpa [zsmul_eq_mul] using this
  · have := congrArg Prod.snd hz; simpa [zsmul_eq_mul] using this

theorem natCast_zmod_ne_zero {n c : ℕ} (h : c % n ≠ 0) : (c : ZMod n) ≠ 0 := by
  intro h0; rw [ZMod.natCast_eq_zero_iff] at h0; exact h (Nat.mod_eq_zero_of_dvd h0)

/-- Membership of `z • (c₃, c₁)`. -/
theorem zsmul_mem_orbit (n c₃ c₁ : ℕ) (z : ℤ) :
    (z * (c₃ : ZMod n), z * (c₁ : ZMod n)) ∈ meetingOrbit n c₃ c₁ := by
  have := (meetingOrbit n c₃ c₁).zsmul_mem (AddSubgroup.mem_zmultiples ((c₃ : ZMod n), (c₁ : ZMod n))) z
  simpa [zsmul_eq_mul] using this

/-- **Axis steps cannot occur off the axes**: `(0, ±1)` on the orbit forces `c₃ ≡ 0`; `(1, 0)` forces
`c₁ ≡ 0`. -/
theorem axis_step_c3 {n c₃ c₁ : ℕ} (hn : 0 < n) {j : ℤ} (hj : j = 1 ∨ j = -1)
    (h : OnOrbit n c₃ c₁ 0 j) : (c₃ : ZMod n) = 0 := by
  obtain ⟨z, h3, h1⟩ := step_of_onOrbit hn h
  push_cast at h3
  rcases hj with rfl | rfl
  · push_cast at h1
    calc (c₃ : ZMod n) = c₃ * (z * c₁) := by rw [h1, mul_one]
      _ = c₁ * (z * c₃) := by ring
      _ = 0 := by rw [h3, mul_zero]
  · push_cast at h1
    calc (c₃ : ZMod n) = -(c₃ * (z * c₁)) := by rw [h1]; ring
      _ = -(c₁ * (z * c₃)) := by ring
      _ = 0 := by rw [h3]; ring

theorem axis_step_c1 {n c₃ c₁ : ℕ} (hn : 0 < n) (h : OnOrbit n c₃ c₁ 1 0) : (c₁ : ZMod n) = 0 := by
  obtain ⟨z, h3, h1⟩ := step_of_onOrbit hn h
  push_cast at h3 h1
  calc (c₁ : ZMod n) = c₁ * (z * c₃) := by rw [h3, mul_one]
    _ = c₃ * (z * c₁) := by ring
    _ = 0 := by rw [h1, mul_zero]

/-- **The diagonal step** `(1, ±1)`: the orbit contains `(m, ±m)` for every `m`, and `m = ⌊n/2⌋` lies in
`P_{1/3}`. -/
theorem diag_step_hits {n c₃ c₁ : ℕ} (hn : 2 ≤ n) {j : ℤ} (hj : j = 1 ∨ j = -1)
    (h : OnOrbit n c₃ c₁ 1 j) : ∃ k < n, inP n ((c₃ * k) % n) ((c₁ * k) % n) = true := by
  have hn0 : 0 < n := by omega
  obtain ⟨z, h3, h1⟩ := step_of_onOrbit hn0 h
  push_cast at h3
  set m := n / 2 with hm
  have hm1 : 1 ≤ m := by omega
  have hmn : m < n := by omega
  have hmem := zsmul_mem_orbit n c₃ c₁ ((m : ℤ) * z)
  rcases hj with rfl | rfl
  · push_cast at h1
    have e : (((m : ℤ) * z : ℤ) * (c₃ : ZMod n), ((m : ℤ) * z : ℤ) * (c₁ : ZMod n)) =
        ((m : ZMod n), (m : ZMod n)) := by
      push_cast; rw [mul_assoc, mul_assoc, h3, h1, mul_one]
    rw [e] at hmem
    obtain ⟨k, hk, hx, hy⟩ := point_of_mem hn0 hmn hmn hmem
    refine ⟨k, hk, ?_⟩
    rw [hx, hy]; simp only [inP, Bool.and_eq_true, decide_eq_true_eq]; omega
  · push_cast at h1
    have e : (((m : ℤ) * z : ℤ) * (c₃ : ZMod n), ((m : ℤ) * z : ℤ) * (c₁ : ZMod n)) =
        ((m : ZMod n), ((n - m : ℕ) : ZMod n)) := by
      push_cast
      rw [Nat.cast_sub hmn.le, ZMod.natCast_self, mul_assoc, mul_assoc, h3, h1]; ring
    rw [e] at hmem
    obtain ⟨k, hk, hx, hy⟩ := point_of_mem hn0 hmn (by omega) hmem
    refine ⟨k, hk, ?_⟩
    rw [hx, hy]; simp only [inP, Bool.and_eq_true, decide_eq_true_eq]; omega

/-- **Walking by a step.** The least `t` with `L ≤ 3(X + t·i)`: below it every `t'` falls short, and it
overshoots by less than `3i` unless `t = 0`. -/
theorem walk {X i L : ℕ} (hi : 0 < i) :
    ∃ t, L ≤ 3 * (X + t * i) ∧ (∀ t' < t, 3 * (X + t' * i) < L) ∧ (t = 0 ∨ 3 * (X + t * i) < L + 3 * i) := by
  classical
  have hex : ∃ t, L ≤ 3 * (X + t * i) := ⟨L, by nlinarith⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, fun t' ht' => by
    have := Nat.find_min hex ht'; omega, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · exact Or.inl h0
  · right
    have h1 := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    have e : (Nat.find hex - 1) * i + i = Nat.find hex * i := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hpos]
    omega

/-- **The horizontal step** `(i, 0)`, `1 ≤ i ≤ 4`, off the axes: an orbit point at height in `[n/3, 2n/3]`
(Bézout on `c₁`), walked by the step `(i, 0)` into `x ∈ [n/3, 2n/3]`, lies in `P_{1/3}`. -/
theorem horiz_step_hits {n c₃ c₁ : ℕ} (hn : 12 ≤ n) (h1 : c₁ % n ≠ 0) {i : ℕ} (hi1 : 1 ≤ i) (hi4 : i ≤ 4)
    (h : OnOrbit n c₃ c₁ i 0) : ∃ k < n, inP n ((c₃ * k) % n) ((c₁ * k) % n) = true := by
  classical
  have hn0 : 0 < n := by omega
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨z₀, h3, h1'⟩ := step_of_onOrbit hn0 h
  push_cast at h3 h1'
  set g := Nat.gcd c₁ n with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ hn0
  have hgn : g ∣ n := Nat.gcd_dvd_right _ _
  have hg1 : g ∣ c₁ := Nat.gcd_dvd_left _ _
  have hg2 : 2 * g ≤ n := by
    obtain ⟨q, hq⟩ := hgn
    have hq2 : 2 ≤ q := by
      rcases Nat.lt_or_ge q 2 with hq2 | hq2
      · interval_cases q
        · omega
        · exfalso; apply h1; rw [hq, mul_one] at *; exact Nat.mod_eq_zero_of_dvd hg1
      · exact hq2
    nlinarith
  -- the height y = s·g ∈ [n/3, 2n/3]
  obtain ⟨s, hs1, hsmin, hs2⟩ := walk (X := 0) (L := n) hgpos
  have hy1 : n ≤ 3 * (s * g) := by simpa using hs1
  have hy2 : 3 * (s * g) ≤ 2 * n := by
    rcases hs2 with h0 | h0
    · subst h0; simp at hs1; omega
    · by_cases hbig : n ≤ 3 * g
      · have : ¬ (1 < s) := fun h' => by have := hsmin 1 h'; simp at this; omega
        have hs1' : s = 1 := by
          rcases Nat.lt_or_ge s 2 with h'' | h''
          · interval_cases s <;> simp_all
          · omega
        subst hs1'; omega
      · simp at h0; omega
  set y := s * g with hy
  have hyn : y < n := by omega
  have hbez : (g : ZMod n) = (c₁ : ZMod n) * (Nat.gcdA c₁ n : ZMod n) := by
    have := Nat.gcd_eq_gcd_ab c₁ n
    have h' : ((g : ℤ) : ZMod n) = ((c₁ * Nat.gcdA c₁ n + n * Nat.gcdB c₁ n : ℤ) : ZMod n) := by
      rw [hg, this]
    push_cast at h'; rw [ZMod.natCast_self, zero_mul, add_zero] at h'; exact h'
  set zA : ℤ := (s : ℤ) * Nat.gcdA c₁ n with hzA
  set X : ℕ := ((zA : ZMod n) * c₃).val with hX
  have hXn : X < n := ZMod.val_lt _
  -- walk x into [n/3, 2n/3]
  obtain ⟨t, ht⟩ : ∃ t, n ≤ 3 * ((X + t * i) % n) ∧ 3 * ((X + t * i) % n) ≤ 2 * n := by
    by_cases hA : n ≤ 3 * X ∧ 3 * X ≤ 2 * n
    · exact ⟨0, by simpa [Nat.mod_eq_of_lt hXn] using hA⟩
    · rcases Nat.lt_or_ge (3 * X) n with hB | hB
      · obtain ⟨t, ht1, -, ht2⟩ := walk (X := X) (L := n) (i := i) (by omega)
        rcases ht2 with h0 | h0
        · subst h0; simp at ht1; omega
        · have hlt : X + t * i < n := by omega
          refine ⟨t, ?_, ?_⟩ <;> rw [Nat.mod_eq_of_lt hlt] <;> omega
      · obtain ⟨t, ht1, -, ht2⟩ := walk (X := X) (L := 4 * n) (i := i) (by omega)
        rcases ht2 with h0 | h0
        · subst h0; simp at ht1; omega
        · have hrng : n ≤ X + t * i ∧ X + t * i < 2 * n := by omega
          have hm : (X + t * i) % n = X + t * i - n := by
            rw [Nat.mod_eq_sub_mod hrng.1, Nat.mod_eq_of_lt (by omega)]
          refine ⟨t, ?_, ?_⟩ <;> rw [hm] <;> omega
  set x := (X + t * i) % n with hx
  have hmem := zsmul_mem_orbit n c₃ c₁ (zA + (t : ℤ) * z₀)
  have e : (((zA + (t : ℤ) * z₀ : ℤ) : ZMod n) * c₃, ((zA + (t : ℤ) * z₀ : ℤ) : ZMod n) * c₁) =
      ((x : ZMod n), (y : ZMod n)) := by
    have hXc : ((X : ℕ) : ZMod n) = (zA : ZMod n) * c₃ := by rw [hX]; exact ZMod.natCast_zmod_val _
    have ex : ((x : ℕ) : ZMod n) = (X : ZMod n) + t * i := by rw [hx, ZMod.natCast_mod]; push_cast; ring
    refine Prod.ext ?_ ?_
    · show ((zA + (t : ℤ) * z₀ : ℤ) : ZMod n) * c₃ = (x : ZMod n)
      rw [ex, hXc]; push_cast; rw [add_mul, mul_assoc, h3]
    · show ((zA + (t : ℤ) * z₀ : ℤ) : ZMod n) * c₁ = (y : ZMod n)
      rw [hy]; push_cast; rw [add_mul, mul_assoc (t : ZMod n), h1', mul_zero, add_zero, hzA]
      push_cast; rw [mul_assoc, mul_comm (Nat.gcdA c₁ n : ZMod n), ← hbez]
  rw [e] at hmem
  obtain ⟨k, hk, hkx, hky⟩ := point_of_mem hn0 (Nat.mod_lt _ hn0) hyn hmem
  refine ⟨k, hk, ?_⟩
  rw [hkx, hky]; simp only [inP, Bool.and_eq_true, decide_eq_true_eq]; omega

/-- **BHK §7's main route fails only on `G₄` and `G₇`, for every order.** An orbit `⟨(c₃, c₁)⟩ ⊂ (ℤ/n)²`
off the axes (`c₃, c₁ ≢ 0`) with `gcd(n, c₃, c₁) = 1` has a meeting time whose point lies in `P_{1/3}`
(so the main route works for every ratio `v₁/v₃ ≤ 1/3`), unless it is BHK's `G₄` or `G₇`. Order `n ≤ 35`:
`check_orbits`; `n ≥ 36`: the framework's two-dimensional global isolation `orbit_isolation_two_bhk`, its
box inside `P_{1/3}`, and the short steps: axis steps impossible, diagonal and horizontal steps hit, the rest
bounded (`short_step_bounded`). -/
theorem s7_main_route (n c₃ c₁ : ℕ) (hn : 2 ≤ n) (hg : Nat.gcd n (Nat.gcd c₃ c₁) = 1)
    (h3 : c₃ % n ≠ 0) (h1 : c₁ % n ≠ 0) (hx : isExc n (c₃ % n) (c₁ % n) = false) :
    ∃ k < n, inP n ((c₃ * k) % n) ((c₁ * k) % n) = true := by
  have hn0 : 0 < n := by omega
  rcases Nat.lt_or_ge n 36 with hsmall | hbig
  · -- the finite check, on residues
    have hg' : Nat.gcd (Nat.gcd (c₃ % n) (c₁ % n)) n = 1 := by
      set d := Nat.gcd (Nat.gcd (c₃ % n) (c₁ % n)) n
      have hdn : d ∣ n := Nat.gcd_dvd_right _ _
      have hd3 : d ∣ c₃ := (Nat.dvd_mod_iff hdn).mp ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _))
      have hd1 : d ∣ c₁ := (Nat.dvd_mod_iff hdn).mp ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _))
      exact Nat.dvd_one.mp (hg ▸ Nat.dvd_gcd hdn (Nat.dvd_gcd hd3 hd1))
    rcases orbit_hits_or_exc hn (by omega) (by omega) (Nat.mod_lt _ hn0) (by omega) (Nat.mod_lt _ hn0) hg'
      with h | ⟨k, hk, hk'⟩
    · rw [hx] at h; exact absurd h (by simp)
    · refine ⟨k, hk, ?_⟩; rwa [Nat.mod_mul_mod, Nat.mod_mul_mod] at hk'
  · rcases orbit_isolation_two_bhk n c₃ c₁ (by omega) hg with
      ⟨k, hk, a1, a2, b1, b2⟩ | ⟨i, j, hne, hon, hi0, hi4, hj1, hj2, -, hineq, -, -⟩
    · exact ⟨k, hk, by simp only [inP, Bool.and_eq_true, decide_eq_true_eq]; omega⟩
    · have h3' : (c₃ : ZMod n) ≠ 0 := natCast_zmod_ne_zero h3
      have h1' : (c₁ : ZMod n) ≠ 0 := natCast_zmod_ne_zero h1
      by_cases hi : i = 0
      · subst hi
        have hj : j = 1 ∨ j = -1 := by
          have : j ≠ 0 := fun h => hne (by simp [h])
          omega
        exact absurd (axis_step_c3 hn0 hj hon) h3'
      by_cases hj : j = 0
      · subst hj
        by_cases hi1 : i = 1
        · subst hi1; exact absurd (axis_step_c1 hn0 hon) h1'
        · obtain ⟨i', rfl⟩ : ∃ i' : ℕ, i = i' := ⟨i.toNat, by omega⟩
          exact horiz_step_hits (by omega) h1 (by omega) (by omega) hon
      by_cases hd : i = 1 ∧ (j = 1 ∨ j = -1)
      · obtain ⟨rfl, hj'⟩ := hd
        exact diag_step_hits hn hj' hon
      · have hb := short_step_bounded (n := (n : ℝ)) (by exact_mod_cast hbig) hi0 hi4 hj1 hj2 hi hj hd
        linarith




/-- **The main route.** At a meeting time `t` where runners 2 and 3 read `x ∈ [1/6, 5/6]` and runner 1 reads
`y`, with `(x, y)` in BHK's parallelogram at ratio `v₁/v₃`, runners 1–3 are clear across runner 3's whole
clear lap `[t − (x − 1/6)/v₃, t + (5/6 − x)/v₃]` (length `2/(3v₃)`), and `window_two_uniform` finds an instant
in it where runners 4 and 5 are clear too. -/
theorem main_route_lonely {v₁ v₂ v₃ a b t x y : ℝ} {p q r : ℤ} (h1 : 0 < v₁) (h12 : v₁ < v₂)
    (h23 : v₂ < v₃) (h3a : v₃ < a) (hab : a < b) (hx1 : 1 / 6 ≤ x) (hx2 : x ≤ 5 / 6)
    (hyl : 1 / 6 ≤ y - v₁ * (x - 1 / 6) / v₃) (hyu : y + v₁ * (5 / 6 - x) / v₃ ≤ 5 / 6)
    (hp : v₁ * t = p + y) (hq : v₂ * t = q + x) (hr : v₃ * t = r + x) :
    ∃ s, Lonely5 v₁ v₂ v₃ a b s := by
  have h2 : 0 < v₂ := by linarith
  have h3 : 0 < v₃ := by linarith
  have ha : 0 < a := by linarith
  have hlen : 2 / (3 * a) ≤ 2 / (3 * v₃) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity); linarith
  obtain ⟨s, hs0, hs1, h4, h5⟩ :=
    window_two_uniform (J₀ := t - (x - 1 / 6) / v₃) (ℓ := 2 / (3 * v₃)) ha hab.le hlen
  obtain ⟨δ, rfl⟩ : ∃ δ, s = t + δ := ⟨s - t, by ring⟩
  have hdl : -((x - 1 / 6) / v₃) ≤ δ := by linarith
  have hdu : δ ≤ (5 / 6 - x) / v₃ := by
    have e : 2 / (3 * v₃) - (x - 1 / 6) / v₃ = (5 / 6 - x) / v₃ := by field_simp; ring
    linarith
  have m3l : -(x - 1 / 6) ≤ v₃ * δ := by
    have := mul_le_mul_of_nonneg_left hdl h3.le
    rwa [show v₃ * -((x - 1 / 6) / v₃) = -(x - 1 / 6) by field_simp] at this
  have m3u : v₃ * δ ≤ 5 / 6 - x := by
    have := mul_le_mul_of_nonneg_left hdu h3.le
    rwa [show v₃ * ((5 / 6 - x) / v₃) = 5 / 6 - x by field_simp] at this
  have m1l : -(v₁ * (x - 1 / 6) / v₃) ≤ v₁ * δ := by
    have := mul_le_mul_of_nonneg_left hdl h1.le
    rwa [show v₁ * -((x - 1 / 6) / v₃) = -(v₁ * (x - 1 / 6) / v₃) by ring] at this
  have m1u : v₁ * δ ≤ v₁ * (5 / 6 - x) / v₃ := by
    have := mul_le_mul_of_nonneg_left hdu h1.le
    rwa [show v₁ * ((5 / 6 - x) / v₃) = v₁ * (5 / 6 - x) / v₃ by ring] at this
  have hA : 0 ≤ v₁ * (x - 1 / 6) / v₃ := by apply div_nonneg _ h3.le; nlinarith
  have hB : 0 ≤ v₁ * (5 / 6 - x) / v₃ := by apply div_nonneg _ h3.le; nlinarith
  rcases le_total 0 δ with hd | hd
  · have a1 : 0 ≤ v₁ * δ := mul_nonneg h1.le hd
    have a2 : 0 ≤ v₂ * δ := mul_nonneg h2.le hd
    have a23 : v₂ * δ ≤ v₃ * δ := mul_le_mul_of_nonneg_right h23.le hd
    exact ⟨t + δ, clear_shift hp (by linarith) (by linarith), clear_shift hq (by linarith) (by linarith),
      clear_shift hr (by linarith) (by linarith), h4, h5⟩
  · have a1 : v₁ * δ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1.le hd
    have a2 : v₂ * δ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h2.le hd
    have a23 : v₃ * δ ≤ v₂ * δ := mul_le_mul_of_nonpos_right h23.le hd
    exact ⟨t + δ, clear_shift hp (by linarith) (by linarith), clear_shift hq (by linarith) (by linarith),
      clear_shift hr (by linarith) (by linarith), h4, h5⟩

/-- `N/n = ⌊N/n⌋ + (N mod n)/n`. -/
theorem div_split (N n : ℕ) (hn : 0 < n) : (N : ℝ) / n = (((N / n : ℕ) : ℤ) : ℝ) + ((N % n : ℕ) : ℝ) / n := by
  have hnR : (n : ℝ) ≠ 0 := by positivity
  have h : (N : ℝ) = n * ((N / n : ℕ) : ℝ) + ((N % n : ℕ) : ℝ) := by exact_mod_cast (Nat.div_add_mod N n).symm
  rw [Int.cast_natCast, h]; field_simp

set_option maxHeartbeats 1600000 in
/-- **BHK §7 natively, from the speeds.** Whole-number speeds `0 < v₁ < v₂ < v₃ < v₄ < v₅` with `3 v₁ < v₃`
and `D = v₃ − v₂` dividing neither `v₁` nor `v₃` (BHK §7) have a lonely instant. The meeting-time orbit has
order `n = D/g`, `g = gcd(D, v₃, v₁)`; off `G₄`/`G₇`, `s7_main_route` gives a meeting time with its point in the
parallelogram and `main_route_lonely` the instant; `G₄` and `G₇` by `g4_nat`, `g7_nat`, or (for `G₄` with
`v₃ ≥ 4 v₁`) the main route through the orbit point `(1/2, 1/4)`. -/
theorem s7_lonely {v₁ v₂ v₃ v₄ v₅ : ℕ} (h1 : 0 < v₁) (h12 : v₁ < v₂) (h23 : v₂ < v₃) (h34 : v₃ < v₄)
    (h45 : v₄ < v₅) (h13 : 3 * v₁ < v₃) (hD1 : ¬ (v₃ - v₂) ∣ v₁) (hD3 : ¬ (v₃ - v₂) ∣ v₃) :
    ∃ s, Lonely5 v₁ v₂ v₃ v₄ v₅ s := by
  set D := v₃ - v₂ with hDdef
  have hDpos : 0 < D := by omega
  set g := Nat.gcd D (Nat.gcd v₃ v₁) with hgdef
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hDpos
  have hgD : g ∣ D := Nat.gcd_dvd_left _ _
  have hg3 : g ∣ v₃ := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  have hg1 : g ∣ v₁ := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  obtain ⟨n, hn⟩ := hgD
  obtain ⟨c₃, hc3⟩ := hg3
  obtain ⟨c₁, hc1⟩ := hg1
  have hcop : Nat.gcd n (Nat.gcd c₃ c₁) = 1 := by
    set d := Nat.gcd n (Nat.gcd c₃ c₁)
    have e1 : g * d ∣ D := hn ▸ Nat.mul_dvd_mul_left g (Nat.gcd_dvd_left _ _)
    have e3 : g * d ∣ v₃ := hc3 ▸ Nat.mul_dvd_mul_left g ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _))
    have e4 : g * d ∣ v₁ := hc1 ▸ Nat.mul_dvd_mul_left g ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _))
    have : g * d ∣ g * 1 := by rw [mul_one]; exact Nat.dvd_gcd e1 (Nat.dvd_gcd e3 e4)
    exact Nat.dvd_one.mp (Nat.dvd_of_mul_dvd_mul_left hgpos this)
  have hnpos : 0 < n := by rcases Nat.eq_zero_or_pos n with h | h <;> [simp [h] at hn; exact h] <;> omega
  have h3' : c₃ % n ≠ 0 := fun h => hD3 (by
    rw [hn, hc3]; exact Nat.mul_dvd_mul_left g (Nat.dvd_of_mod_eq_zero h))
  have h1' : c₁ % n ≠ 0 := fun h => hD1 (by
    rw [hn, hc1]; exact Nat.mul_dvd_mul_left g (Nat.dvd_of_mod_eq_zero h))
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · exfalso; interval_cases n; exact h1' (Nat.mod_one _)
    · exact h
  have hgR : (0 : ℝ) < g := by exact_mod_cast hgpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hDR : ((v₂ : ℕ) : ℝ) = v₃ - g * n := by
    have : v₃ = v₂ + g * n := by omega
    have : ((v₃ : ℕ) : ℝ) = v₂ + g * n := by exact_mod_cast this
    linarith
  have h1R : (0 : ℝ) < v₁ := by exact_mod_cast h1
  have h12R : (v₁ : ℝ) < v₂ := by exact_mod_cast h12
  have h23R : (v₂ : ℝ) < v₃ := by exact_mod_cast h23
  have h34R : (v₃ : ℝ) < v₄ := by exact_mod_cast h34
  have h45R : (v₄ : ℝ) < v₅ := by exact_mod_cast h45
  have h13R : 3 * (v₁ : ℝ) < v₃ := by exact_mod_cast h13
  by_cases hE : isExc n (c₃ % n) (c₁ % n) = true
  · simp only [isExc, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hE
    rcases hE with ⟨⟨hn4, hm3⟩, hm1⟩ | ⟨⟨hn7, hn0⟩, hm⟩
    · subst hn4
      have hm3' : c₃ % 4 = 2 := by omega
      have hm1' : c₁ % 4 = 1 ∨ c₁ % 4 = 3 := by omega
      by_cases hv : v₃ < 4 * v₁
      · exact g4_nat h1 h12 h23 h34 h45 h13 hv hgpos (by omega) (by rw [hc3]) (by rw [hc1]) hm3' hm1'
      · push Not at hv
        obtain ⟨k, hk1, hk3⟩ : ∃ k : ℕ, (c₁ * k) % 4 = 1 ∧ (c₃ * k) % 4 = 2 := by
          rcases hm1' with h | h
          · exact ⟨1, by omega, by omega⟩
          · exact ⟨3, by rw [Nat.mul_mod, h], by rw [Nat.mul_mod, hm3']⟩
        set t : ℝ := (k : ℝ) / (4 * g) with ht
        have r1 : (v₁ : ℝ) * t = ((c₁ * k / 4 : ℕ) : ℤ) + 1 / 4 := by
          have : (v₁ : ℝ) * t = ((c₁ * k : ℕ) : ℝ) / 4 := by rw [ht, hc1]; push_cast; field_simp
          rw [this, div_four_split (c₁ * k) (c₁ * k / 4) 1 (by omega)]; norm_num
        have r3 : (v₃ : ℝ) * t = ((c₃ * k / 4 : ℕ) : ℤ) + 1 / 2 := by
          have : (v₃ : ℝ) * t = ((c₃ * k : ℕ) : ℝ) / 4 := by rw [ht, hc3]; push_cast; field_simp
          rw [this, div_four_split (c₃ * k) (c₃ * k / 4) 2 (by omega)]; norm_num
        have r2 : (v₂ : ℝ) * t = (((c₃ * k / 4 : ℕ) : ℤ) - (k : ℤ) : ℤ) + 1 / 2 := by
          have e2 : (v₂ : ℝ) * t = (v₃ : ℝ) * t - k := by rw [hDR, ht]; field_simp; ring
          rw [e2, r3]; push_cast; ring
        have hvR : 4 * (v₁ : ℝ) ≤ v₃ := by exact_mod_cast hv
        have hq : (v₁ : ℝ) * (1 / 2 - 1 / 6) / v₃ ≤ 1 / 12 := by
          rw [div_le_iff₀ (by linarith)]; nlinarith
        exact main_route_lonely h1R h12R h23R h34R h45R (by norm_num) (by norm_num)
          (by linarith) (by nlinarith) r1 r2 r3
    · subst hn7
      exact g7_nat h1 h12 h23 h34 h45 h13 hgpos (by omega) (by rw [hc3]) (by rw [hc1]) (by omega)
        (by rw [Nat.mul_mod]; omega)
  · have hE' : isExc n (c₃ % n) (c₁ % n) = false := by simpa using hE
    obtain ⟨k, hk, hP⟩ := s7_main_route n c₃ c₁ hn2 hcop h3' h1' hE'
    simp only [inP, Bool.and_eq_true, decide_eq_true_eq] at hP
    obtain ⟨⟨⟨p1, p2⟩, p3⟩, p4⟩ := hP
    set X := (c₃ * k) % n with hX
    set Y := (c₁ * k) % n with hY
    set t : ℝ := (k : ℝ) / (g * n) with ht
    have r3 : (v₃ : ℝ) * t = ((c₃ * k / n : ℕ) : ℤ) + (X : ℝ) / n := by
      have : (v₃ : ℝ) * t = ((c₃ * k : ℕ) : ℝ) / n := by rw [ht, hc3]; push_cast; field_simp
      rw [this, div_split _ _ hnpos]
    have r1 : (v₁ : ℝ) * t = ((c₁ * k / n : ℕ) : ℤ) + (Y : ℝ) / n := by
      have : (v₁ : ℝ) * t = ((c₁ * k : ℕ) : ℝ) / n := by rw [ht, hc1]; push_cast; field_simp
      rw [this, div_split _ _ hnpos]
    have r2 : (v₂ : ℝ) * t = (((c₃ * k / n : ℕ) : ℤ) - (k : ℤ) : ℤ) + (X : ℝ) / n := by
      have e2 : (v₂ : ℝ) * t = (v₃ : ℝ) * t - k := by rw [hDR, ht]; field_simp <;> ring
      rw [e2, r3]; push_cast; ring
    have q1 : (n : ℝ) ≤ 6 * X := by exact_mod_cast p1
    have q2 : 6 * (X : ℝ) ≤ 5 * n := by exact_mod_cast p2
    have q3 : 6 * (X : ℝ) + 2 * n ≤ 18 * Y := by exact_mod_cast p3
    have q4 : 18 * (Y : ℝ) ≤ 10 * n + 6 * X := by exact_mod_cast p4
    set x : ℝ := (X : ℝ) / n with hx
    set y : ℝ := (Y : ℝ) / n with hy
    have hx1 : 1 / 6 ≤ x := by rw [hx, le_div_iff₀ hnR]; linarith
    have hx2 : x ≤ 5 / 6 := by rw [hx, div_le_iff₀ hnR]; linarith
    have hyl0 : x / 3 + 1 / 9 ≤ y := by
      have e : y - (x / 3 + 1 / 9) = (18 * (Y : ℝ) - (6 * X + 2 * n)) / (18 * n) := by
        rw [hx, hy]; field_simp <;> ring
      have : 0 ≤ (18 * (Y : ℝ) - (6 * X + 2 * n)) / (18 * n) := div_nonneg (by linarith) (by positivity)
      linarith
    have hyu0 : y ≤ 5 / 9 + x / 3 := by
      have e : 5 / 9 + x / 3 - y = ((10 * n + 6 * X) - 18 * (Y : ℝ)) / (18 * n) := by
        rw [hx, hy]; field_simp <;> ring
      have : 0 ≤ ((10 * n + 6 * X) - 18 * (Y : ℝ)) / (18 * n) := div_nonneg (by linarith) (by positivity)
      linarith
    have hv3 : (0 : ℝ) < v₃ := by linarith
    have ha : (v₁ : ℝ) * (x - 1 / 6) / v₃ ≤ (x - 1 / 6) / 3 := by
      rw [div_le_div_iff₀ hv3 (by norm_num)]
      have := mul_le_mul_of_nonneg_left h13R.le (show (0 : ℝ) ≤ x - 1 / 6 by linarith)
      linarith
    have hb : (v₁ : ℝ) * (5 / 6 - x) / v₃ ≤ (5 / 6 - x) / 3 := by
      rw [div_le_div_iff₀ hv3 (by norm_num)]
      have := mul_le_mul_of_nonneg_left h13R.le (show (0 : ℝ) ≤ 5 / 6 - x by linarith)
      linarith
    have hyl : 1 / 6 ≤ y - (v₁ : ℝ) * (x - 1 / 6) / v₃ := by linarith
    have hyu : y + (v₁ : ℝ) * (5 / 6 - x) / v₃ ≤ 5 / 6 := by linarith
    exact main_route_lonely (a := (v₄ : ℝ)) (b := (v₅ : ℝ)) h1R h12R h23R h34R h45R hx1 hx2 hyl hyu r1 r2 r3

/-- `circDist` is unchanged by a whole-number shift. -/
theorem circDist_add_intCast' (x : ℝ) (k : ℤ) : circDist (x + k) = circDist x := by
  unfold circDist; rw [Int.fract_add_intCast]

/-- **BHK §7, native route, in the dispatch's form.** Same hypotheses and conclusion as `S7.lonely_7`:
`s7_lonely` gives an instant; a whole number of laps added makes it positive without moving any reading. -/
theorem lonely_7_native {v1 v2 v3 v4 v5 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3)
    (h34 : v3 < v4) (h45 : v4 < v5) (hsmall : 3 * v1 < v3)
    (hD3 : ¬ (v3 - v2) ∣ v3) (hD1 : ¬ (v3 - v2) ∣ v1) :
    ∃ t : ℝ, 0 < t ∧ LRC.OrderSixN.Lonely6 v1 v2 v3 v4 v5 t := by
  obtain ⟨s, a1, a2, a3, a4, a5⟩ := s7_lonely h0 h12 h23 h34 h45 hsmall hD1 hD3
  obtain ⟨m, hm⟩ := exists_nat_gt (-s)
  have key : ∀ v : ℕ, circDist ((v : ℝ) * (s + ((m + 1 : ℕ) : ℝ))) = circDist ((v : ℝ) * s) := by
    intro v
    have e : (v : ℝ) * (s + ((m + 1 : ℕ) : ℝ)) = (v : ℝ) * s + ((v * (m + 1) : ℕ) : ℤ) := by push_cast; ring
    rw [e, circDist_add_intCast']
  refine ⟨s + ((m + 1 : ℕ) : ℝ), by push_cast; linarith, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [key, one_div] <;> assumption

end LRC.S7Native
