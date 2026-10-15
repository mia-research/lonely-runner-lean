import LonelyRunner.LRC.Spec.OrderSixN

/-!
# The two-runner window lemma, the window route, and BHK's exceptional orbits G₄, G₇ closed (n6_native, E38, E51, E53, E54)

Two runners with speeds `0 < a ≤ b`. Any window `[J₀, J₀ + ℓ]` with
`ℓ ≥ 1/(3a) + 1/(3b)` and `ℓ ≥ (m + 1/3)/b` for every integer `m` with `3 m a < a + b`
contains an instant at which both runners are clear (distance at least `1/6` from the nearest integer).

In runner-`a` laps (`ρ = b/a`) the threshold is `L(ρ) = max(1/3 + 1/(3ρ), (m* + 1/3)/ρ)` with `m*` the largest
integer below `(ρ+1)/3`; it is at most `2/3`, with equality at `ρ = 1` (`six_window_L_v2.out`: sharp on 237 ratios).

Proof: four candidate instants: runner `a`'s first clear point, runner `b`'s entry while `a` is clear, `a`'s
re-entry, and `b`'s next entry.
-/

namespace N6Native

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

end N6Native

#print axioms N6Native.window_two
#print axioms N6Native.window_two_uniform
#print axioms N6Native.lonely_of_window
#print axioms N6Native.g4_window
#print axioms N6Native.g7_window
#print axioms N6Native.g4_lonely
#print axioms N6Native.g7_lonely
#print axioms N6Native.g4_closed
#print axioms N6Native.g7_closed
#print axioms N6Native.g4_nat
#print axioms N6Native.g7_nat
