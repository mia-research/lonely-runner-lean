import LonelyRunner.LRC.Spec.OrderSixN

/-!
# The two-runner window lemma, and the window route to loneliness (n6_native, E38, E51)

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

end N6Native

#print axioms N6Native.window_two
#print axioms N6Native.window_two_uniform
#print axioms N6Native.lonely_of_window
