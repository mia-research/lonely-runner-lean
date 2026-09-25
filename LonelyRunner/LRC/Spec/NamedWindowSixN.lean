import LonelyRunner.LRC.Spec.WindowTwoN

/-!
# A window where runners 1–3 are clear, with the lonely instant named

2026-09-24.  BHK close their exceptional groups `G₄` and `G₇` (§7) by contradiction: if no
lonely time existed, a window on which runners 1–3 are clear (a "123-gap") would be covered by the
blocked zones of runners 4 and 5, which forces bounds under which `t = 2/(3v₃)` is lonely.  Here
the same window gives the instant directly (`lonely_of_123_window`):

1. window at least `2/(3v₄)` long: the two-flank window rule names it;
2. otherwise follow runner 4's clear stretches in the window; one at least `1/(3v₅)` long holds
   a named instant where runner 5 is clear too (its start, or runner 5's next opening);
3. otherwise runner 5 is read at named points: the window's ends, its opening after the start,
   its closing before the end.  If all four are blocked, whole-number block counting forces
   `2v₄ < v₅` and `7v₅ < 16v₃`, and `t = 2/(3v₃)` is lonely.

Every branch ends at a named instant.  No `by_contra` over time.

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option linter.style.longLine false

namespace LRC.OrderSixN

open MomentIterationN LRC.SpecN ConstructionN

/-- Clear at `1/6` means the reading sits in the band `[⌊x⌋ + 1/6, ⌊x⌋ + 5/6]`. -/
theorem band_of_clear_six {x : ℝ} (h : (6 : ℝ)⁻¹ ≤ circDist x) :
    (⌊x⌋ : ℝ) + 6⁻¹ ≤ x ∧ x ≤ (⌊x⌋ : ℝ) + 5 / 6 := by
  unfold circDist at h
  have h1 := le_trans h (min_le_left _ _)
  have h2 := le_trans h (min_le_right _ _)
  have hx := Int.floor_add_fract x
  constructor <;> linarith

/-- **A stretch as long as a block holds a clear instant**, named: the stretch's start, or the
runner's next opening. -/
theorem clear_in_stretch {f p q : ℝ} (hf : 0 < f) (hlen : 1 / (3 * f) ≤ q - p) :
    ∃ t, p ≤ t ∧ t ≤ q ∧ (6 : ℝ)⁻¹ ≤ circDist (f * t) := by
  by_cases hp : (6 : ℝ)⁻¹ ≤ circDist (f * p)
  · have : 0 < 1 / (3 * f) := by positivity
    exact ⟨p, le_rfl, by linarith, hp⟩
  push Not at hp
  obtain ⟨K, hK1, hK2⟩ := zone_of_blocked_six hp
  refine ⟨((K : ℝ) + 6⁻¹) / f, ?_, ?_, clear_at_opening_six hf K⟩
  · rw [le_div_iff₀ hf]; linarith [mul_comm f p]
  · have hq : 1 / 3 ≤ f * q - f * p := by
      have := mul_le_mul_of_nonneg_left hlen hf.le
      rw [show f * (1 / (3 * f)) = 1 / 3 by field_simp] at this
      linarith [mul_sub f q p]
    rw [div_le_iff₀ hf]; linarith [mul_comm f q, mul_comm f p]

/-- Clear at a closing: `(K − 1/6)/f` reads `K − 1/6`. -/
theorem clear_at_closing_six {f : ℝ} (hf : 0 < f) (K : ℤ) :
    (6 : ℝ)⁻¹ ≤ circDist (f * (((K : ℝ) - 6⁻¹) / f)) := by
  rw [mul_div_cancel₀ _ hf.ne']
  refine clear_of_band_six (K - 1) ?_ ?_ <;> push_cast <;> linarith

set_option maxHeartbeats 1000000 in
/-- **The 123-window, lonely at a named instant.**  If runners 1–3 are clear on `[A, B]`, the
window is longer than `7/(12v₃)`, and after runner 3's lap there is room for a runner-5 block
(`1/(3v₅) ≤ B − A − 1/(3v₃)`), the five runners are lonely together at a named instant. -/
theorem lonely_of_123_window {v1 v2 v3 v4 v5 : ℝ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3)
    (h34 : v3 < v4) (h45 : v4 < v5) (h41 : v3 < 4 * v1) {A B : ℝ}
    (hL : 7 / (12 * v3) < B - A) (htail : 1 / (3 * v5) ≤ B - A - 1 / (3 * v3))
    (h123 : ∀ t, A ≤ t → t ≤ B →
      (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧
        (6 : ℝ)⁻¹ ≤ circDist (v3 * t)) :
    ∃ t, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧
        (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  have p3 : 0 < v3 := by linarith
  have p4 : 0 < v4 := by linarith
  have p5 : 0 < v5 := by linarith
  have b35 : 0 < 1 / (3 * v5) := by positivity
  have b3 : 0 < 1 / (3 * v3) := by positivity
  have b43 : 1 / (3 * v4) < 1 / (3 * v3) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]; linarith
  have b54 : 1 / (3 * v5) < 1 / (3 * v4) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]; linarith
  -- inside the window, runners 4 and 5 clear together is enough
  have fin : ∀ t, A ≤ t → t ≤ B → (6 : ℝ)⁻¹ ≤ circDist (v4 * t) →
      (6 : ℝ)⁻¹ ≤ circDist (v5 * t) →
      ∃ t, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧
        (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧
          (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := fun t h1 h2 c4 c5 =>
    let ⟨a1, a2, a3⟩ := h123 t h1 h2
    ⟨t, a1, a2, a3, c4, c5⟩
  -- a runner-4 clear stretch as long as a runner-5 block holds the instant
  have stretch : ∀ p q, A ≤ p → q ≤ B → 1 / (3 * v5) ≤ q - p →
      (∀ t, p ≤ t → t ≤ q → (6 : ℝ)⁻¹ ≤ circDist (v4 * t)) →
      ∃ t, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧
        (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧
          (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
    intro p q hp hq hlen h4
    obtain ⟨t, h1, h2, c5⟩ := clear_in_stretch p5 hlen
    exact fin t (by linarith) (by linarith) (h4 t h1 h2) c5
  -- 1. a window as long as runner 4's clear lap: the two-flank window rule
  by_cases hlong : 2 / (3 * v4) ≤ B - A
  · obtain ⟨t, h1, h2, c4, c5, -⟩ := two_flank_window p4 h45 A hlong
    exact fin t h1 (by linarith) c4 c5
  push Not at hlong
  have h48 : 7 * v4 < 8 * v3 := by
    have := lt_trans hL hlong
    rw [div_lt_div_iff₀ (by positivity) (by positivity)] at this; linarith
  -- the instant `2/(3v₃)`, under the bounds block counting forces
  have fallback : 2 * v4 < v5 → 7 * v5 < 16 * v3 →
      ∃ t, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧
        (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧
          (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
    intro ha hb
    have r : ∀ v : ℝ, v * (2 / (3 * v3)) = 2 * v / (3 * v3) := fun v => by ring
    have band : ∀ (v : ℝ) (k : ℤ), ((k : ℝ) + 6⁻¹) * (3 * v3) ≤ 2 * v →
        2 * v ≤ ((k : ℝ) + 5 / 6) * (3 * v3) → (6 : ℝ)⁻¹ ≤ circDist (v * (2 / (3 * v3))) := by
      intro v k hlo hhi
      rw [r]
      exact clear_of_band_six k (by rw [le_div_iff₀ (by positivity)]; linarith)
        (by rw [div_le_iff₀ (by positivity)]; linarith)
    refine ⟨2 / (3 * v3), band v1 0 ?_ ?_, band v2 0 ?_ ?_, band v3 0 ?_ ?_, band v4 0 ?_ ?_,
      band v5 1 ?_ ?_⟩ <;> push_cast <;> linarith
  by_cases hA4 : (6 : ℝ)⁻¹ ≤ circDist (v4 * A)
  · -- 2. runner 4 clear at the start: its clear stretch `[A, P]`, block `[P, Q]`, stretch `[Q, B]`
    obtain ⟨hk1, hk2⟩ := band_of_clear_six hA4
    set k : ℤ := ⌊v4 * A⌋ with hk
    set P : ℝ := ((k : ℝ) + 5 / 6) / v4 with hP
    set Q : ℝ := ((k : ℝ) + 7 / 6) / v4 with hQ
    have eP : v4 * P = (k : ℝ) + 5 / 6 := by rw [hP]; field_simp
    have eQ : v4 * Q = (k : ℝ) + 7 / 6 := by rw [hQ]; field_simp
    have hPQ : Q - P = 1 / (3 * v4) := by rw [hP, hQ]; field_simp; ring
    have hAP : A ≤ P := by rw [hP, le_div_iff₀ p4]; linarith [mul_comm v4 A]
    have c4J1 : ∀ t, A ≤ t → t ≤ P → (6 : ℝ)⁻¹ ≤ circDist (v4 * t) :=
      fun t h1 h2 => clear_between_six p4 k hk1 eP.le h1 h2
    by_cases hPB : B ≤ P
    · exact stretch A B le_rfl le_rfl (by linarith)
        (fun t h1 h2 => c4J1 t h1 (le_trans h2 hPB))
    push Not at hPB
    by_cases hJ1 : 1 / (3 * v5) ≤ P - A
    · exact stretch A P le_rfl hPB.le hJ1 c4J1
    push Not at hJ1
    have hQB : Q < B := by
      by_contra h; push Not at h; linarith
    have hvB : v4 * B ≤ ((k + 1 : ℤ) : ℝ) + 5 / 6 := by
      have := mul_lt_mul_of_pos_left hlong p4
      rw [show v4 * (2 / (3 * v4)) = 2 / 3 by field_simp, mul_sub] at this
      push_cast; linarith
    have c4J2 : ∀ t, Q ≤ t → t ≤ B → (6 : ℝ)⁻¹ ≤ circDist (v4 * t) :=
      fun t h1 h2 => clear_between_six p4 (k + 1) (by push_cast; linarith) hvB h1 h2
    by_cases hJ2 : 1 / (3 * v5) ≤ B - Q
    · exact stretch Q B (by linarith) le_rfl hJ2 c4J2
    push Not at hJ2
    -- 3. runner 5 at named points: the ends, its opening after `A`, its closing before `B`
    by_cases hA5 : (6 : ℝ)⁻¹ ≤ circDist (v5 * A)
    · exact fin A le_rfl (by linarith) hA4 hA5
    push Not at hA5
    obtain ⟨k1, hk1a, hk1b⟩ := zone_of_blocked_six hA5
    by_cases ho1 : ((k1 : ℝ) + 6⁻¹) / v5 ≤ P
    · have hAo : A ≤ ((k1 : ℝ) + 6⁻¹) / v5 := by
        rw [le_div_iff₀ p5]; linarith [mul_comm v5 A]
      exact fin _ hAo (by linarith) (c4J1 _ hAo ho1) (clear_at_opening_six p5 k1)
    push Not at ho1
    by_cases hB5 : (6 : ℝ)⁻¹ ≤ circDist (v5 * B)
    · exact fin B (by linarith) le_rfl (c4J2 B hQB.le le_rfl) hB5
    push Not at hB5
    obtain ⟨k2, hk2a, hk2b⟩ := zone_of_blocked_six hB5
    by_cases hc2 : Q ≤ ((k2 : ℝ) - 6⁻¹) / v5
    · have hcB : ((k2 : ℝ) - 6⁻¹) / v5 ≤ B := by
        rw [div_le_iff₀ p5]; linarith [mul_comm v5 B]
      exact fin _ (by linarith) hcB (c4J2 _ hc2 hcB) (clear_at_closing_six p5 k2)
    push Not at hc2
    -- block counting in runner 5's units
    have o1P : (k1 : ℝ) + 6⁻¹ > v5 * P := by
      have := (lt_div_iff₀ p5).mp ho1; linarith [mul_comm v5 P]
    have c2Q : (k2 : ℝ) - 6⁻¹ < v5 * Q := by
      have := (div_lt_iff₀ p5).mp hc2; linarith [mul_comm v5 Q]
    have hQP5 : v5 * Q - v5 * P = v5 / (3 * v4) := by
      rw [← mul_sub, hPQ]; field_simp
    have hAB : v5 * A < v5 * B := mul_lt_mul_of_pos_left (by linarith) p5
    have hk12 : k1 ≤ k2 := by
      have : (k1 : ℝ) < k2 + 1 := by linarith
      exact_mod_cast Int.lt_add_one_iff.mp (by exact_mod_cast this)
    have hLv5 : 1 / 3 < v5 * B - v5 * A := by
      have := mul_lt_mul_of_pos_left (show 1 / (3 * v5) < B - A by linarith) p5
      rw [show v5 * (1 / (3 * v5)) = 1 / 3 by field_simp, mul_sub] at this; exact this
    rcases lt_trichotomy k2 (k1 + 1) with hlt | heq | hgt
    · -- one block across the window: too short
      have : k2 = k1 := by omega
      subst this; linarith
    · -- consecutive blocks: `2v₄ < v₅` and `7v₅ < 16v₃`
      have hk : (k2 : ℝ) = k1 + 1 := by exact_mod_cast heq
      apply fallback
      · have h23' : (2 : ℝ) / 3 < v5 / (3 * v4) := by linarith
        rw [div_lt_div_iff₀ (by norm_num) (by positivity)] at h23'; linarith
      · have hB : v5 * B - v5 * A < 4 / 3 := by linarith
        have h7 := mul_lt_mul_of_pos_left hL p5
        rw [mul_sub] at h7
        have : v5 * (7 / (12 * v3)) < 4 / 3 := by linarith
        rw [show v5 * (7 / (12 * v3)) = 7 * v5 / (12 * v3) by ring,
          div_lt_iff₀ (by positivity)] at this
        linarith
    · -- blocks two apart: `5v₄ < v₅`, and the window is too short
      have hk : (k1 : ℝ) + 2 ≤ k2 := by exact_mod_cast (show k1 + 2 ≤ k2 by omega)
      have h5 : 5 * v4 < v5 := by
        have h53 : (5 : ℝ) / 3 < v5 / (3 * v4) := by linarith
        rw [div_lt_div_iff₀ (by norm_num) (by positivity)] at h53; linarith
      have hsum : B - A < 2 / (3 * v5) + 1 / (3 * v4) := by
        have : 2 / (3 * v5) = 1 / (3 * v5) + 1 / (3 * v5) := by ring
        linarith
      have h1 : 2 / (3 * v5) < 2 / (15 * v4) := by
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]; linarith
      have h2 : 2 / (15 * v4) + 1 / (3 * v4) ≤ 7 / (12 * v3) := by
        rw [show 2 / (15 * v4) + 1 / (3 * v4) = 7 / (15 * v4) by field_simp; ring,
          div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      linarith
  · -- 2'. runner 4 blocked at the start: after its block, it is clear to the end
    push Not at hA4
    obtain ⟨k, hka, hkb⟩ := zone_of_blocked_six hA4
    set Q : ℝ := ((k : ℝ) + 6⁻¹) / v4 with hQ
    have eQ : v4 * Q = (k : ℝ) + 6⁻¹ := by rw [hQ]; field_simp
    have hAQ : A ≤ Q := by rw [hQ, le_div_iff₀ p4]; linarith [mul_comm v4 A]
    have hQA : Q - A < 1 / (3 * v4) := by
      have : v4 * Q - v4 * A < 1 / 3 := by linarith
      rw [← mul_sub] at this
      rw [lt_div_iff₀ (by positivity)]; linarith
    have hvB : v4 * B ≤ (k : ℝ) + 5 / 6 := by
      have := mul_lt_mul_of_pos_left hlong p4
      rw [show v4 * (2 / (3 * v4)) = 2 / 3 by field_simp, mul_sub] at this
      linarith
    exact stretch Q B hAQ le_rfl (by linarith)
      (fun t h1 h2 => clear_between_six p4 k eQ.ge hvB h1 h2)

end LRC.OrderSixN
