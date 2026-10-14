import LonelyRunner.LRC.Spec.ParityDescentTwoN

set_option linter.style.longLine false

/-!
# Two odd readings in different pair classes and two readings `≡ 2 (mod 4)` (order eight)

2026-10-05 (running log E402).  At the shifts `t = (τ + k)/8` an odd reading `e` blocks shifts
inside one pair `{x, x + e}` mod 8 (`odd_container`: two blocked shifts differ by `0` or `±e`, from
`blocked_step`), and a reading `≡ 2 (mod 4)` blocks shifts inside one class mod 4
(`two_mod_four_container`).  Two such pairs and two classes mod 4 cannot cover `ℤ/8` when the two odd
readings are not congruent to `±` each other mod 8, i.e. lie in different classes `{1, 7}`, `{3, 5}`
(`oott_core`, a finite check by `decide`).  So some shift is free at every `τ` (`free_shift_oott`), and
with the multiples of `8` and silenced readings `≡ 4 (mod 8)` from a mixed instant the set is lonely
(`lonely_eight_of_oott`).

Everything here is proved; no `sorry`, no `native_decide`.
-/


namespace LRC.ParityDescent

open ConstructionN LRC.Descent

/-- For an odd integer `w`, `8 ∣ w² − 1`. -/
theorem eight_dvd_sq_sub_one {w : ℤ} (hw : ¬ (2 : ℤ) ∣ w) : (8 : ℤ) ∣ w * w - 1 := by
  have h : w % 8 = 1 ∨ w % 8 = 3 ∨ w % 8 = 5 ∨ w % 8 = 7 := by omega
  have key : (w * w - 1) % 8 = 0 := by
    rcases h with h | h | h | h <;> simp [Int.sub_emod, Int.mul_emod, h]
  exact Int.dvd_of_emod_eq_zero key

/-- **Two blocked shifts of an odd reading differ by `0` or `±e` mod 8.** -/
theorem odd_blocked_rel {τ : ℝ} {e k₁ k₂ : ℕ} (he : ¬ 2 ∣ e) (hk₁ : k₁ < 8) (hk₂ : k₂ < 8)
    (h₁ : Blocked τ e k₁) (h₂ : Blocked τ e k₂) :
    k₁ = k₂ ∨ k₁ = (k₂ + e) % 8 ∨ k₂ = (k₁ + e) % 8 := by
  obtain ⟨w, hw⟩ := blocked_step h₁ h₂
  have he' : ¬ (2 : ℤ) ∣ (e : ℤ) := by exact_mod_cast he
  have hsq := eight_dvd_sq_sub_one he'
  obtain ⟨q, hq⟩ := hsq
  rw [abs_le] at hw
  set D : ℤ := (k₁ : ℤ) - k₂ with hD
  set σ : ℤ := (e : ℤ) * D - 8 * w with hσ
  have hσr : σ = -1 ∨ σ = 0 ∨ σ = 1 := by omega
  -- `D - σ·e = D·(1 - e²) + 8·w·e`, a multiple of 8
  have hkey : D - σ * (e : ℤ) = 8 * (w * (e : ℤ) - q * D) := by
    have : (e : ℤ) * (e : ℤ) = 8 * q + 1 := by linarith
    rw [hσ]; nlinarith [this]
  rcases hσr with h | h | h
  · rw [h] at hkey
    right; right; omega
  · rw [h] at hkey
    left; omega
  · rw [h] at hkey
    right; left; omega

/-- **An odd reading's blocked shifts lie in one pair `{x, x + e}` mod 8.** -/
theorem odd_container (τ : ℝ) {e : ℕ} (he : ¬ 2 ∣ e) :
    ∃ x, x < 8 ∧ ∀ k, k < 8 → Blocked τ e k → k = x ∨ k = (x + e) % 8 := by
  classical
  by_cases h : ∃ k₀, k₀ < 8 ∧ Blocked τ e k₀
  · obtain ⟨k₀, hk₀, hb₀⟩ := h
    by_cases h' : ∃ k₁, k₁ < 8 ∧ Blocked τ e k₁ ∧ (k₁ + e) % 8 = k₀
    · obtain ⟨k₁, hk₁, hb₁, hr⟩ := h'
      refine ⟨k₁, hk₁, fun k hk hb => ?_⟩
      rcases odd_blocked_rel he hk hk₀ hb hb₀ with h1 | h1 | h1
      · right; omega
      · exfalso
        rcases odd_blocked_rel he hk hk₁ hb hb₁ with h2 | h2 | h2 <;> omega
      · left; omega
    · push Not at h'
      refine ⟨k₀, hk₀, fun k hk hb => ?_⟩
      rcases odd_blocked_rel he hk hk₀ hb hb₀ with h1 | h1 | h1
      · left; exact h1
      · right; exact h1
      · exact absurd h1.symm (h' k hk hb)
  · push Not at h
    exact ⟨0, by norm_num, fun k hk hb => absurd hb (h k hk)⟩

/-- **A reading `≡ 2 (mod 4)` blocks shifts inside one class mod 4.** -/
theorem two_mod_four_rel {τ : ℝ} {e k₁ k₂ : ℕ} (he : e % 4 = 2)
    (h₁ : Blocked τ e k₁) (h₂ : Blocked τ e k₂) : k₁ % 4 = k₂ % 4 := by
  obtain ⟨w, hw⟩ := blocked_step h₁ h₂
  obtain ⟨v, hv, hev⟩ : ∃ v : ℕ, ¬ 2 ∣ v ∧ e = 2 * v := ⟨e / 2, by omega, by omega⟩
  set u : ℤ := (v : ℤ) * ((k₁ : ℤ) - k₂) with hu
  have hσ : (e : ℤ) * ((k₁ : ℤ) - k₂) - 8 * w = 2 * u - 8 * w := by rw [hu, hev]; push_cast; ring
  rw [hσ, abs_le] at hw
  have hzero : 2 * u - 8 * w = 0 := by omega
  have h4 : (4 : ℤ) ∣ ((k₁ : ℤ) - k₂) * (v : ℤ) := ⟨w, by rw [mul_comm]; rw [hu] at hzero; linarith⟩
  have hv' : ¬ (2 : ℤ) ∣ (v : ℤ) := by exact_mod_cast hv
  have hcop : IsCoprime (4 : ℤ) (v : ℤ) := by
    have h := (isCoprime_two_of_odd hv').pow_left (m := 2)
    norm_num at h
    exact h
  have hd : (4 : ℤ) ∣ ((k₁ : ℤ) - k₂) := hcop.dvd_of_dvd_mul_right h4
  omega

theorem two_mod_four_container (τ : ℝ) {e : ℕ} (he : e % 4 = 2) :
    ∃ c, c < 4 ∧ ∀ k, k < 8 → Blocked τ e k → k % 4 = c := by
  classical
  by_cases h : ∃ k₀, k₀ < 8 ∧ Blocked τ e k₀
  · obtain ⟨k₀, -, hb₀⟩ := h
    exact ⟨k₀ % 4, Nat.mod_lt _ (by norm_num), fun k _ hb => two_mod_four_rel he hb hb₀⟩
  · push Not at h
    exact ⟨0, by norm_num, fun k hk hb => absurd hb (h k hk)⟩

/-- **The finite core.**  Two pairs `{x, x + w}` and two classes mod 4 do not cover `ℤ/8` when the odd
residues `w₁, w₂` satisfy `w₂ ≢ ±w₁ (mod 8)`. -/
theorem oott_core_fin : ∀ w₁ w₂ : Fin 8, w₁.val % 2 = 1 → w₂.val % 2 = 1 → w₁ ≠ w₂ → w₁ + w₂ ≠ 0 →
    ∀ x₁ x₂ : Fin 8, ∀ c₁ c₂ : Fin 4,
      ∃ k : Fin 8, k ≠ x₁ ∧ k ≠ x₁ + w₁ ∧ k ≠ x₂ ∧ k ≠ x₂ + w₂ ∧
        k.val % 4 ≠ c₁.val ∧ k.val % 4 ≠ c₂.val := by
  decide

theorem oott_core : ∀ w₁, w₁ < 8 → ∀ w₂, w₂ < 8 → w₁ % 2 = 1 → w₂ % 2 = 1 → w₁ ≠ w₂ →
    (w₁ + w₂) % 8 ≠ 0 → ∀ x₁, x₁ < 8 → ∀ x₂, x₂ < 8 → ∀ c₁, c₁ < 4 → ∀ c₂, c₂ < 4 →
      ∃ k, k < 8 ∧ k ≠ x₁ ∧ k ≠ (x₁ + w₁) % 8 ∧ k ≠ x₂ ∧ k ≠ (x₂ + w₂) % 8 ∧
        k % 4 ≠ c₁ ∧ k % 4 ≠ c₂ := by
  intro w₁ hw₁ w₂ hw₂ h1 h2 hne hsum x₁ hx₁ x₂ hx₂ c₁ hc₁ c₂ hc₂
  have hne' : (⟨w₁, hw₁⟩ : Fin 8) ≠ ⟨w₂, hw₂⟩ := fun h => hne (congrArg Fin.val h)
  have hsum' : (⟨w₁, hw₁⟩ : Fin 8) + ⟨w₂, hw₂⟩ ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [Fin.val_add] at this
    exact hsum this
  obtain ⟨k, k1, k2, k3, k4, k5, k6⟩ := oott_core_fin ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ h1 h2 hne' hsum'
    ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩
  refine ⟨k.val, k.isLt, fun h => k1 (Fin.ext h), fun h => k2 (Fin.ext (by simp [Fin.val_add, h])),
    fun h => k3 (Fin.ext h), fun h => k4 (Fin.ext (by simp [Fin.val_add, h])), k5, k6⟩

/-- **A free shift for `(o, o, t, t)` with the odd readings in different classes.** -/
theorem free_shift_oott (τ : ℝ) {w₁ w₂ t₁ t₂ : ℕ} (hw₁ : ¬ 2 ∣ w₁) (hw₂ : ¬ 2 ∣ w₂)
    (ht₁ : t₁ % 4 = 2) (ht₂ : t₂ % 4 = 2) (hne : w₁ % 8 ≠ w₂ % 8) (hneg : (w₁ + w₂) % 8 ≠ 0) :
    ∃ k, k < 8 ∧ ¬ Blocked τ w₁ k ∧ ¬ Blocked τ w₂ k ∧ ¬ Blocked τ t₁ k ∧ ¬ Blocked τ t₂ k := by
  obtain ⟨x₁, hx₁, hX₁⟩ := odd_container τ hw₁
  obtain ⟨x₂, hx₂, hX₂⟩ := odd_container τ hw₂
  obtain ⟨c₁, hc₁, hC₁⟩ := two_mod_four_container τ ht₁
  obtain ⟨c₂, hc₂, hC₂⟩ := two_mod_four_container τ ht₂
  obtain ⟨k, hk, h1, h2, h3, h4, h5, h6⟩ := oott_core (w₁ % 8) (Nat.mod_lt _ (by norm_num))
    (w₂ % 8) (Nat.mod_lt _ (by norm_num)) (by omega) (by omega) hne (by omega) x₁ hx₁ x₂ hx₂ c₁ hc₁ c₂ hc₂
  refine ⟨k, hk, fun hb => ?_, fun hb => ?_, fun hb => h5 (hC₁ k hk hb), fun hb => h6 (hC₂ k hk hb)⟩
  · rcases hX₁ k hk hb with h | h
    · exact h1 h
    · exact h2 (by rw [h]; omega)
  · rcases hX₂ k hk hb with h | h
    · exact h3 h
    · exact h4 (by rw [h]; omega)

end LRC.ParityDescent

namespace LRC.OrderEightN

open ConstructionN LRC.Descent LRC.ParityDescent

/-- **The eighth level with a supplied free shift.**  If every offset leaves a shift free for the
non-multiples of `8` other than those `≡ 4 (mod 8)`, and a mixed instant clears the multiples' cofactors at
`1/8` and silences the readings `≡ 4 (mod 8)`, the set is lonely. -/
theorem lonely_eight_of_eighth_free {S : Finset ℕ}
    (hfree : ∀ τ : ℝ, ∃ k, k < 8 ∧ ∀ e ∈ S, ¬ 8 ∣ e → e % 8 ≠ 4 → ¬ Blocked τ e k)
    (hmix : ∃ τ : ℝ, 0 < τ ∧ (∀ m ∈ S, 8 ∣ m → (8 : ℝ)⁻¹ ≤ circDist (((m / 8 : ℕ) : ℝ) * τ)) ∧
      ∀ f ∈ S, f % 8 = 4 → (4 : ℝ)⁻¹ ≤ circDist (((f / 4 : ℕ) : ℝ) * τ)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  obtain ⟨τ, hτ, hM, hF⟩ := hmix
  obtain ⟨k, -, hk⟩ := hfree τ
  refine ⟨(τ + k) / 8, by positivity, fun d hd => ?_⟩
  by_cases h8 : 8 ∣ d
  · obtain ⟨c, rfl⟩ := h8
    have hc := hM (8 * c) hd (dvd_mul_right 8 c)
    rw [show 8 * c / 8 = c by omega] at hc
    have heq : ((8 * c : ℕ) : ℝ) * ((τ + k) / 8) = (c : ℝ) * τ + (((c * k : ℕ) : ℤ) : ℝ) := by
      push_cast; ring
    rw [heq, circDist_add_int]; exact hc
  · by_cases h4 : d % 8 = 4
    · obtain ⟨u, hu, hd4⟩ : ∃ u : ℕ, ¬ 2 ∣ u ∧ d = 4 * u := ⟨d / 4, by omega, by omega⟩
      have hf := hF d hd h4
      rw [hd4, show 4 * u / 4 = u by omega] at hf
      have hsil := silent_of_quarter hu (τ := τ) hf k
      unfold Blocked at hsil
      push Not at hsil
      have heq : (d : ℝ) * ((τ + k) / 8) = ((4 * u : ℕ) : ℝ) * τ / 8 + ((4 * u : ℕ) : ℝ) * (k : ℝ) / 8 := by
        rw [hd4]; ring
      rw [heq]; exact hsil
    · have hb := hk d hd h8 h4
      unfold Blocked at hb
      push Not at hb
      have heq : (d : ℝ) * ((τ + k) / 8) = (d : ℝ) * τ / 8 + (d : ℝ) * (k : ℝ) / 8 := by ring
      rw [heq]; exact hb

/-- **`(o, o, t, t)` with the odd readings in different pair classes, any number of silenced readings
`≡ 4 (mod 8)`.**  The non-multiples of `8` other than those `≡ 4 (mod 8)` are exactly two odd readings
`w₁, w₂` with `w₂ ≢ ±w₁ (mod 8)` and two readings `≡ 2 (mod 4)`; with at most three multiples of `8` and
readings `≡ 4 (mod 8)` together, the set is lonely (order four for the mixed instant). -/
theorem lonely_eight_of_oott {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d) {w₁ w₂ t₁ t₂ : ℕ}
    (hR : ∀ e ∈ S, ¬ 8 ∣ e → e % 8 ≠ 4 → e = w₁ ∨ e = w₂ ∨ e = t₁ ∨ e = t₂)
    (hw₁ : ¬ 2 ∣ w₁) (hw₂ : ¬ 2 ∣ w₂) (ht₁ : t₁ % 4 = 2) (ht₂ : t₂ % 4 = 2)
    (hne : w₁ % 8 ≠ w₂ % 8) (hneg : (w₁ + w₂) % 8 ≠ 0)
    (h : (S.filter (fun d => 8 ∣ d)).card + (S.filter (fun d => d % 8 = 4)).card ≤ 3) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  refine lonely_eight_of_eighth_free (fun τ => ?_) ?_
  · obtain ⟨k, hk, h1, h2, h3, h4⟩ := free_shift_oott τ hw₁ hw₂ ht₁ ht₂ hne hneg
    refine ⟨k, hk, fun e he h8 h48 => ?_⟩
    rcases hR e he h8 h48 with rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  · set A := (S.filter (fun d => 8 ∣ d)).image (fun d => d / 8) with hAdef
    set B := (S.filter (fun d => d % 8 = 4)).image (fun d => d / 4) with hBdef
    have hBpos : ∀ x ∈ B, 0 < x := by
      intro x hx
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hdS, hd4⟩ := Finset.mem_filter.mp hd
      exact Nat.div_pos (by have := hpos d hdS; omega) (by norm_num)
    have hcard : A.card + B.card ≤ 3 := by
      have h1 : A.card ≤ (S.filter (fun d => 8 ∣ d)).card := Finset.card_image_le
      have h2 : B.card ≤ (S.filter (fun d => d % 8 = 4)).card := Finset.card_image_le
      omega
    obtain ⟨τ, hτ, hτA, hτB⟩ := exists_mixed_le_three A B (quot_pos hpos 8 (by norm_num)) hBpos hcard
    exact ⟨τ, hτ, fun m hm h8 => hτA (m / 8) (Finset.mem_image.mpr ⟨m, Finset.mem_filter.mpr ⟨hm, h8⟩, rfl⟩),
      fun f hf h4 => hτB (f / 4) (Finset.mem_image.mpr ⟨f, Finset.mem_filter.mpr ⟨hf, h4⟩, rfl⟩)⟩

end LRC.OrderEightN
