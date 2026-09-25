import LonelyRunner.LRC.Spec.FastPairEightN
import LonelyRunner.LRC.Spec.RealSevenN

/-!
# The split-chain rule: a lower-order core, and nested windows for the fast runners

2026-09-26.  R8 carries one fast runner on top of order seven and the fast pair (`FastPairEightN`) carries two on
top of order six.  Both use the same template: the lower order makes the slow core lonely at a stricter threshold,
which leaves a window of room, and a window lemma puts the fast runners' clear instant inside it.  This file states
the template once, for any list of fast runners.

* **A clear stretch in every window** (`stretch`).  A runner of speed `a > 0` is blocked on
  `((j - 1/8)/a, (j + 1/8)/a)`, so every window of length `(2ℓ + 1/4)/a` holds a stretch of length `ℓ/a` on which it
  is clear at `1/8`, for `0 ≤ ℓ ≤ 3/4`.
* **Nested windows** (`nested`).  For a list of speeds `a :: L`, the time the whole list needs is
  `needT (a :: L) = 2·needT L + 1/(4a)` (`needT [] = 0`): runner `a` supplies a clear stretch of length `needT L`, and
  the rest of the list finds its instant inside it.  Valid when `a · needT L ≤ 3/4` at every step (`Valid`).
  Every window of length `needT L` then holds an instant at which every runner of the list is clear at `1/8`.
  No order of the list is assumed; the conditions are what they are.
* **The split** (`lonely_of_split`).  A nonempty core `C`, every element positive and at most `m`, lonely at a
  threshold `θ ≥ 1/8` at some `τ > 0`; a valid list `F` with `needT F ≤ 2(θ − 1/8)/m`.  Then there is `t > 0` at
  which the core and every runner of `F` are clear at `1/8`.  The core stays clear on `[τ − δ, τ + δ]`,
  `δ = (θ − 1/8)/m`, because `circDist` is 1-Lipschitz.
* **At order eight** (`lonely_eight_of_split`): the core of at most six by native order seven at `1/7`, so the
  condition is `needT F ≤ 1/(28 m)`.  One fast runner `V` gives `needT [V] = 1/(4V)`, i.e. `V ≥ 7m`: R8.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.SplitChain

open MomentIterationN

/-- **A clear stretch in every window.** -/
theorem stretch {a ℓ : ℝ} (ha : 0 < a) (hl0 : 0 ≤ ℓ) (hl : ℓ ≤ 3 / 4) (x : ℝ) :
    ∃ y : ℝ, x ≤ y ∧ y + ℓ / a ≤ x + (2 * ℓ + 1 / 4) / a ∧
      ∀ t : ℝ, y ≤ t → t ≤ y + ℓ / a → (8 : ℝ)⁻¹ ≤ circDist (a * t) := by
  -- in `a`'s own coordinate: find w with v ≤ w, w + ℓ ≤ v + 2ℓ + 1/4, [w, w + ℓ] inside one clear band
  set v := a * x with hv
  have hfl := Int.floor_add_fract v
  have hf0 := Int.fract_nonneg v
  have hf1 := Int.fract_lt_one v
  have key : ∃ w : ℝ, v ≤ w ∧ w + ℓ ≤ v + 2 * ℓ + 1 / 4 ∧
      ∃ m : ℤ, (m : ℝ) + 1 / 8 ≤ w ∧ w + ℓ ≤ (m : ℝ) + 1 - 1 / 8 := by
    by_cases h1 : Int.fract v < 1 / 8
    · exact ⟨(⌊v⌋ : ℝ) + 1 / 8, by linarith, by linarith, ⌊v⌋, le_refl _, by linarith⟩
    by_cases h2 : Int.fract v ≤ 7 / 8 - ℓ
    · push Not at h1
      exact ⟨v, le_refl _, by linarith, ⌊v⌋, by linarith, by linarith⟩
    · push Not at h1 h2
      refine ⟨((⌊v⌋ + 1 : ℤ) : ℝ) + 1 / 8, ?_, ?_, ⌊v⌋ + 1, le_refl _, ?_⟩ <;> push_cast <;> linarith
  obtain ⟨w, hw1, hw2, m, hm1, hm2⟩ := key
  refine ⟨w / a, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ ha]; linarith [show x * a = v by rw [hv]; ring]
  · have e1 : w / a + ℓ / a = (w + ℓ) / a := by field_simp
    have e2 : x + (2 * ℓ + 1 / 4) / a = (v + 2 * ℓ + 1 / 4) / a := by rw [hv]; field_simp; ring
    rw [e1, e2]; exact div_le_div_of_nonneg_right hw2 ha.le
  · intro t ht1 ht2
    have hlo : w ≤ a * t := by
      have := mul_le_mul_of_nonneg_left ht1 ha.le
      rwa [show a * (w / a) = w by field_simp] at this
    have hhi : a * t ≤ w + ℓ := by
      have := mul_le_mul_of_nonneg_left ht2 ha.le
      rwa [show a * (w / a + ℓ / a) = w + ℓ by field_simp] at this
    rw [show (8 : ℝ)⁻¹ = 1 / 8 by norm_num]
    exact LRC.MirrorCentre.circDist_ge_of_window (m := m) (by linarith) (by linarith) (by norm_num)

/-- The time a list of fast runners needs: `needT [] = 0`, `needT (a :: L) = 2 · needT L + 1/(4a)`. -/
noncomputable def needT : List ℝ → ℝ
  | [] => 0
  | a :: L => 2 * needT L + 1 / (4 * a)

/-- The chain conditions: every speed positive, and `a · needT L ≤ 3/4` at every step. -/
def Valid : List ℝ → Prop
  | [] => True
  | a :: L => 0 < a ∧ a * needT L ≤ 3 / 4 ∧ Valid L

theorem needT_nonneg : ∀ {L : List ℝ}, Valid L → 0 ≤ needT L
  | [], _ => by simp [needT]
  | a :: L, ⟨ha, _, hL⟩ => by
      have := needT_nonneg hL
      have : 0 < 1 / (4 * a) := by positivity
      simp only [needT]; linarith

/-- **Nested windows.**  Every window of length `needT L` holds an instant at which every runner of the list is
clear at `1/8`. -/
theorem nested : ∀ {L : List ℝ}, Valid L → ∀ x : ℝ,
    ∃ t : ℝ, x ≤ t ∧ t ≤ x + needT L ∧ ∀ d ∈ L, (8 : ℝ)⁻¹ ≤ circDist (d * t)
  | [], _, x => ⟨x, le_refl _, by simp [needT], by simp⟩
  | a :: L, ⟨ha, hle, hL⟩, x => by
      have hN := needT_nonneg hL
      obtain ⟨y, hy1, hy2, hclear⟩ := stretch (ℓ := a * needT L) ha (by positivity) hle x
      have hy2' : y + needT L ≤ x + needT (a :: L) := by
        have e1 : a * needT L / a = needT L := by field_simp
        have e2 : (2 * (a * needT L) + 1 / 4) / a = 2 * needT L + 1 / (4 * a) := by field_simp
        rw [e1, e2] at hy2; simp only [needT]; linarith
      obtain ⟨t, ht1, ht2, hrest⟩ := nested hL y
      refine ⟨t, le_trans hy1 ht1, by linarith, ?_⟩
      intro d hd
      rcases List.mem_cons.mp hd with h | hd
      · rw [h]
        exact hclear t ht1 (by rw [show a * needT L / a = needT L by field_simp]; exact ht2)
      · exact hrest d hd

/-- **The split.**  A nonempty core lonely at `θ ≥ 1/8`, every element at most `m`; a valid list whose need fits
the room the core leaves.  Then core and list are clear together at some positive instant. -/
theorem lonely_of_split {C : Finset ℝ} {F : List ℝ} {θ m τ : ℝ}
    (hCpos : ∀ c ∈ C, 0 < c) (hCne : C.Nonempty) (hCm : ∀ c ∈ C, c ≤ m) (hθ : (8 : ℝ)⁻¹ ≤ θ)
    (hτ : 0 < τ) (hcore : ∀ c ∈ C, θ ≤ circDist (c * τ))
    (hF : Valid F) (hroom : needT F ≤ 2 * (θ - (8 : ℝ)⁻¹) / m) :
    ∃ t : ℝ, 0 < t ∧ (∀ c ∈ C, (8 : ℝ)⁻¹ ≤ circDist (c * t)) ∧ ∀ d ∈ F, (8 : ℝ)⁻¹ ≤ circDist (d * t) := by
  obtain ⟨c0, hc0⟩ := hCne
  have hc0pos := hCpos c0 hc0
  have hm : 0 < m := lt_of_lt_of_le hc0pos (hCm c0 hc0)
  set δ := (θ - (8 : ℝ)⁻¹) / m with hδ
  have hδ0 : 0 ≤ δ := div_nonneg (by linarith) hm.le
  -- τ is beyond δ: θ ≤ circDist (c0 τ) ≤ c0 τ ≤ m τ, and δ < θ/m
  have hτδ : δ < τ := by
    have h1 : θ ≤ c0 * τ := le_trans (hcore c0 hc0)
      (LRC.FastPairEight.circDist_le_self (by positivity))
    have h2 : c0 * τ ≤ m * τ := mul_le_mul_of_nonneg_right (hCm c0 hc0) hτ.le
    rw [hδ, div_lt_iff₀ hm]
    have : (8 : ℝ)⁻¹ > 0 := by norm_num
    nlinarith
  obtain ⟨t, ht1, ht2, hFt⟩ := nested hF (τ - δ)
  have hneed : needT F ≤ 2 * δ := by rw [hδ]; linarith [show 2 * (θ - (8 : ℝ)⁻¹) / m = 2 * ((θ - (8 : ℝ)⁻¹) / m) by ring]
  refine ⟨t, by linarith, ?_, hFt⟩
  intro c hc
  have hcpos := hCpos c hc
  have hdist : |c * t - c * τ| ≤ θ - (8 : ℝ)⁻¹ := by
    rw [← mul_sub, abs_mul, abs_of_pos hcpos]
    have htt : |t - τ| ≤ δ := by rw [abs_le]; constructor <;> linarith
    calc c * |t - τ| ≤ m * δ := mul_le_mul (hCm c hc) htt (abs_nonneg _) hm.le
      _ = θ - (8 : ℝ)⁻¹ := by rw [hδ]; field_simp
  have hlip := circDist_lipschitz.dist_le_mul (c * t) (c * τ)
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
  have := (abs_sub_le_iff.mp hlip).2
  linarith [hcore c hc]

/-- **At order eight.**  A nonempty core of at most six positive reals, every element at most `m`, is lonely at
`1/7` by native order seven; a valid list with `needT F ≤ 1/(28 m)` then gives a lonely instant at `1/8` for the core
and the list together. -/
theorem lonely_eight_of_split {C : Finset ℝ} {F : List ℝ} {m : ℝ}
    (hCpos : ∀ c ∈ C, 0 < c) (hCne : C.Nonempty) (hCcard : C.card ≤ 6) (hCm : ∀ c ∈ C, c ≤ m)
    (hF : Valid F) (hroom : needT F ≤ 1 / (28 * m)) :
    ∃ t : ℝ, 0 < t ∧ (∀ c ∈ C, (8 : ℝ)⁻¹ ≤ circDist (c * t)) ∧ ∀ d ∈ F, (8 : ℝ)⁻¹ ≤ circDist (d * t) := by
  obtain ⟨τ, hτ, hl⟩ := LRC.OrderSevenN.existenceAtN_seven C hCpos (by simpa using hCcard)
  refine lonely_of_split hCpos hCne hCm (θ := (7 : ℝ)⁻¹) (by norm_num) hτ ?_ hF ?_
  · intro c hc; have := hl c hc; simpa using this
  · have e : 2 * ((7 : ℝ)⁻¹ - (8 : ℝ)⁻¹) / m = 1 / (28 * m) := by
      obtain ⟨c0, hc0⟩ := hCne
      have hm : 0 < m := lt_of_lt_of_le (hCpos c0 hc0) (hCm c0 hc0)
      field_simp; ring
    rw [e]; exact hroom

/-- **R8 recovered.**  One fast runner `V ≥ 7m` over a core of at most six: `needT [V] = 1/(4V) ≤ 1/(28 m)`. -/
theorem r8_of_split {C : Finset ℝ} {V m : ℝ} (hCpos : ∀ c ∈ C, 0 < c) (hCne : C.Nonempty)
    (hCcard : C.card ≤ 6) (hCm : ∀ c ∈ C, c ≤ m) (hV : 7 * m ≤ V) :
    ∃ t : ℝ, 0 < t ∧ (∀ c ∈ C, (8 : ℝ)⁻¹ ≤ circDist (c * t)) ∧ (8 : ℝ)⁻¹ ≤ circDist (V * t) := by
  obtain ⟨c0, hc0⟩ := hCne
  have hm : 0 < m := lt_of_lt_of_le (hCpos c0 hc0) (hCm c0 hc0)
  have hVpos : 0 < V := by linarith
  have hF : Valid [V] := ⟨hVpos, by simp only [needT, mul_zero]; norm_num, trivial⟩
  obtain ⟨t, ht, hC, hFt⟩ := lonely_eight_of_split hCpos ⟨c0, hc0⟩ hCcard hCm hF (by
    simp only [needT, mul_zero, zero_add]
    exact one_div_le_one_div_of_le (by positivity) (by linarith))
  exact ⟨t, ht, hC, hFt V (by simp)⟩

end LRC.SplitChain
