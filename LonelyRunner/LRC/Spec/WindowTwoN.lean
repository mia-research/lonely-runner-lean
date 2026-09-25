import LonelyRunner.LRC.Cascade.Flanks
import LonelyRunner.LRC.ConstructionN.Band

/-!
# The two-flank window rule at order six (BHK Lemma 4 and Corollary 5, in framework form)

2026-09-24.  Two runners at real disparities `0 < e < f`, threshold `1/6`.  The clear set of one
runner is a union of closed bands `[(k + 1/6)/v, (k + 5/6)/v]`, of length `2/(3v)`, separated by
open in-the-way zones of length `1/(3v)`.  The rule:

* **Every closed window of length `2/(3e)` holds an instant at which both `e` and `f` are clear**
  (`two_flank_window`).  The instant is named, as Theorem 9 says it must be: the window's start, or
  an opening `(j + 1/6)/e` of `e`, or an opening `(j + 1/6)/f` of `f`.

The reading is exact, instant by instant.  In `e`'s coordinate `u = e·t` the window is
`[m + s, m + s + 2/3]`, `m = ⌊e·a⌋`, `s` its fractional part.

* `s ∉ (1/2, 5/6)`: the window holds a stretch of one `e`-band of `e`-length `1/3`, starting at the
  window's start or at an `e`-opening.  Its time length `1/(3e)` exceeds `f`'s in-the-way zone
  `1/(3f)`, so `f` is clear at the start of the stretch or opens inside it (`clear_on_stretch_six`).
* `s ∈ (1/2, 5/6)`: the window meets two `e`-bands, in stretches `[a, e₁]` and `[e₂, b]` with
  `e·e₁ = m + 5/6`, `e·e₂ = m + 7/6`.  Try `a`, then `f`'s next opening; then the `e`-opening `e₂`,
  then `f`'s next opening.  If all four fail, `f` is in the way on both stretches, in zones `K` and
  `K'`.  Each stretch has `f`-length below `1/3`, and together they have `f`-length `f/(3e)`, so
  `f/(3e) < 2/3`; and `f·e₂ − f·e₁ = f/(3e) > 1/3`.  Hence `K < K' < K + 1`: no such integer.

BHK's Lemma 4 is the same statement read backwards: a closed interval on which one of `e`, `f` is
always in the way is shorter than `2/(3e)` (`blocked_cover_short`).  BHK's Corollary 5 is the rule
with slow runners added: slow disparities clear across a window of length `2/(3·(largest slow))`,
and two further disparities faster than all of them, give a lonely instant in the window
(`lonely_six_of_slow_window`), named as above.

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.SpecN

open MomentIterationN Flanks

/-- Order six sits at `n = 6 ≥ 2`. -/
instance fact_two_le_six_window : Fact (2 ≤ 6) := ⟨by norm_num⟩

/-! ## 1. one runner: bands, zones, openings -/

/-- **Inside a band is clear.**  A reading in `[k + 1/6, k + 5/6]` is at least `1/6` from every
integer. -/
theorem clear_of_band_six {x : ℝ} (k : ℤ) (h1 : (k : ℝ) + 6⁻¹ ≤ x) (h2 : x ≤ (k : ℝ) + 5 / 6) :
    (6 : ℝ)⁻¹ ≤ circDist x := by
  obtain ⟨K, hK⟩ := ConstructionN.circDist_eq_abs_sub_some_int x
  rw [hK]
  by_contra h
  push Not at h
  obtain ⟨hl, hr⟩ := abs_lt.mp h
  have h3 : (k : ℝ) < (K : ℝ) := by linarith
  have h4 : (K : ℝ) < (k : ℝ) + 1 := by linarith
  have h3z : k < K := by exact_mod_cast h3
  have h4z : K < k + 1 := by exact_mod_cast h4
  omega

/-- **In the way means inside one zone.**  A reading less than `1/6` from the integers lies in
`(K − 1/6, K + 1/6)` for one integer `K`. -/
theorem zone_of_blocked_six {x : ℝ} (h : circDist x < 6⁻¹) :
    ∃ K : ℤ, (K : ℝ) - 6⁻¹ < x ∧ x < (K : ℝ) + 6⁻¹ := by
  obtain ⟨K, hK⟩ := ConstructionN.circDist_eq_abs_sub_some_int x
  rw [hK] at h
  obtain ⟨hl, hr⟩ := abs_lt.mp h
  exact ⟨K, by linarith, by linarith⟩

/-- **A runner is clear at its own opening** `(j + 1/6)/v`. -/
theorem clear_at_opening_six {v : ℝ} (hv : 0 < v) (j : ℤ) :
    (6 : ℝ)⁻¹ ≤ circDist (v * (((j : ℝ) + 6⁻¹) / v)) := by
  rw [mul_div_cancel₀ _ hv.ne']
  exact clear_of_band_six j le_rfl (by linarith)

/-- **Clear across a band stretch.**  If `e·p` and `e·q` lie in one band `[k + 1/6, k + 5/6]`, `e` is
clear at every instant of `[p, q]`. -/
theorem clear_between_six {e : ℝ} (he : 0 < e) (k : ℤ) {p q : ℝ} (hp : (k : ℝ) + 6⁻¹ ≤ e * p)
    (hq : e * q ≤ (k : ℝ) + 5 / 6) {t : ℝ} (h1 : p ≤ t) (h2 : t ≤ q) :
    (6 : ℝ)⁻¹ ≤ circDist (e * t) := by
  have h3 := mul_le_mul_of_nonneg_left h1 he.le
  have h4 := mul_le_mul_of_nonneg_left h2 he.le
  exact clear_of_band_six k (by linarith) (by linarith)

/-- **The second flank on an `e`-clear stretch.**  On a stretch `[p, q]` where `e` is clear, of
`e`-length at least `1/3`, the faster runner `f ≥ e` is clear at `p` or opens inside the stretch:
its in-the-way zone lasts `1/(3f) ≤ 1/(3e)`. -/
theorem clear_on_stretch_six {e f : ℝ} (he : 0 < e) (hef : e ≤ f) {p q : ℝ}
    (hlen : 1 / 3 ≤ e * q - e * p) (hE : ∀ t, p ≤ t → t ≤ q → (6 : ℝ)⁻¹ ≤ circDist (e * t)) :
    ∃ t, p ≤ t ∧ t ≤ q ∧ (6 : ℝ)⁻¹ ≤ circDist (e * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (f * t) ∧
      (t = p ∨ ∃ K : ℤ, t = ((K : ℝ) + 6⁻¹) / f) := by
  have hf : 0 < f := lt_of_lt_of_le he hef
  have hpq : p ≤ q := by
    by_contra h
    push Not at h
    have := mul_lt_mul_of_pos_left h he
    linarith
  have hflen : 1 / 3 ≤ f * q - f * p := by
    have : e * (q - p) ≤ f * (q - p) := mul_le_mul_of_nonneg_right hef (by linarith)
    nlinarith
  by_cases hfp : (6 : ℝ)⁻¹ ≤ circDist (f * p)
  · exact ⟨p, le_rfl, hpq, hE p le_rfl hpq, hfp, Or.inl rfl⟩
  · push Not at hfp
    obtain ⟨K, hK1, hK2⟩ := zone_of_blocked_six hfp
    set t := ((K : ℝ) + 6⁻¹) / f with ht
    have hft : f * t = (K : ℝ) + 6⁻¹ := by rw [ht, mul_div_cancel₀ _ hf.ne']
    have hpt : p ≤ t := by
      by_contra h
      push Not at h
      have := mul_lt_mul_of_pos_left h hf
      linarith
    have htq : t ≤ q := by
      by_contra h
      push Not at h
      have := mul_lt_mul_of_pos_left h hf
      linarith
    refine ⟨t, hpt, htq, hE t hpt htq, ?_, Or.inr ⟨K, rfl⟩⟩
    rw [hft]
    exact clear_of_band_six K le_rfl (by linarith)

/-! ## 2. the two-flank window rule -/

/-- **The two-flank window rule, on the exact window `[a, a + 2/(3e)]`.**  For real disparities
`0 < e < f`, some instant of the window has both runners clear at `1/6`; it is the window's start,
an opening of `e`, or an opening of `f`. -/
theorem two_flank_window_exact {e f : ℝ} (he : 0 < e) (hef : e < f) (a : ℝ) :
    ∃ t, a ≤ t ∧ t ≤ a + 2 / (3 * e) ∧
      (6 : ℝ)⁻¹ ≤ circDist (e * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (f * t) ∧
      (t = a ∨ ∃ j : ℤ, t = ((j : ℝ) + 6⁻¹) / e ∨ t = ((j : ℝ) + 6⁻¹) / f) := by
  have hf : 0 < f := he.trans hef
  have hdiv : ∀ x : ℝ, e * (x / e) = x := fun x => mul_div_cancel₀ x he.ne'
  set m : ℤ := ⌊e * a⌋ with hm
  set s : ℝ := Int.fract (e * a) with hs
  have hs0 : 0 ≤ s := Int.fract_nonneg _
  have hs1 : s < 1 := Int.fract_lt_one _
  have hea : e * a = (m : ℝ) + s := by rw [hs, hm]; exact (Int.floor_add_fract _).symm
  set b := a + 2 / (3 * e) with hb
  have heb : e * b = (m : ℝ) + s + 2 / 3 := by
    rw [hb, mul_add, hea, show e * (2 / (3 * e)) = 2 / 3 by field_simp]
  -- comparisons of instants read in `e`'s coordinate
  have hle : ∀ x y : ℝ, e * x ≤ e * y → x ≤ y := fun x y h => le_of_mul_le_mul_left h he
  -- a stretch `[p, q]` of one `e`-band, of `e`-length `1/3`, inside the window
  have stretch : ∀ (k : ℤ) (p q : ℝ), a ≤ p → q ≤ b → (k : ℝ) + 6⁻¹ ≤ e * p →
      e * q ≤ (k : ℝ) + 5 / 6 → 1 / 3 ≤ e * q - e * p → (p = a ∨ p = ((k : ℝ) + 6⁻¹) / e) →
      ∃ t, a ≤ t ∧ t ≤ b ∧ (6 : ℝ)⁻¹ ≤ circDist (e * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (f * t) ∧
        (t = a ∨ ∃ j : ℤ, t = ((j : ℝ) + 6⁻¹) / e ∨ t = ((j : ℝ) + 6⁻¹) / f) := by
    intro k p q hap hqb hkp hkq hlen hpa
    obtain ⟨t, hpt, htq, hte, htf, hwho⟩ :=
      clear_on_stretch_six he hef.le hlen (fun t h1 h2 => clear_between_six he k hkp hkq h1 h2)
    refine ⟨t, hap.trans hpt, htq.trans hqb, hte, htf, ?_⟩
    rcases hwho with rfl | ⟨K, rfl⟩
    · rcases hpa with h | h
      · exact Or.inl h
      · exact Or.inr ⟨k, Or.inl h⟩
    · exact Or.inr ⟨K, Or.inr rfl⟩
  rcases lt_or_ge s 6⁻¹ with hsA | hsA
  · -- `s < 1/6`: the stretch `[m + 1/6, m + 1/2]`, from `e`'s opening `m`
    refine stretch m (((m : ℝ) + 6⁻¹) / e) (((m : ℝ) + 1 / 2) / e) ?_ ?_ ?_ ?_ ?_ (Or.inr rfl)
    · apply hle; rw [hdiv, hea]; linarith
    · apply hle; rw [hdiv, heb]; linarith
    · rw [hdiv]
    · rw [hdiv]; linarith
    · rw [hdiv, hdiv]; linarith
  rcases le_or_gt s (1 / 2) with hsB | hsB
  · -- `1/6 ≤ s ≤ 1/2`: the stretch `[a, m + 5/6]`
    refine stretch m a (((m : ℝ) + 5 / 6) / e) le_rfl ?_ ?_ ?_ ?_ (Or.inl rfl)
    · apply hle; rw [hdiv, heb]; linarith
    · rw [hea]; linarith
    · rw [hdiv]
    · rw [hdiv, hea]; linarith
  rcases le_or_gt (5 / 6) s with hsD | hsC
  · -- `5/6 ≤ s`: the stretch `[m + 7/6, m + 3/2]`, from `e`'s opening `m + 1`
    refine stretch (m + 1) ((((m + 1 : ℤ) : ℝ) + 6⁻¹) / e) ((((m + 1 : ℤ) : ℝ) + 1 / 2) / e)
      ?_ ?_ ?_ ?_ ?_ (Or.inr rfl)
    · apply hle; rw [hdiv, hea]; push_cast; linarith
    · apply hle; rw [hdiv, heb]; push_cast; linarith
    · rw [hdiv]
    · rw [hdiv]; linarith
    · rw [hdiv, hdiv]; linarith
  -- `1/2 < s < 5/6`: two stretches, `[a, e₁]` and `[e₂, b]`
  set e₁ := ((m : ℝ) + 5 / 6) / e with he₁
  set e₂ := (((m + 1 : ℤ) : ℝ) + 6⁻¹) / e with he₂
  have hee₁ : e * e₁ = (m : ℝ) + 5 / 6 := hdiv _
  have hee₂ : e * e₂ = (m : ℝ) + 7 / 6 := by rw [he₂, hdiv]; push_cast; ring
  have hae₁ : a ≤ e₁ := hle _ _ (by rw [hea, hee₁]; linarith)
  have he₁e₂ : e₁ ≤ e₂ := hle _ _ (by rw [hee₁, hee₂]; linarith)
  have he₂b : e₂ ≤ b := hle _ _ (by rw [hee₂, heb]; linarith)
  -- first stretch: `a`, or `f`'s next opening
  by_cases hfa : (6 : ℝ)⁻¹ ≤ circDist (f * a)
  · refine ⟨a, le_rfl, hae₁.trans (he₁e₂.trans he₂b), ?_, hfa, Or.inl rfl⟩
    exact clear_between_six he m (p := a) (q := a) (by rw [hea]; linarith) (by rw [hea]; linarith)
      le_rfl le_rfl
  push Not at hfa
  obtain ⟨K, hK1, hK2⟩ := zone_of_blocked_six hfa
  by_cases ht₁ : ((K : ℝ) + 6⁻¹) / f ≤ e₁
  · have hat : a ≤ ((K : ℝ) + 6⁻¹) / f := by
      rw [le_div_iff₀ hf]; linarith
    exact ⟨_, hat, ht₁.trans (he₁e₂.trans he₂b),
      clear_between_six he m (by rw [hea]; linarith) (by rw [hee₁]) hat ht₁,
      clear_at_opening_six hf K, Or.inr ⟨K, Or.inr rfl⟩⟩
  push Not at ht₁
  have hfe₁ : f * e₁ < (K : ℝ) + 6⁻¹ := by
    have := mul_lt_mul_of_pos_left ht₁ hf
    rwa [mul_div_cancel₀ _ hf.ne'] at this
  -- second stretch: `e`'s opening `e₂`, or `f`'s next opening
  by_cases hfe₂ : (6 : ℝ)⁻¹ ≤ circDist (f * e₂)
  · refine ⟨e₂, hae₁.trans he₁e₂, he₂b, ?_, hfe₂, Or.inr ⟨m + 1, Or.inl rfl⟩⟩
    rw [he₂]; exact clear_at_opening_six he _
  push Not at hfe₂
  obtain ⟨K', hK'1, hK'2⟩ := zone_of_blocked_six hfe₂
  by_cases ht₂ : ((K' : ℝ) + 6⁻¹) / f ≤ b
  · have he₂t : e₂ ≤ ((K' : ℝ) + 6⁻¹) / f := by
      rw [le_div_iff₀ hf, mul_comm]; linarith
    exact ⟨_, (hae₁.trans he₁e₂).trans he₂t, ht₂,
      clear_between_six he (m + 1) (by rw [hee₂]; push_cast; linarith)
        (by rw [heb]; push_cast; linarith) he₂t ht₂,
      clear_at_opening_six hf K', Or.inr ⟨K', Or.inr rfl⟩⟩
  push Not at ht₂
  have hfb : f * b < (K' : ℝ) + 6⁻¹ := by
    have := mul_lt_mul_of_pos_left ht₂ hf
    rwa [mul_div_cancel₀ _ hf.ne'] at this
  -- `f` in the way on both stretches: the two zones `K`, `K'` are `f/(3e)` apart in `f`'s reading
  exfalso
  have hD : f * e₂ - f * e₁ = f / (3 * e) := by
    rw [he₁, he₂]; push_cast; field_simp; ring
  have hsum : (f * e₁ - f * a) + (f * b - f * e₂) = f / (3 * e) := by
    have hfa' : f * a = f / e * (e * a) := by field_simp
    have hfb' : f * b = f / e * (e * b) := by field_simp
    have hfe₁' : f * e₁ = f / e * (e * e₁) := by field_simp
    have hfe₂' : f * e₂ = f / e * (e * e₂) := by field_simp
    rw [hfa', hfb', hfe₁', hfe₂', hea, heb, hee₁, hee₂]; field_simp; ring
  have hD1 : 1 / 3 < f / (3 * e) := by
    rw [lt_div_iff₀ (by positivity)]; linarith
  have hmono : f * a ≤ f * e₁ := mul_le_mul_of_nonneg_left hae₁ hf.le
  have h1 : (K : ℝ) < K' := by linarith
  have h2 : (K' : ℝ) < K + 1 := by linarith
  have h1z : K < K' := by exact_mod_cast h1
  have h2z : K' < K + 1 := by exact_mod_cast h2
  omega

/-- **The two-flank window rule.**  For real disparities `0 < e < f`, every closed window
`[a, a + L]` with `L ≥ 2/(3e)` holds an instant at which both are clear at `1/6`: the window's start,
an opening `(j + 1/6)/e`, or an opening `(j + 1/6)/f`. -/
theorem two_flank_window {e f : ℝ} (he : 0 < e) (hef : e < f) (a : ℝ) {L : ℝ}
    (hL : 2 / (3 * e) ≤ L) :
    ∃ t, a ≤ t ∧ t ≤ a + L ∧
      (6 : ℝ)⁻¹ ≤ circDist (e * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (f * t) ∧
      (t = a ∨ ∃ j : ℤ, t = ((j : ℝ) + 6⁻¹) / e ∨ t = ((j : ℝ) + 6⁻¹) / f) := by
  obtain ⟨t, h1, h2, h3, h4, h5⟩ := two_flank_window_exact he hef a
  exact ⟨t, h1, by linarith, h3, h4, h5⟩

/-- A clear instant of a positive runner is not `0`. -/
theorem ne_zero_of_clear_six {e t : ℝ} (h : (6 : ℝ)⁻¹ ≤ circDist (e * t)) : t ≠ 0 := by
  rintro rfl
  rw [mul_zero] at h
  have : circDist 0 = 0 := by simp [circDist]
  linarith

/-- **The two-flank window rule, at the flanks' openings.**  For a window starting at `a ≥ 0`, the
instant is positive, and is the window's start or a flank opening `flankOpening 6 e j`,
`flankOpening 6 f j` (Theorem 9: the first clear instant is an opening). -/
theorem two_flank_window_opening {e f : ℝ} (he : 0 < e) (hef : e < f) {a : ℝ} (ha : 0 ≤ a)
    {L : ℝ} (hL : 2 / (3 * e) ≤ L) :
    ∃ t, 0 < t ∧ a ≤ t ∧ t ≤ a + L ∧
      (6 : ℝ)⁻¹ ≤ circDist (e * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (f * t) ∧
      (t = a ∨ ∃ j : ℕ, t = flankOpening 6 e j ∨ t = flankOpening 6 f j) := by
  have hf : 0 < f := he.trans hef
  obtain ⟨t, h1, h2, h3, h4, h5⟩ := two_flank_window he hef a hL
  have ht0 : 0 < t := lt_of_le_of_ne (ha.trans h1) (ne_zero_of_clear_six h3).symm
  refine ⟨t, ht0, h1, h2, h3, h4, ?_⟩
  rcases h5 with h | ⟨j, hj⟩
  · exact Or.inl h
  · right
    -- an opening at a positive instant has `j ≥ 0`
    have hj0 : 0 ≤ j := by
      have hpos : 0 < (j : ℝ) + 6⁻¹ := by
        rcases hj with h | h
        · have := mul_pos he ht0; rw [h, mul_div_cancel₀ _ he.ne'] at this; exact this
        · have := mul_pos hf ht0; rw [h, mul_div_cancel₀ _ hf.ne'] at this; exact this
      have : (-1 : ℝ) < j := by linarith
      have : (-1 : ℤ) < j := by exact_mod_cast this
      omega
    have hcast : (((j.toNat : ℕ) : ℝ)) = (j : ℝ) := by
      have := Int.toNat_of_nonneg hj0
      exact_mod_cast this
    refine ⟨j.toNat, ?_⟩
    unfold flankOpening
    rw [hcast, show ((6 : ℕ) : ℝ) = 6 by norm_num]
    exact hj

/-! ## 3. BHK Lemma 4, read backwards -/

/-- **BHK Lemma 4.**  For real disparities `0 < e < f`, a closed interval `[a, b]` at every instant of
which `e` or `f` is in the way (within `1/6`) is shorter than `2/(3e)`. -/
theorem blocked_cover_short {e f : ℝ} (he : 0 < e) (hef : e < f) {a b : ℝ}
    (hcov : ∀ t, a ≤ t → t ≤ b → circDist (e * t) < 6⁻¹ ∨ circDist (f * t) < 6⁻¹) :
    b - a < 2 / (3 * e) := by
  by_contra h
  push Not at h
  obtain ⟨t, h1, h2, h3, h4, -⟩ := two_flank_window he hef a h
  rcases hcov t h1 (by linarith) with h5 | h5 <;> linarith

/-! ## 4. BHK Corollary 5: slow runners clear on a window, two fast flanks -/

/-- **The window rule with slow runners.**  If every disparity of `S` is clear at `1/6` across a
window `[a, a + L]` with `L ≥ 2/(3e)`, and `0 < e < f`, then `insert e (insert f S)` is lonely at
some named instant of the window: its start, or an opening of `e` or of `f`. -/
theorem lonely_six_of_window {S : Finset ℝ} {e f : ℝ} (he : 0 < e) (hef : e < f) (a : ℝ) {L : ℝ}
    (hL : 2 / (3 * e) ≤ L)
    (hS : ∀ t, a ≤ t → t ≤ a + L → ∀ s ∈ S, (6 : ℝ)⁻¹ ≤ circDist (s * t)) :
    ∃ t, a ≤ t ∧ t ≤ a + L ∧ Lonely 6 (insert e (insert f S)) t ∧
      (t = a ∨ ∃ j : ℤ, t = ((j : ℝ) + 6⁻¹) / e ∨ t = ((j : ℝ) + 6⁻¹) / f) := by
  obtain ⟨t, h1, h2, h3, h4, h5⟩ := two_flank_window he hef a hL
  refine ⟨t, h1, h2, fun d hd => ?_, h5⟩
  rw [show ((6 : ℕ) : ℝ) = 6 by norm_num]
  rcases Finset.mem_insert.mp hd with rfl | hd
  · exact h3
  rcases Finset.mem_insert.mp hd with rfl | hd
  · exact h4
  · exact hS t h1 h2 d hd

/-- **BHK Corollary 5, in framework form.**  Let the slow disparities `S` (positive, nonempty) be
clear at `1/6` across a window `[a, a + L]` with `a ≥ 0` and `L ≥ 2/(3·max S)`, and let `e < f` be two
further disparities faster than every slow one.  Then the whole set `insert e (insert f S)` is lonely
at `1/6` at a positive instant of the window, and that instant is the window's start or an opening
`flankOpening 6 e j` or `flankOpening 6 f j`. -/
theorem lonely_six_of_slow_window {S : Finset ℝ} (hne : S.Nonempty) (hpos : ∀ s ∈ S, 0 < s)
    {e f : ℝ} (hSe : ∀ s ∈ S, s < e) (hef : e < f) {a L : ℝ} (ha : 0 ≤ a)
    (hL : 2 / (3 * S.max' hne) ≤ L)
    (hS : ∀ t, a ≤ t → t ≤ a + L → ∀ s ∈ S, (6 : ℝ)⁻¹ ≤ circDist (s * t)) :
    ∃ t, 0 < t ∧ a ≤ t ∧ t ≤ a + L ∧ Lonely 6 (insert e (insert f S)) t ∧
      (t = a ∨ ∃ j : ℕ, t = flankOpening 6 e j ∨ t = flankOpening 6 f j) := by
  have hmS : S.max' hne ∈ S := S.max'_mem hne
  have hm0 : 0 < S.max' hne := hpos _ hmS
  have hme : S.max' hne < e := hSe _ hmS
  have he : 0 < e := hm0.trans hme
  have hLe : 2 / (3 * e) ≤ L := by
    refine le_trans ?_ hL
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  obtain ⟨t, ht0, h1, h2, h3, h4, h5⟩ := two_flank_window_opening he hef ha hLe
  refine ⟨t, ht0, h1, h2, fun d hd => ?_, h5⟩
  rw [show ((6 : ℕ) : ℝ) = 6 by norm_num]
  rcases Finset.mem_insert.mp hd with rfl | hd
  · exact h3
  rcases Finset.mem_insert.mp hd with rfl | hd
  · exact h4
  · exact hS t h1 h2 d hd

end LRC.SpecN

