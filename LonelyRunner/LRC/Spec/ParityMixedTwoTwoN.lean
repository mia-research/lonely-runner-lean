import LonelyRunner.LRC.Spec.ParityDescentTwoN

set_option linter.style.longLine false

/-!
# The displacement step M(2,2), and the quarter and eighth levels at two and two (order eight)

2026-10-06 (running log E402).  Continues `ParityDescentTwoN`.  The isolation is taken at the grid
shifts `j/4` (quarter level) or `k/8` (eighth level), displaced by an offset.  **M(2,2)** supplies the
offset: at most two numbers clear at `1/8` (the readings the shifts hold still, divided down) and at most
two odd numbers clear at `1/4` (the silenced readings, divided down to odd numbers), at one instant.
The corollaries' instant is the displaced grid instant.

Source proof: the header of `experiments/nN/redo/mixed_lemma_check_v1.py` (LEMMA ROT, FIT2, CELL2, C2,
Q, and cases A, C, DE1–DE4).  Odd numbers are written `b ≡ 1 (mod 4)`, `‖u·x‖ = ‖b·x‖`
(`exists_one_mod_four`); `b₁ > b₂`, `d = b₁ − b₂`.

* ROT: `rot_four_dvd`, `rot_one_mod_four`.  FIT2: `exists_quarter_fit`.  CELL2 + C2: `de_finish`.
* Lemma Q: `exists_grid_point`, by the source's grid count, carried out exactly (`card_filter_mod`,
  `card_window_ge`, `card_arc_le`).
* Case A: `case_A`.  Case C: `case_C`.  Case DE: `case_DE1`, `case_DE2`, `case_DE3_pos`,
  `case_DE3_neg`, `de4` (`de4a`, `de4b_z` and its five leaves), dispatched by `case_DE`.
* `exists_mixed_two_two`: M(2,2); at most three numbers in all reduce to `exists_mixed_le_three`.
* `lonely_eight_of_quarter_two_two`, `lonely_eight_of_eighth_two_two`: the two corollaries, through
  `lonely_eight_of_quarter_silent` and `lonely_eight_of_eighth_silent`.

Departures from the written proof (same statements, different arguments):
* DE1 and DE4a use one coset lemma (`exists_coset_quarter`, Bézout): if `q ∤ r`, some `x₀ + n·r/q` is at
  least `1/4` from the integers.  The source uses the points `⌊q/2⌋/q` and "nearest `1/2`".
* DE2/DE3/DE4 are split by `d ∣ 4b₂` instead of `d' = d/(4·gcd(u₁,u₂))`: `d ∤ 4b₂` is DE2; otherwise
  `d = 4g`, `b₂ = gβ`, `b₁ = g(β + 4)`, and the sign pattern of `β, β + 4` gives DE3 (same signs) or
  DE4 (`β = −1, −3`, i.e. `{u₁, u₂} = {g, 3g}`).
* DE3 with `q + 4 > 8t` takes `ξ = n/q`, `n = ⌈q/(8t)⌉`, in place of `n = ⌈1/(8r)⌉`, `r = ‖t/q‖`.
* The DE4b sweeps run over intervals of length exactly `1/(4·speed)` (`exists_sweep`), in place of the
  source's `[z_lo, min(…)]`; the five leaves are otherwise the source's.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.ParityDescent

open ConstructionN LRC.Descent

/-! ## Tools on `circDist` -/

/-- The triangle inequality for the distance to the nearest integer. -/
theorem circDist_add_le (x y : ℝ) : circDist (x + y) ≤ circDist x + circDist y := by
  obtain ⟨K₁, hK₁⟩ := circDist_eq_abs_sub_some_int x
  obtain ⟨K₂, hK₂⟩ := circDist_eq_abs_sub_some_int y
  have h := circDist_le_abs_sub_int (x + y) (K₁ + K₂)
  have : |x + y - ((K₁ + K₂ : ℤ) : ℝ)| ≤ |x - K₁| + |y - K₂| := by
    have heq : x + y - ((K₁ + K₂ : ℤ) : ℝ) = (x - K₁) + (y - K₂) := by push_cast; ring
    rw [heq]; exact abs_add_le _ _
  linarith

/-- **Two positions a step `δ` apart, `‖δ‖ ≥ 1/4`, are not both within `1/8` of the integers.** -/
theorem eighth_or_step {δ : ℝ} (hδ : (4 : ℝ)⁻¹ ≤ circDist δ) (y : ℝ) :
    (8 : ℝ)⁻¹ ≤ circDist y ∨ (8 : ℝ)⁻¹ ≤ circDist (y + δ) := by
  by_contra h
  push Not at h
  have h1 := circDist_add_le (y + δ) (-y)
  rw [circDist.symm_neg, show y + δ + -y = δ by ring] at h1
  linarith [h.1, h.2]

/-- A reading not divisible by `4`, at the quarter instant: `‖c/4‖ ≥ 1/4`. -/
theorem quarter_of_not_four_dvd {c : ℕ} (hc : ¬ 4 ∣ c) : (4 : ℝ)⁻¹ ≤ circDist ((c : ℝ) / 4) := by
  obtain ⟨k, r, hr, hcr⟩ : ∃ k r : ℕ, (r = 1 ∨ r = 2 ∨ r = 3) ∧ c = 4 * k + r :=
    ⟨c / 4, c % 4, by omega, by omega⟩
  have heq : (c : ℝ) / 4 = ((k : ℤ) : ℝ) + (r : ℝ) / 4 := by rw [hcr]; push_cast; ring
  rw [heq]
  rcases hr with rfl | rfl | rfl <;>
    exact LRC.MirrorCentre.circDist_ge_of_window (m := (k : ℤ)) (by push_cast; linarith)
      (by push_cast; linarith) (by norm_num)

/-- An integer `b ≡ 1 (mod 4)`: `‖b/4‖ ≥ 1/4`. -/
theorem quarter_of_one_mod_four {b : ℤ} (hb : 4 ∣ b - 1) : (4 : ℝ)⁻¹ ≤ circDist ((b : ℝ) / 4) := by
  obtain ⟨j, hj⟩ := hb
  have heq : (b : ℝ) / 4 = (j : ℝ) + 1 / 4 := by
    have : (b : ℝ) = 4 * j + 1 := by
      have : b = 4 * j + 1 := by linarith
      rw [this]; push_cast; ring
    rw [this]; ring
  rw [heq]
  exact LRC.MirrorCentre.circDist_ge_of_window (m := j) (by linarith) (by linarith) (by norm_num)

/-- A value within `a` of an integer is at circular distance at most `a`. -/
theorem circDist_le_of_near {x a : ℝ} {m : ℤ} (h1 : (m : ℝ) - a ≤ x) (h2 : x ≤ (m : ℝ) + a) :
    circDist x ≤ a := by
  have := circDist_le_abs_sub_int x m
  have : |x - (m : ℝ)| ≤ a := by rw [abs_le]; constructor <;> linarith
  linarith

/-- **ROT, multiples of `4`.**  A quarter step leaves a multiple of `4` in place. -/
theorem rot_four_dvd {c : ℕ} (hc : 4 ∣ c) (x : ℝ) (K : ℤ) :
    circDist ((c : ℝ) * (x + (K : ℝ) / 4)) = circDist ((c : ℝ) * x) := by
  obtain ⟨c', rfl⟩ := hc
  have heq : ((4 * c' : ℕ) : ℝ) * (x + (K : ℝ) / 4) = ((4 * c' : ℕ) : ℝ) * x + (((c' : ℤ) * K : ℤ) : ℝ) := by
    push_cast; ring
  rw [heq, circDist_add_int]

/-- **ROT, `b ≡ 1 (mod 4)`.**  A quarter step `K/4` moves `b·x` by `K/4`. -/
theorem rot_one_mod_four {b : ℤ} (hb : 4 ∣ b - 1) (x : ℝ) (K : ℤ) :
    circDist ((b : ℝ) * (x + (K : ℝ) / 4)) = circDist ((b : ℝ) * x + (K : ℝ) / 4) := by
  obtain ⟨j, hj⟩ := hb
  have hb' : (b : ℝ) = 4 * j + 1 := by
    have : b = 4 * j + 1 := by linarith
    rw [this]; push_cast; ring
  have heq : (b : ℝ) * (x + (K : ℝ) / 4) = ((b : ℝ) * x + (K : ℝ) / 4) + ((j * K : ℤ) : ℝ) := by
    rw [hb']; push_cast; ring
  rw [heq, circDist_add_int]

/-- An odd natural number reads as an integer `b ≡ 1 (mod 4)` of the same size. -/
theorem exists_one_mod_four {u : ℕ} (hu : ¬ 2 ∣ u) :
    ∃ b : ℤ, 4 ∣ b - 1 ∧ (b = u ∨ b = -(u : ℤ)) ∧ ∀ x : ℝ, circDist ((u : ℝ) * x) = circDist ((b : ℝ) * x) := by
  rcases (show u % 4 = 1 ∨ u % 4 = 3 by omega) with h | h
  · refine ⟨u, ⟨(u / 4 : ℕ), by omega⟩, Or.inl rfl, fun x => rfl⟩
  · refine ⟨-(u : ℤ), ⟨-((u / 4 : ℕ) : ℤ) - 1, by omega⟩, Or.inr rfl, fun x => ?_⟩
    push_cast
    rw [show -(u : ℝ) * x = -((u : ℝ) * x) by ring, circDist.symm_neg]

/-! ## Sweeping an interval, and a coset of a cyclic group -/

/-- **Sweep.**  On an interval over which `e·z` moves by at least `1/4`, some `z` puts `θ + e·z` at
least `1/8` from the integers. -/
theorem exists_sweep (θ : ℝ) {e lo hi : ℝ} (he : 0 < e) (hlen : (4 : ℝ)⁻¹ ≤ e * (hi - lo)) :
    ∃ z : ℝ, lo ≤ z ∧ z ≤ hi ∧ (8 : ℝ)⁻¹ ≤ circDist (θ + e * z) := by
  have hhl : 0 ≤ hi - lo := by
    by_contra h
    push Not at h
    nlinarith
  by_cases h0 : (8 : ℝ)⁻¹ ≤ circDist (θ + e * lo)
  · exact ⟨lo, le_refl _, by linarith, h0⟩
  · push Not at h0
    obtain ⟨K, hK⟩ := circDist_eq_abs_sub_some_int (θ + e * lo)
    rw [hK, abs_lt] at h0
    set z := lo + ((K : ℝ) + 1 / 8 - (θ + e * lo)) / e with hz
    have hez : e * z = e * lo + ((K : ℝ) + 1 / 8 - (θ + e * lo)) := by
      rw [hz, mul_add, mul_div_cancel₀ _ he.ne']
    refine ⟨z, ?_, ?_, ?_⟩
    · have : 0 ≤ ((K : ℝ) + 1 / 8 - (θ + e * lo)) / e := div_nonneg (by linarith) he.le
      linarith
    · have h1 : ((K : ℝ) + 1 / 8 - (θ + e * lo)) / e ≤ hi - lo := by
        rw [div_le_iff₀ he]; nlinarith
      linarith
    · have : θ + e * z = (K : ℝ) + 1 / 8 := by rw [hez]; ring
      rw [this]
      exact LRC.MirrorCentre.circDist_ge_of_window (m := K) (by norm_num) (by norm_num; linarith) (by norm_num)

/-- **A coset of `(gcd(r,q)/q)·ℤ`.**  As `n` runs over the integers, `x₀ + n·r/q` meets every window of
length `gcd(r,q)/q` modulo `1` (Bézout). -/
theorem exists_coset_window (x₀ a : ℝ) (r : ℤ) {q : ℕ} (hq : 0 < q) :
    ∃ n N : ℤ, a ≤ x₀ + (n : ℝ) * r / q - N ∧
      x₀ + (n : ℝ) * r / q - N ≤ a + (Int.gcd r q : ℝ) / q := by
  have hpos : 0 < Int.gcd r q := Int.gcd_pos_of_ne_zero_right r (by exact_mod_cast hq.ne')
  have hbez : ((Int.gcd r q : ℤ) : ℝ) = (r : ℝ) * (Int.gcdA r q : ℝ) + (q : ℝ) * (Int.gcdB r q : ℝ) := by
    have := Int.gcd_eq_gcd_ab r q
    exact_mod_cast this
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hhR : (0 : ℝ) < (Int.gcd r q : ℝ) := by exact_mod_cast hpos
  set M : ℤ := ⌈(a - x₀) * q / (Int.gcd r q : ℝ)⌉ with hM
  refine ⟨M * Int.gcdA r q, -(M * Int.gcdB r q), ?_, ?_⟩
  · have hkey : x₀ + ((M * Int.gcdA r q : ℤ) : ℝ) * r / q - ((-(M * Int.gcdB r q) : ℤ) : ℝ)
        = x₀ + (M : ℝ) * (Int.gcd r q : ℝ) / q := by
      have h' : ((Int.gcd r q : ℕ) : ℝ) = ((Int.gcd r q : ℤ) : ℝ) := by norm_cast
      rw [h', hbez]; push_cast; field_simp; ring
    rw [hkey]
    have hle : (a - x₀) * q / (Int.gcd r q : ℝ) ≤ (M : ℝ) := Int.le_ceil _
    rw [div_le_iff₀ hhR] at hle
    have : a - x₀ ≤ (M : ℝ) * (Int.gcd r q : ℝ) / q := by rw [le_div_iff₀ hqR]; linarith
    linarith
  · have hkey : x₀ + ((M * Int.gcdA r q : ℤ) : ℝ) * r / q - ((-(M * Int.gcdB r q) : ℤ) : ℝ)
        = x₀ + (M : ℝ) * (Int.gcd r q : ℝ) / q := by
      have h' : ((Int.gcd r q : ℕ) : ℝ) = ((Int.gcd r q : ℤ) : ℝ) := by norm_cast
      rw [h', hbez]; push_cast; field_simp; ring
    rw [hkey]
    have hlt : (M : ℝ) < (a - x₀) * q / (Int.gcd r q : ℝ) + 1 := Int.ceil_lt_add_one _
    have : (M : ℝ) * (Int.gcd r q : ℝ) / q ≤ a - x₀ + (Int.gcd r q : ℝ) / q := by
      rw [div_le_iff₀ hqR, add_mul, div_mul_cancel₀ _ hqR.ne']
      have h2 : (M : ℝ) * (Int.gcd r q : ℝ) < ((a - x₀) * q / (Int.gcd r q : ℝ) + 1) * (Int.gcd r q : ℝ) :=
        mul_lt_mul_of_pos_right hlt hhR
      rw [add_mul, div_mul_cancel₀ _ hhR.ne'] at h2
      linarith
    linarith

/-- **Coset lemma.**  If `q ∤ r`, some `x₀ + n·r/q` is at least `1/4` from the integers. -/
theorem exists_coset_quarter (x₀ : ℝ) (r : ℤ) {q : ℕ} (hq : 0 < q) (hdvd : ¬ (q : ℤ) ∣ r) :
    ∃ n : ℤ, (4 : ℝ)⁻¹ ≤ circDist (x₀ + (n : ℝ) * r / q) := by
  obtain ⟨n, N, h1, h2⟩ := exists_coset_window x₀ (1 / 4) r hq
  have hg : 2 * Int.gcd r q ≤ q := by
    have hd : Int.gcd r q ∣ q := by
      have := Int.gcd_dvd_right r (q : ℤ)
      exact_mod_cast this
    obtain ⟨k, hk⟩ := hd
    have hne : Int.gcd r q ≠ q := by
      intro he
      apply hdvd
      have := Int.gcd_dvd_left r (q : ℤ)
      rw [he] at this
      exact this
    rcases k with _ | _ | k
    · omega
    · simp at hk; exact absurd hk.symm hne
    · nlinarith
  have hfrac : (Int.gcd r q : ℝ) / q ≤ 1 / 2 := by
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    rw [div_le_iff₀ hqR]
    have : (2 * Int.gcd r q : ℝ) ≤ q := by exact_mod_cast hg
    linarith
  exact ⟨n, LRC.MirrorCentre.circDist_ge_of_window (m := N) (by linarith) (by linarith) (by norm_num)⟩

/-! ## FIT2, CELL2 and C2: placing the two odd readings by a quarter step -/

/-- **FIT2.**  Two points within `1/4` of each other (modulo `1`) are both at least `1/4` from some
quarter point `−K/4`. -/
theorem exists_quarter_fit {p q : ℝ} (h : circDist (p - q) ≤ (4 : ℝ)⁻¹) :
    ∃ K : ℤ, (4 : ℝ)⁻¹ ≤ circDist (p + (K : ℝ) / 4) ∧ (4 : ℝ)⁻¹ ≤ circDist (q + (K : ℝ) / 4) := by
  obtain ⟨M, hM⟩ := circDist_eq_abs_sub_some_int (p - q)
  rw [hM, abs_le] at h
  set H := max p (q + M) with hH
  have hpH : p ≤ H := le_max_left _ _
  have hqH : q + M ≤ H := le_max_right _ _
  have hp' : H - 4⁻¹ ≤ p := by
    rcases max_choice p (q + M) with h' | h' <;> rw [hH, h'] <;> linarith [h.1, h.2]
  have hq' : H - 4⁻¹ ≤ q + M := by
    rcases max_choice p (q + M) with h' | h' <;> rw [hH, h'] <;> linarith [h.1, h.2]
  set j : ℤ := ⌈4 * H + 1⌉ with hj
  have hj1 : 4 * H + 1 ≤ (j : ℝ) := Int.le_ceil _
  have hj2 : (j : ℝ) < 4 * H + 1 + 1 := Int.ceil_lt_add_one _
  refine ⟨-j, ?_, ?_⟩
  · exact LRC.MirrorCentre.circDist_ge_of_window (m := -1) (by push_cast; linarith)
      (by push_cast; linarith) (by norm_num)
  · have heq : q + ((-j : ℤ) : ℝ) / 4 = (q + M + ((-j : ℤ) : ℝ) / 4) + ((-M : ℤ) : ℝ) := by push_cast; ring
    rw [heq, circDist_add_int]
    exact LRC.MirrorCentre.circDist_ge_of_window (m := -1) (by push_cast; linarith)
      (by push_cast; linarith) (by norm_num)

/-- **CELL2 + C2.**  If `c₁` (a multiple of `4`) is clear at `ρ` and the two readings `b₁ρ`, `b₂ρ`
(`bⱼ ≡ 1 mod 4`) lie in one closed quarter cell `[w/4, (w+1)/4]` modulo `1`, then one of the two quarter
steps `K = −(w+2), −(w+3)` clears `c₂` (not a multiple of `4`) as well, and both keep the odd readings
at least `1/4` from the integers. -/
theorem de_finish {c₁ c₂ : ℕ} (hc₁ : 4 ∣ c₁) (hc₂ : ¬ 4 ∣ c₂) {b₁ b₂ : ℤ} (hb₁ : 4 ∣ b₁ - 1)
    (hb₂ : 4 ∣ b₂ - 1) {ρ : ℝ} (hρ : (8 : ℝ)⁻¹ ≤ circDist ((c₁ : ℝ) * ρ)) (w N₁ N₂ : ℤ)
    (h₁ : (w : ℝ) / 4 ≤ (b₁ : ℝ) * ρ - N₁ ∧ (b₁ : ℝ) * ρ - N₁ ≤ ((w : ℝ) + 1) / 4)
    (h₂ : (w : ℝ) / 4 ≤ (b₂ : ℝ) * ρ - N₂ ∧ (b₂ : ℝ) * ρ - N₂ ≤ ((w : ℝ) + 1) / 4) :
    ∃ τ : ℝ, (8 : ℝ)⁻¹ ≤ circDist ((c₁ : ℝ) * τ) ∧ (8 : ℝ)⁻¹ ≤ circDist ((c₂ : ℝ) * τ) ∧
      (4 : ℝ)⁻¹ ≤ circDist ((b₁ : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((b₂ : ℝ) * τ) := by
  have hb : ∀ {b N : ℤ}, 4 ∣ b - 1 →
      ((w : ℝ) / 4 ≤ (b : ℝ) * ρ - N ∧ (b : ℝ) * ρ - N ≤ ((w : ℝ) + 1) / 4) →
      ∀ K : ℤ, (K = -(w + 2) ∨ K = -(w + 3)) →
        (4 : ℝ)⁻¹ ≤ circDist ((b : ℝ) * (ρ + (K : ℝ) / 4)) := by
    intro b N hb hbN K hK
    rw [rot_one_mod_four hb]
    rcases hK with rfl | rfl
    · exact LRC.MirrorCentre.circDist_ge_of_window (m := N - 1) (by push_cast; linarith [hbN.1, hbN.2])
        (by push_cast; linarith [hbN.1, hbN.2]) (by norm_num)
    · exact LRC.MirrorCentre.circDist_ge_of_window (m := N - 1) (by push_cast; linarith [hbN.1, hbN.2])
        (by push_cast; linarith [hbN.1, hbN.2]) (by norm_num)
  have hδ : (4 : ℝ)⁻¹ ≤ circDist (-((c₂ : ℝ) / 4)) := by
    rw [circDist.symm_neg]; exact quarter_of_not_four_dvd hc₂
  rcases eighth_or_step hδ ((c₂ : ℝ) * (ρ + ((-(w + 2) : ℤ) : ℝ) / 4)) with h | h
  · exact ⟨ρ + ((-(w + 2) : ℤ) : ℝ) / 4, by rw [rot_four_dvd hc₁]; exact hρ, h,
      hb hb₁ h₁ _ (Or.inl rfl), hb hb₂ h₂ _ (Or.inl rfl)⟩
  · refine ⟨ρ + ((-(w + 3) : ℤ) : ℝ) / 4, by rw [rot_four_dvd hc₁]; exact hρ, ?_,
      hb hb₁ h₁ _ (Or.inr rfl), hb hb₂ h₂ _ (Or.inr rfl)⟩
    have heq : (c₂ : ℝ) * (ρ + ((-(w + 3) : ℤ) : ℝ) / 4)
        = (c₂ : ℝ) * (ρ + ((-(w + 2) : ℤ) : ℝ) / 4) + -((c₂ : ℝ) / 4) := by push_cast; ring
    rw [heq]; exact h

/-- **FIT2 + ROT.**  Both readings `c₁, c₂` multiples of `4` and clear at `ρ`, and `‖(b₁ − b₂)ρ‖ ≤ 1/4`:
a quarter step clears the odd readings and keeps the multiples of `4`. -/
theorem c_finish {c₁ c₂ : ℕ} (hc₁ : 4 ∣ c₁) (hc₂ : 4 ∣ c₂) {b₁ b₂ : ℤ} (hb₁ : 4 ∣ b₁ - 1)
    (hb₂ : 4 ∣ b₂ - 1) {ρ : ℝ} (h₁ : (8 : ℝ)⁻¹ ≤ circDist ((c₁ : ℝ) * ρ))
    (h₂ : (8 : ℝ)⁻¹ ≤ circDist ((c₂ : ℝ) * ρ))
    (hd : circDist ((b₁ : ℝ) * ρ - (b₂ : ℝ) * ρ) ≤ (4 : ℝ)⁻¹) :
    ∃ τ : ℝ, (8 : ℝ)⁻¹ ≤ circDist ((c₁ : ℝ) * τ) ∧ (8 : ℝ)⁻¹ ≤ circDist ((c₂ : ℝ) * τ) ∧
      (4 : ℝ)⁻¹ ≤ circDist ((b₁ : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((b₂ : ℝ) * τ) := by
  obtain ⟨K, hK1, hK2⟩ := exists_quarter_fit hd
  exact ⟨ρ + (K : ℝ) / 4, by rw [rot_four_dvd hc₁]; exact h₁, by rw [rot_four_dvd hc₂]; exact h₂,
    by rw [rot_one_mod_four hb₁]; exact hK1, by rw [rot_one_mod_four hb₂]; exact hK2⟩

/-! ## Lemma Q: a count on a grid

`[PROVISIONAL: counting tool; supports: existence of s in Lemma Q, hence case C of M(2,2)]` in the
source.  Here the count is carried out exactly on the grid `(1/L)ℤ`, `L = 32·A₁·A₂`, over one period
`[0, D)`: the window `‖s‖ ≤ 1/4` holds at `D·(L/2 + 1)` grid points, the open arcs `‖Aᵢ s/D‖ < 1/8`
at `L·D/4 − Aᵢ` each, and `L·D/2 − A₁ − A₂ < D·(L/2 + 1)`. -/

/-- A periodic condition counted over `m` periods. -/
theorem card_filter_mod (P m : ℕ) (f : ℕ → Prop) [DecidablePred f] :
    ((Finset.range (m * P)).filter (fun n => f (n % P))).card
      = m * ((Finset.range P).filter f).card := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← Nat.count_eq_card_filter_range] at ih ⊢
    rw [show (m + 1) * P = m * P + P by ring, Nat.count_add, ih, add_mul, one_mul]
    congr 1
    try simp only [Nat.count_eq_card_filter_range]
    congr 1
    apply Finset.filter_congr
    intro k hk
    rw [Nat.mul_comm m P, Nat.mul_add_mod, Nat.mod_eq_of_lt (Finset.mem_range.mp hk)]

/-- The closed window `‖r/(4a)‖ ≤ 1/4` holds at `2a + 1` residues. -/
theorem card_window_ge (a : ℕ) (ha : 0 < a) :
    2 * a + 1 ≤ ((Finset.range (4 * a)).filter (fun r => r ≤ a ∨ 3 * a ≤ r)).card := by
  have hsub : Finset.range (a + 1) ∪ Finset.Ico (3 * a) (4 * a)
      ⊆ (Finset.range (4 * a)).filter (fun r => r ≤ a ∨ 3 * a ≤ r) := by
    intro r hr
    rcases Finset.mem_union.mp hr with h | h
    · have := Finset.mem_range.mp h
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Or.inl (by omega)⟩
    · have := Finset.mem_Ico.mp h
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Or.inr (by omega)⟩
  have hdisj : Disjoint (Finset.range (a + 1)) (Finset.Ico (3 * a) (4 * a)) := by
    rw [Finset.disjoint_left]
    intro r h1 h2
    have := Finset.mem_range.mp h1
    have := Finset.mem_Ico.mp h2
    omega
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_range, Nat.card_Ico] at this
  omega

/-- The open arc `‖r/(8b)‖ < 1/8` holds at `2b − 1` residues. -/
theorem card_arc_le (b : ℕ) :
    ((Finset.range (8 * b)).filter (fun r => r < b ∨ 7 * b < r)).card ≤ 2 * b - 1 := by
  have hsub : (Finset.range (8 * b)).filter (fun r => r < b ∨ 7 * b < r)
      ⊆ Finset.range b ∪ Finset.Ico (7 * b + 1) (8 * b) := by
    intro r hr
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hr
    have := Finset.mem_range.mp h1
    rcases h2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr h)
    · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega, this⟩)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (Finset.range b) (Finset.Ico (7 * b + 1) (8 * b))
  rw [Finset.card_range, Nat.card_Ico] at h2
  omega

/-- A grid point split into whole periods and a residue. -/
theorem nat_div_real (n P : ℕ) (hP : 0 < P) :
    (n : ℝ) / P = ((n / P : ℕ) : ℝ) + ((n % P : ℕ) : ℝ) / P := by
  have h := Nat.div_add_mod n P
  have hR : (n : ℝ) = (P : ℝ) * ((n / P : ℕ) : ℝ) + ((n % P : ℕ) : ℝ) := by exact_mod_cast h.symm
  have hPR : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  rw [hR]; field_simp

/-- A residue in `[b, 7b]` modulo `8b` reads at least `1/8` from the integers. -/
theorem eighth_of_mod {n b : ℕ} (hb : 0 < b) (h : b ≤ n % (8 * b) ∧ n % (8 * b) ≤ 7 * b) :
    (8 : ℝ)⁻¹ ≤ circDist ((n : ℝ) / ((8 * b : ℕ) : ℝ)) := by
  have hP : 0 < 8 * b := by omega
  have hPR : (0 : ℝ) < ((8 * b : ℕ) : ℝ) := by exact_mod_cast hP
  rw [nat_div_real n (8 * b) hP]
  have hl : (b : ℝ) ≤ ((n % (8 * b) : ℕ) : ℝ) := by exact_mod_cast h.1
  have hr : ((n % (8 * b) : ℕ) : ℝ) ≤ 7 * b := by exact_mod_cast h.2
  have e8 : ((8 * b : ℕ) : ℝ) = 8 * (b : ℝ) := by push_cast; ring
  refine LRC.MirrorCentre.circDist_ge_of_window (m := ((n / (8 * b) : ℕ) : ℤ)) ?_ ?_ (by norm_num)
  · simp only [Int.cast_natCast]
    have : (8 : ℝ)⁻¹ ≤ ((n % (8 * b) : ℕ) : ℝ) / ((8 * b : ℕ) : ℝ) := by
      rw [le_div_iff₀ hPR, e8]; linarith
    linarith
  · simp only [Int.cast_natCast]
    have : ((n % (8 * b) : ℕ) : ℝ) / ((8 * b : ℕ) : ℝ) ≤ 1 - (8 : ℝ)⁻¹ := by
      rw [div_le_iff₀ hPR, e8]; linarith
    linarith

/-- A residue in the closed window modulo `4a` reads at most `1/4` from the integers. -/
theorem quarter_le_of_mod {n a : ℕ} (ha : 0 < a) (h : n % (4 * a) ≤ a ∨ 3 * a ≤ n % (4 * a)) :
    circDist ((n : ℝ) / ((4 * a : ℕ) : ℝ)) ≤ (4 : ℝ)⁻¹ := by
  have hP : 0 < 4 * a := by omega
  have hPR : (0 : ℝ) < ((4 * a : ℕ) : ℝ) := by exact_mod_cast hP
  have e4 : ((4 * a : ℕ) : ℝ) = 4 * (a : ℝ) := by push_cast; ring
  have hlt : ((n % (4 * a) : ℕ) : ℝ) < 4 * a := by
    have := Nat.mod_lt n hP
    have : ((n % (4 * a) : ℕ) : ℝ) < ((4 * a : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have h0 : (0 : ℝ) ≤ ((n % (4 * a) : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [nat_div_real n (4 * a) hP]
  rcases h with h | h
  · have hr : ((n % (4 * a) : ℕ) : ℝ) ≤ a := by exact_mod_cast h
    have : ((n % (4 * a) : ℕ) : ℝ) / ((4 * a : ℕ) : ℝ) ≤ (4 : ℝ)⁻¹ := by
      rw [div_le_iff₀ hPR, e4]; linarith
    have : 0 ≤ ((n % (4 * a) : ℕ) : ℝ) / ((4 * a : ℕ) : ℝ) := div_nonneg h0 hPR.le
    exact circDist_le_of_near (m := ((n / (4 * a) : ℕ) : ℤ)) (by simp only [Int.cast_natCast]; linarith)
      (by simp only [Int.cast_natCast]; linarith)
  · have hr : 3 * (a : ℝ) ≤ ((n % (4 * a) : ℕ) : ℝ) := by exact_mod_cast h
    have : 1 - (4 : ℝ)⁻¹ ≤ ((n % (4 * a) : ℕ) : ℝ) / ((4 * a : ℕ) : ℝ) := by
      rw [le_div_iff₀ hPR, e4]; linarith
    have : ((n % (4 * a) : ℕ) : ℝ) / ((4 * a : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_iff₀ hPR]; linarith
    exact circDist_le_of_near (m := ((n / (4 * a) : ℕ) : ℤ) + 1)
      (by simp only [Int.cast_add, Int.cast_natCast, Int.cast_one]; linarith)
      (by simp only [Int.cast_add, Int.cast_natCast, Int.cast_one]; linarith)

/-- **Lemma Q.**  For positive integers `A₁, A₂, D` there is `s` with `‖s‖ ≤ 1/4` and
`‖Aᵢ·s/D‖ ≥ 1/8`, `i = 1, 2`. -/
theorem exists_grid_point (D A₁ A₂ : ℕ) (hD : 0 < D) (h1 : 0 < A₁) (h2 : 0 < A₂) :
    ∃ s : ℝ, circDist s ≤ (4 : ℝ)⁻¹ ∧ (8 : ℝ)⁻¹ ≤ circDist ((A₁ : ℝ) * s / D) ∧
      (8 : ℝ)⁻¹ ≤ circDist ((A₂ : ℝ) * s / D) := by
  classical
  set a := 8 * A₁ * A₂ with ha
  set b₁ := 4 * A₂ * D with hb₁
  set b₂ := 4 * A₁ * D with hb₂
  have hapos : 0 < a := by positivity
  have hb₁pos : 0 < b₁ := by positivity
  have hb₂pos : 0 < b₂ := by positivity
  set N := D * (4 * a) with hN
  have hN1 : N = A₁ * (8 * b₁) := by rw [hN, ha, hb₁]; ring
  have hN2 : N = A₂ * (8 * b₂) := by rw [hN, ha, hb₂]; ring
  set W := (Finset.range N).filter (fun n => (fun r => r ≤ a ∨ 3 * a ≤ r) (n % (4 * a))) with hW
  set B₁ := (Finset.range N).filter (fun n => (fun r => r < b₁ ∨ 7 * b₁ < r) (n % (8 * b₁))) with hB₁
  set B₂ := (Finset.range N).filter (fun n => (fun r => r < b₂ ∨ 7 * b₂ < r) (n % (8 * b₂))) with hB₂
  have hWc : 2 * a * D + D ≤ W.card := by
    have h := card_filter_mod (4 * a) D (fun r => r ≤ a ∨ 3 * a ≤ r)
    rw [← hN] at h
    rw [hW, h]
    have := card_window_ge a hapos
    nlinarith
  have hB₁c : B₁.card + A₁ ≤ 2 * b₁ * A₁ := by
    have h := card_filter_mod (8 * b₁) A₁ (fun r => r < b₁ ∨ 7 * b₁ < r)
    rw [← hN1] at h
    rw [hB₁, h]
    have := card_arc_le b₁
    have h3 : ((Finset.range (8 * b₁)).filter (fun r => r < b₁ ∨ 7 * b₁ < r)).card + 1 ≤ 2 * b₁ := by
      omega
    nlinarith
  have hB₂c : B₂.card + A₂ ≤ 2 * b₂ * A₂ := by
    have h := card_filter_mod (8 * b₂) A₂ (fun r => r < b₂ ∨ 7 * b₂ < r)
    rw [← hN2] at h
    rw [hB₂, h]
    have := card_arc_le b₂
    have h3 : ((Finset.range (8 * b₂)).filter (fun r => r < b₂ ∨ 7 * b₂ < r)).card + 1 ≤ 2 * b₂ := by
      omega
    nlinarith
  have hex : ∃ n ∈ W, n ∉ B₁ ∪ B₂ := by
    by_contra hne
    push Not at hne
    have hsub : W ⊆ B₁ ∪ B₂ := fun n hn => hne n hn
    have := Finset.card_le_card hsub
    have := Finset.card_union_le B₁ B₂
    have e1 : 2 * b₁ * A₁ = 8 * (A₁ * A₂ * D) := by rw [hb₁]; ring
    have e2 : 2 * b₂ * A₂ = 8 * (A₁ * A₂ * D) := by rw [hb₂]; ring
    have e3 : 2 * a * D = 16 * (A₁ * A₂ * D) := by rw [ha]; ring
    rw [e1] at hB₁c
    rw [e2] at hB₂c
    rw [e3] at hWc
    generalize A₁ * A₂ * D = X at *
    omega
  obtain ⟨n, hnW, hnB⟩ := hex
  have hnB₁ : n ∉ B₁ := fun h => hnB (Finset.mem_union_left _ h)
  have hnB₂ : n ∉ B₂ := fun h => hnB (Finset.mem_union_right _ h)
  have hnN : n ∈ Finset.range N := (Finset.mem_filter.mp hnW).1
  have hwin := (Finset.mem_filter.mp hnW).2
  have hg₁ : b₁ ≤ n % (8 * b₁) ∧ n % (8 * b₁) ≤ 7 * b₁ := by
    by_contra h
    exact hnB₁ (Finset.mem_filter.mpr ⟨hnN, by simp only; omega⟩)
  have hg₂ : b₂ ≤ n % (8 * b₂) ∧ n % (8 * b₂) ≤ 7 * b₂ := by
    by_contra h
    exact hnB₂ (Finset.mem_filter.mpr ⟨hnN, by simp only; omega⟩)
  refine ⟨(n : ℝ) / ((4 * a : ℕ) : ℝ), quarter_le_of_mod hapos hwin, ?_, ?_⟩
  · have heq : (A₁ : ℝ) * ((n : ℝ) / ((4 * a : ℕ) : ℝ)) / D = (n : ℝ) / ((8 * b₁ : ℕ) : ℝ) := by
      have hc : ((D * (4 * a) : ℕ) : ℝ) = ((A₁ * (8 * b₁) : ℕ) : ℝ) := by rw [← hN, ← hN1]
      push_cast at hc ⊢
      have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
      have haR : (a : ℝ) ≠ 0 := by exact_mod_cast hapos.ne'
      have hbR : (b₁ : ℝ) ≠ 0 := by exact_mod_cast hb₁pos.ne'
      field_simp
      linear_combination (-(n : ℝ)) * hc
    rw [heq]; exact eighth_of_mod hb₁pos hg₁
  · have heq : (A₂ : ℝ) * ((n : ℝ) / ((4 * a : ℕ) : ℝ)) / D = (n : ℝ) / ((8 * b₂ : ℕ) : ℝ) := by
      have hc : ((D * (4 * a) : ℕ) : ℝ) = ((A₂ * (8 * b₂) : ℕ) : ℝ) := by rw [← hN, ← hN2]
      push_cast at hc ⊢
      have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
      have haR : (a : ℝ) ≠ 0 := by exact_mod_cast hapos.ne'
      have hbR : (b₂ : ℝ) ≠ 0 := by exact_mod_cast hb₂pos.ne'
      field_simp
      linear_combination (-(n : ℝ)) * hc
    rw [heq]; exact eighth_of_mod hb₂pos hg₂

/-! ## The cases of M(2,2)

Throughout, `b₁ > b₂` are the odd readings written `≡ 1 (mod 4)` (`exists_one_mod_four`), and
`d = b₁ − b₂`, a positive multiple of `4`. -/

/-- **Case A** (`4` divides neither reading at `1/8`): `τ = 1/4`. -/
theorem case_A {c₁ c₂ : ℕ} (hc₁ : ¬ 4 ∣ c₁) (hc₂ : ¬ 4 ∣ c₂) {b₁ b₂ : ℤ} (hb₁ : 4 ∣ b₁ - 1)
    (hb₂ : 4 ∣ b₂ - 1) :
    ∃ τ : ℝ, (8 : ℝ)⁻¹ ≤ circDist ((c₁ : ℝ) * τ) ∧ (8 : ℝ)⁻¹ ≤ circDist ((c₂ : ℝ) * τ) ∧
      (4 : ℝ)⁻¹ ≤ circDist ((b₁ : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((b₂ : ℝ) * τ) := by
  refine ⟨1 / 4, ?_, ?_, ?_, ?_⟩
  · rw [show (c₁ : ℝ) * (1 / 4) = (c₁ : ℝ) / 4 by ring]
    exact le_trans (by norm_num) (quarter_of_not_four_dvd hc₁)
  · rw [show (c₂ : ℝ) * (1 / 4) = (c₂ : ℝ) / 4 by ring]
    exact le_trans (by norm_num) (quarter_of_not_four_dvd hc₂)
  · rw [show (b₁ : ℝ) * (1 / 4) = (b₁ : ℝ) / 4 by ring]; exact quarter_of_one_mod_four hb₁
  · rw [show (b₂ : ℝ) * (1 / 4) = (b₂ : ℝ) / 4 by ring]; exact quarter_of_one_mod_four hb₂

/-- **Case C** (`4` divides both readings at `1/8`): Lemma Q at `D = d`, then FIT2 and ROT. -/
theorem case_C {c₁ c₂ : ℕ} (hc₁ : 4 ∣ c₁) (hc₂ : 4 ∣ c₂) (hc₁p : 0 < c₁) (hc₂p : 0 < c₂)
    {b₁ b₂ : ℤ} (hb₁ : 4 ∣ b₁ - 1) (hb₂ : 4 ∣ b₂ - 1) (hlt : b₂ < b₁) :
    ∃ τ : ℝ, (8 : ℝ)⁻¹ ≤ circDist ((c₁ : ℝ) * τ) ∧ (8 : ℝ)⁻¹ ≤ circDist ((c₂ : ℝ) * τ) ∧
      (4 : ℝ)⁻¹ ≤ circDist ((b₁ : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((b₂ : ℝ) * τ) := by
  obtain ⟨D, hD⟩ : ∃ D : ℕ, (D : ℤ) = b₁ - b₂ := ⟨(b₁ - b₂).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hDpos : 0 < D := by omega
  obtain ⟨s, hs, h1, h2⟩ := exists_grid_point D c₁ c₂ hDpos hc₁p hc₂p
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hDpos.ne'
  have hDR' : (b₁ : ℝ) - b₂ = D := by exact_mod_cast hD.symm
  refine c_finish hc₁ hc₂ hb₁ hb₂ (ρ := s / D) ?_ ?_ ?_
  · rw [show (c₁ : ℝ) * (s / D) = (c₁ : ℝ) * s / D by ring]; exact h1
  · rw [show (c₂ : ℝ) * (s / D) = (c₂ : ℝ) * s / D by ring]; exact h2
  · have : (b₁ : ℝ) * (s / D) - (b₂ : ℝ) * (s / D) = s := by
      rw [← sub_mul, hDR']; field_simp
    rw [this]; exact hs

/-- A proper divisor: `gcd(r, q)/q ≤ 1/2` when `q ∤ r`. -/
theorem gcd_div_le_half (r : ℤ) {q : ℕ} (hq : 0 < q) (hdvd : ¬ (q : ℤ) ∣ r) :
    (Int.gcd r q : ℝ) / q ≤ 1 / 2 := by
  have hg : 2 * Int.gcd r q ≤ q := by
    have hd : Int.gcd r q ∣ q := by
      have := Int.gcd_dvd_right r (q : ℤ)
      exact_mod_cast this
    obtain ⟨k, hk⟩ := hd
    have hne : Int.gcd r q ≠ q := by
      intro he
      apply hdvd
      have := Int.gcd_dvd_left r (q : ℤ)
      rw [he] at this
      exact this
    rcases k with _ | _ | k
    · omega
    · simp at hk; exact absurd hk.symm hne
    · nlinarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [div_le_iff₀ hqR]
  have : (2 * Int.gcd r q : ℝ) ≤ q := by exact_mod_cast hg
  linarith

/-- **Case DE1** (`4 ∣ c₁`, `4 ∤ c₂`, `d ∤ c₁`): `ρ = k/d` with `‖c₁k/d‖ ≥ 1/4` (coset lemma); the two
odd readings then differ by the integer `k`, so they sit in one closed cell. -/
theorem case_DE1 {c₁ c₂ : ℕ} (hc₁ : 4 ∣ c₁) (hc₂ : ¬ 4 ∣ c₂) {b₁ b₂ : ℤ} (hb₁ : 4 ∣ b₁ - 1)
    (hb₂ : 4 ∣ b₂ - 1) {d : ℕ} (hd : (d : ℤ) = b₁ - b₂) (hdpos : 0 < d)
    (hndvd : ¬ (d : ℤ) ∣ (c₁ : ℤ)) :
    ∃ τ : ℝ, (8 : ℝ)⁻¹ ≤ circDist ((c₁ : ℝ) * τ) ∧ (8 : ℝ)⁻¹ ≤ circDist ((c₂ : ℝ) * τ) ∧
      (4 : ℝ)⁻¹ ≤ circDist ((b₁ : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((b₂ : ℝ) * τ) := by
  obtain ⟨k, hk⟩ := exists_coset_quarter 0 (c₁ : ℤ) hdpos hndvd
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hρ : (8 : ℝ)⁻¹ ≤ circDist ((c₁ : ℝ) * ((k : ℝ) / d)) := by
    have : (c₁ : ℝ) * ((k : ℝ) / d) = 0 + (k : ℝ) * ((c₁ : ℤ) : ℝ) / d := by push_cast; ring
    rw [this]; exact le_trans (by norm_num) hk
  have hb : (b₁ : ℝ) = b₂ + d := by
    have : ((d : ℤ) : ℝ) = (b₁ : ℝ) - b₂ := by exact_mod_cast hd
    push_cast at this; linarith
  have h12 : (b₁ : ℝ) * ((k : ℝ) / d) - k = (b₂ : ℝ) * ((k : ℝ) / d) := by
    rw [hb]; field_simp; ring
  set x := (b₂ : ℝ) * ((k : ℝ) / d) with hx
  set w : ℤ := ⌊4 * x⌋ with hw
  have hw1 : (w : ℝ) ≤ 4 * x := Int.floor_le _
  have hw2 : 4 * x < (w : ℝ) + 1 := Int.lt_floor_add_one _
  refine de_finish hc₁ hc₂ hb₁ hb₂ hρ w k 0 ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · rw [h12]; linarith
  · rw [h12]; linarith
  · push_cast; linarith
  · push_cast; linarith

/-- **Case DE2** (`c₁ = t·d`, `d ∤ 4b₂`): `ρ = (k + ξ)/d`, `ξ = 1/(8t)`.  Then `c₁ρ = tk + 1/8`, the two
odd readings are `ξ` apart, and as `k` varies `4b₂ρ` runs over a coset of spacing `≤ 1/2` (coset lemma),
so both lie in one closed quarter cell. -/
theorem case_DE2 {c₁ c₂ : ℕ} (hc₁ : 4 ∣ c₁) (hc₂ : ¬ 4 ∣ c₂) {b₁ b₂ : ℤ} (hb₁ : 4 ∣ b₁ - 1)
    (hb₂ : 4 ∣ b₂ - 1) {d t : ℕ} (hd : (d : ℤ) = b₁ - b₂) (hdpos : 0 < d) (htpos : 0 < t)
    (ht : c₁ = t * d) (hndvd : ¬ (d : ℤ) ∣ 4 * b₂) :
    ∃ τ : ℝ, (8 : ℝ)⁻¹ ≤ circDist ((c₁ : ℝ) * τ) ∧ (8 : ℝ)⁻¹ ≤ circDist ((c₂ : ℝ) * τ) ∧
      (4 : ℝ)⁻¹ ≤ circDist ((b₁ : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((b₂ : ℝ) * τ) := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have htR : (0 : ℝ) < t := by exact_mod_cast htpos
  set ξ : ℝ := 1 / (8 * t) with hξ
  have hξ0 : 0 ≤ ξ := by positivity
  have hξ8 : ξ ≤ 1 / 8 := by
    rw [hξ, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (1 : ℝ) ≤ t := by exact_mod_cast htpos
    linarith
  obtain ⟨k, N, h1, h2⟩ := exists_coset_window (4 * (b₂ : ℝ) * ξ / d) 0 (4 * b₂) hdpos
  have hsp := gcd_div_le_half (4 * b₂) hdpos hndvd
  set ρ : ℝ := ((k : ℝ) + ξ) / d with hρ
  have key : 4 * (b₂ : ℝ) * ξ / d + (k : ℝ) * ((4 * b₂ : ℤ) : ℝ) / d = 4 * ((b₂ : ℝ) * ρ) := by
    rw [hρ]; push_cast; field_simp; ring
  rw [key] at h1 h2
  have hb : (b₁ : ℝ) = b₂ + d := by
    have : ((d : ℤ) : ℝ) = (b₁ : ℝ) - b₂ := by exact_mod_cast hd
    push_cast at this; linarith
  have h12 : (b₁ : ℝ) * ρ - k = (b₂ : ℝ) * ρ + ξ := by
    rw [hb, hρ]; field_simp; ring
  have hc : (c₁ : ℝ) * ρ = (((t * k : ℤ)) : ℝ) + 1 / 8 := by
    rw [ht, hρ, hξ]; push_cast; field_simp
  have hcρ : (8 : ℝ)⁻¹ ≤ circDist ((c₁ : ℝ) * ρ) := by
    rw [hc, add_comm, circDist_add_int]
    exact LRC.MirrorCentre.circDist_ge_of_window (m := 0) (by norm_num) (by norm_num) (by norm_num)
  refine de_finish hc₁ hc₂ hb₁ hb₂ hcρ N k 0 ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · rw [h12]; linarith
  · rw [h12]; linarith
  · push_cast; linarith
  · push_cast; linarith

/-- **DE3, the displacement.**  For `t, q ≥ 1` there is `ξ ≥ 0` with `‖tξ‖ ≥ 1/8` and both points
`qξ/4`, `(q+4)ξ/4` in one closed quarter cell.  If `q + 4 ≤ 8t`, `ξ = 1/(8t)`; otherwise
`ξ = n/q` with `n = ⌈q/(8t)⌉` (this replaces the source's choice `n = ⌈1/(8r)⌉`, `r = ‖t/q‖`). -/
theorem de3_xi (t q : ℕ) (ht : 0 < t) (hq : 0 < q) :
    ∃ ξ : ℝ, ∃ w : ℤ, (8 : ℝ)⁻¹ ≤ circDist ((t : ℝ) * ξ) ∧ 0 ≤ ξ ∧
      (w : ℝ) / 4 ≤ (q : ℝ) * ξ / 4 ∧ ((q : ℝ) + 4) * ξ / 4 ≤ ((w : ℝ) + 1) / 4 := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  by_cases hq4 : q + 4 ≤ 8 * t
  · refine ⟨1 / (8 * t), 0, ?_, by positivity, ?_, ?_⟩
    · rw [show (t : ℝ) * (1 / (8 * t)) = 1 / 8 by field_simp]
      exact LRC.MirrorCentre.circDist_ge_of_window (m := 0) (by norm_num) (by norm_num) (by norm_num)
    · push_cast; rw [zero_div]; positivity
    · have h : ((q : ℝ) + 4) ≤ 8 * t := by exact_mod_cast hq4
      push_cast
      rw [show ((q : ℝ) + 4) * (1 / (8 * t)) / 4 = ((q : ℝ) + 4) / (32 * t) by field_simp; ring,
        div_le_iff₀ (by positivity)]
      linarith
  · push Not at hq4
    set n := (q + 8 * t - 1) / (8 * t) with hn
    have hF1 : n * (8 * t) ≤ q + 8 * t - 1 := Nat.div_mul_le_self _ _
    have hF2 : q + 8 * t - 1 < n * (8 * t) + 8 * t := Nat.lt_div_mul_add (by omega)
    have hA : q ≤ n * (8 * t) := by omega
    have hB : n * (8 * t) ≤ 7 * q := by omega
    have hC : 4 * n ≤ q := by
      rcases Nat.lt_or_ge t 2 with h | h
      · have : t = 1 := by omega
        subst this
        omega
      · by_contra hc
        push Not at hc
        have h1 : (q + 1) * (2 * t) ≤ n * (8 * t) := by nlinarith
        have h2 : 2 * 2 * q ≤ 2 * t * q := by nlinarith
        have h3 : (q + 1) * (2 * t) = 2 * t * q + 2 * t := by ring
        omega
    have hAR : (q : ℝ) ≤ (n : ℝ) * (8 * t) := by exact_mod_cast hA
    have hBR : (n : ℝ) * (8 * t) ≤ 7 * q := by exact_mod_cast hB
    have hCR : 4 * (n : ℝ) ≤ q := by exact_mod_cast hC
    refine ⟨(n : ℝ) / q, n, ?_, by positivity, ?_, ?_⟩
    · refine LRC.MirrorCentre.circDist_ge_of_window (m := 0) ?_ ?_ (by norm_num)
      · rw [show (t : ℝ) * ((n : ℝ) / q) = (n : ℝ) * t / q by ring, le_div_iff₀ hqR]
        push_cast; linarith
      · rw [show (t : ℝ) * ((n : ℝ) / q) = (n : ℝ) * t / q by ring, div_le_iff₀ hqR]
        push_cast; linarith
    · rw [show (q : ℝ) * ((n : ℝ) / q) / 4 = (n : ℝ) / 4 by field_simp]
      push_cast; exact le_refl _
    · push_cast
      rw [show ((q : ℝ) + 4) * ((n : ℝ) / q) / 4 = ((q : ℝ) + 4) * n / (4 * q) by field_simp,
        div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith

/-- **Case DE3, both odd readings positive** (`b₂ = g·q`, `b₁ = g·(q + 4)`, `c₁ = 4gt`): `ρ = ξ/(4g)`. -/
theorem case_DE3_pos {c₁ c₂ : ℕ} (hc₁ : 4 ∣ c₁) (hc₂ : ¬ 4 ∣ c₂) {b₁ b₂ : ℤ} (hb₁ : 4 ∣ b₁ - 1)
    (hb₂ : 4 ∣ b₂ - 1) {g t q : ℕ} (hg : 0 < g) (ht : 0 < t) (hq : 0 < q)
    (hc : (c₁ : ℝ) = 4 * g * t) (h₁ : (b₁ : ℝ) = g * (q + 4)) (h₂ : (b₂ : ℝ) = g * q) :
    ∃ τ : ℝ, (8 : ℝ)⁻¹ ≤ circDist ((c₁ : ℝ) * τ) ∧ (8 : ℝ)⁻¹ ≤ circDist ((c₂ : ℝ) * τ) ∧
      (4 : ℝ)⁻¹ ≤ circDist ((b₁ : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((b₂ : ℝ) * τ) := by
  obtain ⟨ξ, w, hξ, hξ0, hw1, hw2⟩ := de3_xi t q ht hq
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have e1 : (b₁ : ℝ) * (ξ / (4 * g)) = ((q : ℝ) + 4) * ξ / 4 := by rw [h₁]; field_simp
  have e2 : (b₂ : ℝ) * (ξ / (4 * g)) = (q : ℝ) * ξ / 4 := by rw [h₂]; field_simp
  have ec : (c₁ : ℝ) * (ξ / (4 * g)) = (t : ℝ) * ξ := by rw [hc]; field_simp
  have hmono : (q : ℝ) * ξ / 4 ≤ ((q : ℝ) + 4) * ξ / 4 := by nlinarith
  refine de_finish hc₁ hc₂ hb₁ hb₂ (by rw [ec]; exact hξ) w 0 0 ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · push_cast; rw [e1]; linarith
  · push_cast; rw [e1]; linarith
  · push_cast; rw [e2]; linarith
  · push_cast; rw [e2]; linarith

/-- **Case DE3, both odd readings negative** (`b₁ = −g·q`, `b₂ = −g·(q + 4)`): `ρ = −ξ/(4g)`. -/
theorem case_DE3_neg {c₁ c₂ : ℕ} (hc₁ : 4 ∣ c₁) (hc₂ : ¬ 4 ∣ c₂) {b₁ b₂ : ℤ} (hb₁ : 4 ∣ b₁ - 1)
    (hb₂ : 4 ∣ b₂ - 1) {g t q : ℕ} (hg : 0 < g) (ht : 0 < t) (hq : 0 < q)
    (hc : (c₁ : ℝ) = 4 * g * t) (h₁ : (b₁ : ℝ) = -(g * q)) (h₂ : (b₂ : ℝ) = -(g * (q + 4))) :
    ∃ τ : ℝ, (8 : ℝ)⁻¹ ≤ circDist ((c₁ : ℝ) * τ) ∧ (8 : ℝ)⁻¹ ≤ circDist ((c₂ : ℝ) * τ) ∧
      (4 : ℝ)⁻¹ ≤ circDist ((b₁ : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((b₂ : ℝ) * τ) := by
  obtain ⟨ξ, w, hξ, hξ0, hw1, hw2⟩ := de3_xi t q ht hq
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have e1 : (b₁ : ℝ) * (-ξ / (4 * g)) = (q : ℝ) * ξ / 4 := by rw [h₁]; field_simp
  have e2 : (b₂ : ℝ) * (-ξ / (4 * g)) = ((q : ℝ) + 4) * ξ / 4 := by rw [h₂]; field_simp
  have ec : (c₁ : ℝ) * (-ξ / (4 * g)) = -((t : ℝ) * ξ) := by rw [hc]; field_simp
  have hmono : (q : ℝ) * ξ / 4 ≤ ((q : ℝ) + 4) * ξ / 4 := by nlinarith
  refine de_finish hc₁ hc₂ hb₁ hb₂ (by rw [ec, circDist.symm_neg]; exact hξ) w 0 0 ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · push_cast; rw [e1]; linarith
  · push_cast; rw [e1]; linarith
  · push_cast; rw [e2]; linarith
  · push_cast; rw [e2]; linarith

/-! ### Case DE4: the odd readings `g` and `3g`

`τ = y/g`, `y = n + 1/2 + z`, `0 ≤ z ≤ 1/12`: then `‖y‖ ≥ 5/12`, `‖3y‖ ≥ 1/4`, `c₁τ = 4ty ≡ 4tz`. -/

/-- **DE4, the odd readings.**  `‖y‖ ≥ 1/4` and `‖3y‖ ≥ 1/4` at `y = n + 1/2 + z`, `0 ≤ z ≤ 1/12`. -/
theorem de4_odd (n : ℤ) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 12) :
    (4 : ℝ)⁻¹ ≤ circDist ((n : ℝ) + 1 / 2 + z) ∧
      (4 : ℝ)⁻¹ ≤ circDist (3 * ((n : ℝ) + 1 / 2 + z)) := by
  constructor
  · exact LRC.MirrorCentre.circDist_ge_of_window (m := n) (by linarith) (by linarith) (by norm_num)
  · exact LRC.MirrorCentre.circDist_ge_of_window (m := 3 * n + 1) (by push_cast; linarith)
      (by push_cast; linarith) (by norm_num)

/-- **DE4, assembly.**  `τ = (n + 1/2 + z)/g`. -/
theorem de4_of_y {g t c₂ : ℕ} (hg : 0 < g) (n : ℤ) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 12)
    (hc₁ : (8 : ℝ)⁻¹ ≤ circDist (4 * (t : ℝ) * z))
    (hc₂ : (8 : ℝ)⁻¹ ≤ circDist ((c₂ : ℝ) * ((n : ℝ) + 1 / 2 + z) / g)) :
    ∃ τ : ℝ, (8 : ℝ)⁻¹ ≤ circDist (4 * (g : ℝ) * t * τ) ∧ (8 : ℝ)⁻¹ ≤ circDist ((c₂ : ℝ) * τ) ∧
      (4 : ℝ)⁻¹ ≤ circDist ((g : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist (3 * (g : ℝ) * τ) := by
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  obtain ⟨h1, h3⟩ := de4_odd n hz0 hz1
  refine ⟨((n : ℝ) + 1 / 2 + z) / g, ?_, ?_, ?_, ?_⟩
  · have : 4 * (g : ℝ) * t * (((n : ℝ) + 1 / 2 + z) / g)
        = 4 * (t : ℝ) * z + ((4 * t * n + 2 * t : ℤ) : ℝ) := by
      push_cast; field_simp; ring
    rw [this, circDist_add_int]; exact hc₁
  · rw [show (c₂ : ℝ) * (((n : ℝ) + 1 / 2 + z) / g) = (c₂ : ℝ) * ((n : ℝ) + 1 / 2 + z) / g by ring]
    exact hc₂
  · rw [show (g : ℝ) * (((n : ℝ) + 1 / 2 + z) / g) = (n : ℝ) + 1 / 2 + z by field_simp]; exact h1
  · rw [show 3 * (g : ℝ) * (((n : ℝ) + 1 / 2 + z) / g) = 3 * ((n : ℝ) + 1 / 2 + z) by field_simp]
    exact h3

/-- **DE4a** (`g ∤ c₂`): `z = 1/(32t)`, and `n` from the coset lemma for `c₂/g`. -/
theorem de4a {g t c₂ : ℕ} (hg : 0 < g) (ht : 0 < t) (hndvd : ¬ (g : ℤ) ∣ (c₂ : ℤ)) :
    ∃ n : ℤ, ∃ z : ℝ, 0 ≤ z ∧ z ≤ 1 / 12 ∧ (8 : ℝ)⁻¹ ≤ circDist (4 * (t : ℝ) * z) ∧
      (8 : ℝ)⁻¹ ≤ circDist ((c₂ : ℝ) * ((n : ℝ) + 1 / 2 + z) / g) := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  obtain ⟨n, hn⟩ := exists_coset_quarter ((c₂ : ℝ) * (1 / 2 + 1 / (32 * t)) / g) (c₂ : ℤ) hg hndvd
  refine ⟨n, 1 / (32 * t), by positivity, ?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  · rw [show 4 * (t : ℝ) * (1 / (32 * t)) = 1 / 8 by field_simp; ring]
    exact LRC.MirrorCentre.circDist_ge_of_window (m := 0) (by norm_num) (by norm_num) (by norm_num)
  · have : (c₂ : ℝ) * ((n : ℝ) + 1 / 2 + 1 / (32 * t)) / g
        = (c₂ : ℝ) * (1 / 2 + 1 / (32 * t)) / g + (n : ℝ) * ((c₂ : ℤ) : ℝ) / g := by
      push_cast; ring
    rw [this]; exact le_trans (by norm_num) hn

/-- **DE4b, `e` odd, `e ≤ 12t`**: `z = 1/(32t)`. -/
theorem de4b_odd_small {t e : ℕ} (ht : 0 < t) (he : e % 2 = 1) (hle : e ≤ 12 * t) :
    ∃ z : ℝ, 0 ≤ z ∧ z ≤ 1 / 12 ∧ (8 : ℝ)⁻¹ ≤ circDist (4 * (t : ℝ) * z) ∧
      (8 : ℝ)⁻¹ ≤ circDist ((e : ℝ) * (1 / 2 + z)) := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  obtain ⟨j, hj⟩ : ∃ j : ℕ, e = 2 * j + 1 := ⟨e / 2, by omega⟩
  have hleR : (e : ℝ) ≤ 12 * t := by exact_mod_cast hle
  refine ⟨1 / (32 * t), by positivity, ?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  · rw [show 4 * (t : ℝ) * (1 / (32 * t)) = 1 / 8 by field_simp; ring]
    exact LRC.MirrorCentre.circDist_ge_of_window (m := 0) (by norm_num) (by norm_num) (by norm_num)
  · have h0 : 0 ≤ (e : ℝ) / (32 * t) := by positivity
    have h1 : (e : ℝ) / (32 * t) ≤ 3 / 8 := by rw [div_le_iff₀ (by positivity)]; linarith
    have heq : (e : ℝ) * (1 / 2 + 1 / (32 * t)) = (j : ℝ) + 1 / 2 + (e : ℝ) / (32 * t) := by
      have : (e : ℝ) = 2 * j + 1 := by rw [hj]; push_cast; ring
      rw [this]; field_simp
    rw [heq]
    exact LRC.MirrorCentre.circDist_ge_of_window (m := j) (by push_cast; linarith)
      (by push_cast; linarith) (by norm_num)

/-- **DE4b, `e` odd, `e > 12t`**: sweep `e` over `[1/(32t), 1/(32t) + 1/(4e)]`, on which `c₁` is clear. -/
theorem de4b_odd_large {t e : ℕ} (ht : 0 < t) (hlt : 12 * t < e) :
    ∃ z : ℝ, 0 ≤ z ∧ z ≤ 1 / 12 ∧ (8 : ℝ)⁻¹ ≤ circDist (4 * (t : ℝ) * z) ∧
      (8 : ℝ)⁻¹ ≤ circDist ((e : ℝ) * (1 / 2 + z)) := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hlt' : 12 * (t : ℝ) + 1 ≤ e := by exact_mod_cast hlt
  have heR : (0 : ℝ) < e := by linarith
  obtain ⟨z, hz1, hz2, hz⟩ := exists_sweep ((e : ℝ) / 2) (lo := 1 / (32 * t))
    (hi := 1 / (32 * t) + 1 / (4 * e)) heR (by rw [add_sub_cancel_left]; field_simp; norm_num)
  have hlo : 0 < 1 / (32 * (t : ℝ)) := by positivity
  have hA : 1 / (32 * (t : ℝ)) ≤ 1 / 32 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hB : 1 / (4 * (e : ℝ)) ≤ 1 / 52 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have h4lo : 4 * (t : ℝ) * (1 / (32 * t)) = 1 / 8 := by field_simp; ring
  have h4hi : 4 * (t : ℝ) * (1 / (4 * e)) ≤ 1 / 12 := by
    rw [show 4 * (t : ℝ) * (1 / (4 * e)) = (t : ℝ) / e by field_simp, div_le_iff₀ heR]; linarith
  have hl : 4 * (t : ℝ) * (1 / (32 * t)) ≤ 4 * (t : ℝ) * z :=
    mul_le_mul_of_nonneg_left hz1 (by positivity)
  have hr : 4 * (t : ℝ) * z ≤ 4 * (t : ℝ) * (1 / (32 * t) + 1 / (4 * e)) :=
    mul_le_mul_of_nonneg_left hz2 (by positivity)
  rw [mul_add] at hr
  refine ⟨z, by linarith, by linarith, ?_, ?_⟩
  · exact LRC.MirrorCentre.circDist_ge_of_window (m := 0) (by push_cast; linarith)
      (by push_cast; linarith) (by norm_num)
  · rw [show (e : ℝ) * (1 / 2 + z) = (e : ℝ) / 2 + (e : ℝ) * z by ring]; exact hz

/-- **DE4b, `e ≡ 2 (mod 4)`, `3 ∤ t`**: `z = 1/12` (`‖t/3‖ = 1/3`, `e/12` an odd multiple of `1/6`). -/
theorem de4b_two_not3 {t e : ℕ} (he : e % 4 = 2) (h3 : ¬ 3 ∣ t) :
    ∃ z : ℝ, 0 ≤ z ∧ z ≤ 1 / 12 ∧ (8 : ℝ)⁻¹ ≤ circDist (4 * (t : ℝ) * z) ∧
      (8 : ℝ)⁻¹ ≤ circDist ((e : ℝ) * (1 / 2 + z)) := by
  refine ⟨1 / 12, by norm_num, le_refl _, ?_, ?_⟩
  · obtain ⟨k, r, hr, hk⟩ : ∃ k r : ℕ, (r = 1 ∨ r = 2) ∧ t = 3 * k + r :=
      ⟨t / 3, t % 3, by omega, by omega⟩
    rw [hk]
    rcases hr with rfl | rfl <;>
      exact LRC.MirrorCentre.circDist_ge_of_window (m := k) (by push_cast; linarith)
        (by push_cast; linarith) (by norm_num)
  · obtain ⟨k, r, hr, hk⟩ : ∃ k r : ℕ, (r = 2 ∨ r = 6 ∨ r = 10) ∧ e = 12 * k + r :=
      ⟨e / 12, e % 12, by omega, by omega⟩
    rw [hk]
    rcases hr with rfl | rfl | rfl
    · exact LRC.MirrorCentre.circDist_ge_of_window (m := 7 * k + 1) (by push_cast; linarith)
        (by push_cast; linarith) (by norm_num)
    · exact LRC.MirrorCentre.circDist_ge_of_window (m := 7 * k + 3) (by push_cast; linarith)
        (by push_cast; linarith) (by norm_num)
    · exact LRC.MirrorCentre.circDist_ge_of_window (m := 7 * k + 5) (by push_cast; linarith)
        (by push_cast; linarith) (by norm_num)

/-- **DE4b, `e ≡ 2 (mod 4)`, `t = 3s`, `e ≥ 4s`**: sweep `e` over `[1/(96s), 1/(96s) + 1/(4e)]`. -/
theorem de4b_two_big {s e : ℕ} (hs : 0 < s) (hle : 4 * s ≤ e) :
    ∃ z : ℝ, 0 ≤ z ∧ z ≤ 1 / 12 ∧ (8 : ℝ)⁻¹ ≤ circDist (4 * ((3 * s : ℕ) : ℝ) * z) ∧
      (8 : ℝ)⁻¹ ≤ circDist ((e : ℝ) * (1 / 2 + z)) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hleR : 4 * (s : ℝ) ≤ e := by exact_mod_cast hle
  have heR : (0 : ℝ) < e := by linarith
  obtain ⟨z, hz1, hz2, hz⟩ := exists_sweep ((e : ℝ) / 2) (lo := 1 / (96 * s))
    (hi := 1 / (96 * s) + 1 / (4 * e)) heR (by rw [add_sub_cancel_left]; field_simp; norm_num)
  have hlo : 0 < 1 / (96 * (s : ℝ)) := by positivity
  have hB : 1 / (4 * (e : ℝ)) ≤ 1 / (16 * s) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
  have hC : 1 / (96 * (s : ℝ)) + 1 / (16 * s) ≤ 1 / 12 := by
    rw [show 1 / (96 * (s : ℝ)) + 1 / (16 * s) = 7 / (96 * s) by field_simp; ring,
      div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h4lo : 12 * (s : ℝ) * (1 / (96 * s)) = 1 / 8 := by field_simp; ring
  have h4hi : 12 * (s : ℝ) * (1 / (4 * e)) ≤ 3 / 4 := by
    rw [show 12 * (s : ℝ) * (1 / (4 * e)) = 3 * (s : ℝ) / e by field_simp; ring, div_le_iff₀ heR]
    linarith
  have hl : 12 * (s : ℝ) * (1 / (96 * s)) ≤ 12 * (s : ℝ) * z :=
    mul_le_mul_of_nonneg_left hz1 (by positivity)
  have hr : 12 * (s : ℝ) * z ≤ 12 * (s : ℝ) * (1 / (96 * s) + 1 / (4 * e)) :=
    mul_le_mul_of_nonneg_left hz2 (by positivity)
  rw [mul_add] at hr
  refine ⟨z, by linarith, by linarith, ?_, ?_⟩
  · rw [show 4 * ((3 * s : ℕ) : ℝ) * z = 12 * (s : ℝ) * z by push_cast; ring]
    exact LRC.MirrorCentre.circDist_ge_of_window (m := 0) (by push_cast; linarith)
      (by push_cast; linarith) (by norm_num)
  · rw [show (e : ℝ) * (1 / 2 + z) = (e : ℝ) / 2 + (e : ℝ) * z by ring]; exact hz

/-- **DE4b, `e ≡ 2 (mod 4)`, `t = 3s`, `e < 4s`**: sweep `12s` over `[1/(8e), 1/(8e) + 1/(48s)]`, on
which `e` is clear. -/
theorem de4b_two_small {s e : ℕ} (hs : 0 < s) (he : e % 4 = 2) (hlt : e < 4 * s) :
    ∃ z : ℝ, 0 ≤ z ∧ z ≤ 1 / 12 ∧ (8 : ℝ)⁻¹ ≤ circDist (4 * ((3 * s : ℕ) : ℝ) * z) ∧
      (8 : ℝ)⁻¹ ≤ circDist ((e : ℝ) * (1 / 2 + z)) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hltR : (e : ℝ) ≤ 4 * s := by exact_mod_cast hlt.le
  obtain ⟨j, hj⟩ : ∃ j : ℕ, e = 2 * j := ⟨e / 2, by omega⟩
  have he2 : (2 : ℝ) ≤ e := by exact_mod_cast (show 2 ≤ e by omega)
  have heR : (0 : ℝ) < e := by linarith
  have h12 : (0 : ℝ) < 12 * s := by positivity
  obtain ⟨z, hz1, hz2, hz⟩ := exists_sweep 0 (lo := 1 / (8 * e))
    (hi := 1 / (8 * e) + 1 / (48 * s)) h12 (by rw [add_sub_cancel_left]; field_simp; norm_num)
  have hlo : 0 < 1 / (8 * (e : ℝ)) := by positivity
  have hA : 1 / (8 * (e : ℝ)) ≤ 1 / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hB : 1 / (48 * (s : ℝ)) ≤ 1 / 48 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have h4lo : (e : ℝ) * (1 / (8 * e)) = 1 / 8 := by field_simp
  have h4hi : (e : ℝ) * (1 / (48 * s)) ≤ 1 / 12 := by
    rw [show (e : ℝ) * (1 / (48 * s)) = (e : ℝ) / (48 * s) by ring, div_le_iff₀ (by positivity)]
    linarith
  have hl : (e : ℝ) * (1 / (8 * e)) ≤ (e : ℝ) * z := mul_le_mul_of_nonneg_left hz1 heR.le
  have hr : (e : ℝ) * z ≤ (e : ℝ) * (1 / (8 * e) + 1 / (48 * s)) :=
    mul_le_mul_of_nonneg_left hz2 heR.le
  rw [mul_add] at hr
  refine ⟨z, by linarith, by linarith, ?_, ?_⟩
  · rw [show 4 * ((3 * s : ℕ) : ℝ) * z = 0 + 12 * (s : ℝ) * z by push_cast; ring]; exact hz
  · have : (e : ℝ) * (1 / 2 + z) = (j : ℝ) + (e : ℝ) * z := by
      have : (e : ℝ) = 2 * j := by rw [hj]; push_cast; ring
      rw [this]; ring
    rw [this]
    exact LRC.MirrorCentre.circDist_ge_of_window (m := j) (by push_cast; linarith)
      (by push_cast; linarith) (by norm_num)

/-- **DE4b**: `g ∣ c₂`, `e = c₂/g`, `4 ∤ e`; one of the five choices of `z` above. -/
theorem de4b_z {t e : ℕ} (ht : 0 < t) (he4 : ¬ 4 ∣ e) :
    ∃ z : ℝ, 0 ≤ z ∧ z ≤ 1 / 12 ∧ (8 : ℝ)⁻¹ ≤ circDist (4 * (t : ℝ) * z) ∧
      (8 : ℝ)⁻¹ ≤ circDist ((e : ℝ) * (1 / 2 + z)) := by
  rcases (show e % 2 = 1 ∨ e % 4 = 2 by omega) with h | h
  · rcases le_or_gt e (12 * t) with h' | h'
    · exact de4b_odd_small ht h h'
    · exact de4b_odd_large ht h'
  · by_cases h3 : 3 ∣ t
    · obtain ⟨s, rfl⟩ := h3
      have hs : 0 < s := by omega
      rcases le_or_gt (4 * s) e with h' | h'
      · exact de4b_two_big hs h'
      · exact de4b_two_small hs h h'
    · exact de4b_two_not3 h h3

/-- **Case DE4** (`{u₁, u₂} = {g, 3g}`, `c₁ = 4gt`, `4 ∤ c₂`). -/
theorem de4 {g t c₂ : ℕ} (hg : 0 < g) (ht : 0 < t) (hc₂ : ¬ 4 ∣ c₂) :
    ∃ τ : ℝ, (8 : ℝ)⁻¹ ≤ circDist (4 * (g : ℝ) * t * τ) ∧ (8 : ℝ)⁻¹ ≤ circDist ((c₂ : ℝ) * τ) ∧
      (4 : ℝ)⁻¹ ≤ circDist ((g : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist (3 * (g : ℝ) * τ) := by
  by_cases hdg : (g : ℤ) ∣ (c₂ : ℤ)
  · obtain ⟨e, he⟩ : g ∣ c₂ := Int.natCast_dvd_natCast.mp hdg
    have he4 : ¬ 4 ∣ e := fun h => hc₂ (he ▸ Dvd.dvd.mul_left h g)
    obtain ⟨z, hz0, hz1, hz4, hze⟩ := de4b_z ht he4
    have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
    refine de4_of_y hg 0 hz0 hz1 hz4 ?_
    rw [he]; push_cast
    rw [show (g : ℝ) * e * (0 + 1 / 2 + z) / g = e * (1 / 2 + z) by field_simp; ring]
    exact hze
  · obtain ⟨n, z, hz0, hz1, hz4, hzc⟩ := de4a hg ht hdg
    exact de4_of_y hg n hz0 hz1 hz4 hzc

/-! ### Case DE: the dispatch -/

/-- **Case DE** (`4 ∣ c₁`, `4 ∤ c₂`).  With `d = b₁ − b₂`: DE1 if `d ∤ c₁`; DE2 if `c₁ = t·d` and
`d ∤ 4b₂`; otherwise `d = 4g`, `b₂ = g·β`, `b₁ = g·(β + 4)`, and DE3 (`β ≥ 1` or `β ≤ −5`) or
DE4 (`β = −1, −3`); `β = 0, −2, −4` would make an odd reading even. -/
theorem case_DE {c₁ c₂ : ℕ} (hc₁ : 4 ∣ c₁) (hc₁p : 0 < c₁) (hc₂ : ¬ 4 ∣ c₂) {b₁ b₂ : ℤ}
    (hb₁ : 4 ∣ b₁ - 1) (hb₂ : 4 ∣ b₂ - 1) (hlt : b₂ < b₁) :
    ∃ τ : ℝ, (8 : ℝ)⁻¹ ≤ circDist ((c₁ : ℝ) * τ) ∧ (8 : ℝ)⁻¹ ≤ circDist ((c₂ : ℝ) * τ) ∧
      (4 : ℝ)⁻¹ ≤ circDist ((b₁ : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((b₂ : ℝ) * τ) := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = b₁ - b₂ := ⟨(b₁ - b₂).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hdpos : 0 < d := by omega
  by_cases h1 : (d : ℤ) ∣ (c₁ : ℤ)
  swap
  · exact case_DE1 hc₁ hc₂ hb₁ hb₂ hd hdpos h1
  obtain ⟨t, ht⟩ : d ∣ c₁ := Int.natCast_dvd_natCast.mp h1
  have htpos : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, mul_zero] at ht; omega
    · exact h
  by_cases h2 : (d : ℤ) ∣ 4 * b₂
  swap
  · exact case_DE2 hc₁ hc₂ hb₁ hb₂ hd hdpos htpos (by rw [ht, mul_comm]) h2
  obtain ⟨g, hg⟩ : ∃ g : ℕ, d = 4 * g := ⟨d / 4, by omega⟩
  have hgpos : 0 < g := by omega
  obtain ⟨β, hβ⟩ := h2
  have hb₂g : b₂ = g * β := by
    have h4 : (4 : ℤ) * b₂ = 4 * (g * β) := by rw [hβ, hg]; push_cast; ring
    linarith
  have hb₁' : b₁ = b₂ + 4 * g := by omega
  have hb₁g : b₁ = g * (β + 4) := by rw [hb₁', hb₂g]; ring
  have hc₁R : (c₁ : ℝ) = 4 * g * t := by rw [ht, hg]; push_cast; ring
  rcases (show 1 ≤ β ∨ β ≤ -5 ∨ β = -1 ∨ β = -3 ∨ β = 0 ∨ β = -2 ∨ β = -4 by omega) with
    hβ1 | hβ5 | hβm1 | hβm3 | hβ0 | hβm2 | hβm4
  · obtain ⟨q, hq⟩ : ∃ q : ℕ, (q : ℤ) = β := ⟨β.toNat, Int.toNat_of_nonneg (by omega)⟩
    exact case_DE3_pos hc₁ hc₂ hb₁ hb₂ hgpos htpos (q := q) (by omega) hc₁R
      (by rw [hb₁g, ← hq]; push_cast; ring) (by rw [hb₂g, ← hq]; push_cast; ring)
  · obtain ⟨q, hq⟩ : ∃ q : ℕ, (q : ℤ) = -β - 4 := ⟨(-β - 4).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hβq : β = -(q : ℤ) - 4 := by omega
    exact case_DE3_neg hc₁ hc₂ hb₁ hb₂ hgpos htpos (q := q) (by omega) hc₁R
      (by rw [hb₁g, hβq]; push_cast; ring) (by rw [hb₂g, hβq]; push_cast; ring)
  · obtain ⟨τ, k1, k2, k3, k4⟩ := de4 hgpos htpos hc₂
    refine ⟨τ, by rw [hc₁R]; exact k1, k2, ?_, ?_⟩
    · rw [show (b₁ : ℝ) * τ = 3 * (g : ℝ) * τ by rw [hb₁g, hβm1]; push_cast; ring]; exact k4
    · rw [show (b₂ : ℝ) * τ = -((g : ℝ) * τ) by rw [hb₂g, hβm1]; push_cast; ring, circDist.symm_neg]
      exact k3
  · obtain ⟨τ, k1, k2, k3, k4⟩ := de4 hgpos htpos hc₂
    refine ⟨τ, by rw [hc₁R]; exact k1, k2, ?_, ?_⟩
    · rw [show (b₁ : ℝ) * τ = (g : ℝ) * τ by rw [hb₁g, hβm3]; push_cast; ring]; exact k3
    · rw [show (b₂ : ℝ) * τ = -(3 * (g : ℝ) * τ) by rw [hb₂g, hβm3]; push_cast; ring,
        circDist.symm_neg]
      exact k4
  · rw [hb₂g, hβ0] at hb₂; omega
  · rw [hb₂g, hβm2] at hb₂; omega
  · rw [hb₁g, hβm4] at hb₁; omega

/-! ## M(2,2) -/

/-- **M(2,2) on integers `≡ 1 (mod 4)`.**  Cases A, C, DE (and DE with the roles of `c₁, c₂`
exchanged). -/
theorem exists_mixed_two_two_one_mod_four {c₁ c₂ : ℕ} (hc₁p : 0 < c₁) (hc₂p : 0 < c₂) {b₁ b₂ : ℤ}
    (hb₁ : 4 ∣ b₁ - 1) (hb₂ : 4 ∣ b₂ - 1) (hlt : b₂ < b₁) :
    ∃ τ : ℝ, (8 : ℝ)⁻¹ ≤ circDist ((c₁ : ℝ) * τ) ∧ (8 : ℝ)⁻¹ ≤ circDist ((c₂ : ℝ) * τ) ∧
      (4 : ℝ)⁻¹ ≤ circDist ((b₁ : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((b₂ : ℝ) * τ) := by
  by_cases h1 : 4 ∣ c₁ <;> by_cases h2 : 4 ∣ c₂
  · exact case_C h1 h2 hc₁p hc₂p hb₁ hb₂ hlt
  · exact case_DE h1 hc₁p h2 hb₁ hb₂ hlt
  · obtain ⟨τ, k1, k2, k3, k4⟩ := case_DE h2 hc₂p h1 hb₁ hb₂ hlt
    exact ⟨τ, k2, k1, k3, k4⟩
  · exact case_A h1 h2 hb₁ hb₂

/-- **M(2,2) for two readings at `1/8` and two distinct odd readings at `1/4`.** -/
theorem exists_mixed_two_two_pair {c₁ c₂ u₁ u₂ : ℕ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hu₁ : ¬ 2 ∣ u₁) (hu₂ : ¬ 2 ∣ u₂) (hne : u₁ ≠ u₂) :
    ∃ τ : ℝ, 0 < τ ∧ (8 : ℝ)⁻¹ ≤ circDist ((c₁ : ℝ) * τ) ∧ (8 : ℝ)⁻¹ ≤ circDist ((c₂ : ℝ) * τ) ∧
      (4 : ℝ)⁻¹ ≤ circDist ((u₁ : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((u₂ : ℝ) * τ) := by
  obtain ⟨b₁, hb₁, hb₁u, hb₁e⟩ := exists_one_mod_four hu₁
  obtain ⟨b₂, hb₂, hb₂u, hb₂e⟩ := exists_one_mod_four hu₂
  have hbne : b₁ ≠ b₂ := by
    intro h
    apply hne
    rcases hb₁u with h1 | h1 <;> rcases hb₂u with h2 | h2 <;> omega
  obtain ⟨τ, k1, k2, k3, k4⟩ : ∃ τ : ℝ, (8 : ℝ)⁻¹ ≤ circDist ((c₁ : ℝ) * τ) ∧
      (8 : ℝ)⁻¹ ≤ circDist ((c₂ : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((b₁ : ℝ) * τ) ∧
      (4 : ℝ)⁻¹ ≤ circDist ((b₂ : ℝ) * τ) := by
    rcases lt_or_gt_of_ne hbne with h | h
    · obtain ⟨τ, k1, k2, k3, k4⟩ := exists_mixed_two_two_one_mod_four hc₁ hc₂ hb₂ hb₁ h
      exact ⟨τ, k1, k2, k4, k3⟩
    · exact exists_mixed_two_two_one_mod_four hc₁ hc₂ hb₁ hb₂ h
  set N : ℕ := ⌊|τ|⌋₊ + 1 with hN
  have hNpos : 0 < τ + N := by
    have h1 := Nat.lt_floor_add_one |τ|
    have h2 := neg_abs_le τ
    rw [hN]; push_cast; linarith
  have hshift : ∀ m : ℕ, circDist ((m : ℝ) * (τ + N)) = circDist ((m : ℝ) * τ) := fun m => by
    rw [show (m : ℝ) * (τ + N) = (m : ℝ) * τ + (((m * N : ℕ) : ℤ) : ℝ) by push_cast; ring,
      circDist_add_int]
  exact ⟨τ + N, hNpos, by rw [hshift]; exact k1, by rw [hshift]; exact k2,
    by rw [hshift, hb₁e]; exact k3, by rw [hshift, hb₂e]; exact k4⟩

/-- **M(2,2).**  At most two positive readings `A` at `1/8` and at most two odd readings `B` at `1/4`
are clear together at some `τ > 0`. -/
theorem exists_mixed_two_two (A B : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) (hB : ∀ b ∈ B, ¬ 2 ∣ b)
    (hAc : A.card ≤ 2) (hBc : B.card ≤ 2) :
    ∃ τ : ℝ, 0 < τ ∧ (∀ a ∈ A, (8 : ℝ)⁻¹ ≤ circDist ((a : ℝ) * τ)) ∧
      ∀ b ∈ B, (4 : ℝ)⁻¹ ≤ circDist ((b : ℝ) * τ) := by
  classical
  by_cases h3 : A.card + B.card ≤ 3
  · refine exists_mixed_le_three A B hA (fun b hb => ?_) h3
    have := hB b hb
    omega
  · have hA2 : A.card = 2 := by omega
    have hB2 : B.card = 2 := by omega
    obtain ⟨c₁, c₂, -, rfl⟩ := Finset.card_eq_two.mp hA2
    obtain ⟨u₁, u₂, hu, rfl⟩ := Finset.card_eq_two.mp hB2
    obtain ⟨τ, hτ, k1, k2, k3, k4⟩ := exists_mixed_two_two_pair (hA c₁ (by simp)) (hA c₂ (by simp))
      (hB u₁ (by simp)) (hB u₂ (by simp)) hu
    refine ⟨τ, hτ, fun a ha => ?_, fun b hb => ?_⟩
    · rcases Finset.mem_insert.mp ha with rfl | ha
      · exact k1
      · rw [Finset.mem_singleton.mp ha]; exact k2
    · rcases Finset.mem_insert.mp hb with rfl | hb
      · exact k3
      · rw [Finset.mem_singleton.mp hb]; exact k4

end LRC.ParityDescent

namespace LRC.OrderEightN

open ConstructionN LRC.Descent LRC.ParityDescent

/-- **Quarter level, two and two.**  At most three odd readings, at most two multiples of `4`, at most
two readings `≡ 2 (mod 4)`: the mixed instant is M(2,2) (`exists_mixed_two_two`), and the set is lonely
at the displaced quarter instant `s/4 + j/4`. -/
theorem lonely_eight_of_quarter_two_two {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d)
    (hodd : (S.filter (fun d => ¬ 2 ∣ d)).card ≤ 3)
    (h4 : (S.filter (fun d => 4 ∣ d)).card ≤ 2)
    (ht : (S.filter (fun d => d % 4 = 2)).card ≤ 2) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  set A := (S.filter (fun d => 4 ∣ d)).image (fun d => d / 4) with hAdef
  set B := (S.filter (fun d => d % 4 = 2)).image (fun d => d / 2) with hBdef
  have hAcard : A.card ≤ 2 := le_trans Finset.card_image_le h4
  have hBcard : B.card ≤ 2 := le_trans Finset.card_image_le ht
  have hBodd : ∀ x ∈ B, ¬ 2 ∣ x := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    have := (Finset.mem_filter.mp hd).2
    omega
  obtain ⟨s, hs, hsA, hsB⟩ := exists_mixed_two_two A B (quot_pos hpos 4 (by norm_num)) hBodd
    hAcard hBcard
  refine lonely_eight_of_quarter_silent hodd ⟨s, hs, fun a ha h4a => ?_, fun d hd hd2 => ?_⟩
  · exact hsA (a / 4) (Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, h4a⟩, rfl⟩)
  · exact hsB (d / 2) (Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨hd, hd2⟩, rfl⟩)

/-- **Eighth level, two and two.**  The parity split for the non-multiples of `8` other than those
`≡ 4 (mod 8)`, at most two multiples of `8`, at most two readings `≡ 4 (mod 8)`: the mixed instant is
M(2,2), and the set is lonely at the displaced eighth instant `(τ + k)/8`. -/
theorem lonely_eight_of_eighth_two_two {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d)
    (hsplit : ParitySplit8 (S.filter (fun d => ¬ 8 ∣ d ∧ d % 8 ≠ 4)))
    (h8 : (S.filter (fun d => 8 ∣ d)).card ≤ 2)
    (h4 : (S.filter (fun d => d % 8 = 4)).card ≤ 2) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  set A := (S.filter (fun d => 8 ∣ d)).image (fun d => d / 8) with hAdef
  set B := (S.filter (fun d => d % 8 = 4)).image (fun d => d / 4) with hBdef
  have hAcard : A.card ≤ 2 := le_trans Finset.card_image_le h8
  have hBcard : B.card ≤ 2 := le_trans Finset.card_image_le h4
  have hBodd : ∀ x ∈ B, ¬ 2 ∣ x := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    have := (Finset.mem_filter.mp hd).2
    omega
  obtain ⟨τ, hτ, hτA, hτB⟩ := exists_mixed_two_two A B (quot_pos hpos 8 (by norm_num)) hBodd
    hAcard hBcard
  refine lonely_eight_of_eighth_silent hsplit ⟨τ, hτ, fun m hm h8m => ?_, fun f hf h4f => ?_⟩
  · exact hτA (m / 8) (Finset.mem_image.mpr ⟨m, Finset.mem_filter.mpr ⟨hm, h8m⟩, rfl⟩)
  · exact hτB (f / 4) (Finset.mem_image.mpr ⟨f, Finset.mem_filter.mpr ⟨hf, h4f⟩, rfl⟩)

end LRC.OrderEightN
