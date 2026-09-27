import LonelyRunner.LRC.Spec.PinchOpenN

/-!
# The path route: what a lonely instant looks like locally

2026-09-27.  Plan: `docs/n8/PATH_ROUTE_LEAN_PLAN_v1.md` (P1).  The subject `k` is the slowest runner here: every other
runner's reading `v i − v k` is positive, so every reading increases with time.

* `margin_or_pinch`: at a lonely instant `t > 0`, either some instant has every runner strictly clear (a margin), or `t`
  is a **pinch**: some runner sits exactly on `+1/8` (leaving the subject's slot) and some runner exactly on `−1/8`
  (entering).  If no runner is on `+1/8`, a slightly earlier instant has everyone strictly clear; if none is on `−1/8`,
  a slightly later one does.
* `simple_or_multi`: a pinch is **simple** (every other runner strictly clear, hence with a margin) or **multi** (a
  third runner also on an edge: two runners at one place).

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.PathRoute

open Arrangement Filter Topology LRC.PinchOpen

/-- A reading strictly inside `(N + 1/8, N + 7/8)` is strictly clear. -/
theorem strict_clear_of_band {x : ℝ} {N : ℤ} (h1 : (N : ℝ) + 1 / 8 < x) (h2 : x < (N : ℝ) + 7 / 8) :
    (8 : ℝ)⁻¹ < circDist x := by
  have hfl : ⌊x⌋ = N := by rw [Int.floor_eq_iff]; constructor <;> linarith
  unfold circDist
  rw [Int.fract, hfl]
  exact lt_min (by linarith) (by linarith)

/-- A reading at circle distance exactly `1/8` is on one of the two edges. -/
theorem edge_of_eq {x : ℝ} (h : circDist x = (8 : ℝ)⁻¹) :
    ∃ N : ℤ, x = (N : ℝ) + 1 / 8 ∨ x = (N : ℝ) + 7 / 8 := by
  unfold circDist at h
  refine ⟨⌊x⌋, ?_⟩
  have hx : x = (⌊x⌋ : ℝ) + Int.fract x := (Int.floor_add_fract x).symm
  rcases min_choice (Int.fract x) (1 - Int.fract x) with hm | hm <;> rw [hm] at h
  · left; linarith
  · right; linarith

/-- Strict clearness of every runner gives a positive margin (finitely many runners). -/
theorem margin_of_strict {v : Fin 8 → ℝ} {k : Fin 8} {t : ℝ}
    (h : ∀ i : Fin 8, i ≠ k → (8 : ℝ)⁻¹ < circDist (sep v k i t)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i : Fin 8, i ≠ k → (8 : ℝ)⁻¹ + ε ≤ circDist (sep v k i t) := by
  classical
  have hne : (Finset.univ.erase k).Nonempty :=
    Finset.card_pos.mp (by rw [Finset.card_erase_of_mem (Finset.mem_univ k)]; simp)
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image _ (fun i => circDist (sep v k i t)) hne
  refine ⟨circDist (sep v k i0 t) - (8 : ℝ)⁻¹, by linarith [h i0 (Finset.ne_of_mem_erase hi0)], ?_⟩
  intro i hi
  have := hmin i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩)
  linarith

/-- The same, for the runners other than two named ones. -/
theorem margin_of_strict_others {v : Fin 8 → ℝ} {k a b : Fin 8} {t : ℝ}
    (h : ∀ i : Fin 8, i ≠ k → i ≠ a → i ≠ b → (8 : ℝ)⁻¹ < circDist (sep v k i t)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i : Fin 8, i ≠ k → i ≠ a → i ≠ b → (8 : ℝ)⁻¹ + ε ≤ circDist (sep v k i t) := by
  classical
  set S := (Finset.univ.filter fun i : Fin 8 => i ≠ k ∧ i ≠ a ∧ i ≠ b) with hS
  rcases S.eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun i h1 h2 h3 => ?_⟩
    have : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2, h3⟩
    rw [he] at this; exact absurd this (Finset.notMem_empty _)
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image _ (fun i => circDist (sep v k i t)) hne
  have hi0' := (Finset.mem_filter.mp hi0).2
  refine ⟨circDist (sep v k i0 t) - (8 : ℝ)⁻¹, by linarith [h i0 hi0'.1 hi0'.2.1 hi0'.2.2], ?_⟩
  intro i h1 h2 h3
  have := hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2, h3⟩)
  linarith

theorem sep_eq (v : Fin 8 → ℝ) (k i : Fin 8) (t : ℝ) : sep v k i t = (v i - v k) * t := by
  simp only [sep]; ring

/-- One runner's reading, as a function of time, is continuous. -/
theorem tendsto_sep (v : Fin 8 → ℝ) (k i : Fin 8) (t : ℝ) :
    Tendsto (fun s => circDist (sep v k i s)) (𝓝 t) (𝓝 (circDist (sep v k i t))) := by
  have hc : Continuous fun s => sep v k i s := by
    simp only [sep_eq]; exact continuous_const.mul continuous_id
  exact (circDist_lipschitz.continuous.tendsto _).comp (hc.tendsto t)

/-- **No runner on the leaving edge ⇒ a slightly earlier instant has every runner strictly clear.** -/
theorem strict_before {v : Fin 8 → ℝ} {k : Fin 8} {t : ℝ} (hpos : ∀ i : Fin 8, i ≠ k → 0 < v i - v k)
    (ht : 0 < t) (hl : LonelyAt v k t)
    (hnone : ∀ i : Fin 8, i ≠ k → ∀ N : ℤ, sep v k i t ≠ (N : ℝ) + 1 / 8) :
    ∃ t' : ℝ, 0 < t' ∧ ∀ i : Fin 8, i ≠ k → (8 : ℝ)⁻¹ < circDist (sep v k i t') := by
  have hall : ∀ᶠ s in 𝓝[<] t, 0 < s ∧ ∀ i : Fin 8, i ≠ k → (8 : ℝ)⁻¹ < circDist (sep v k i s) := by
    refine Filter.Eventually.and ((lt_mem_nhds ht).filter_mono nhdsWithin_le_nhds) ?_
    rw [Filter.eventually_all]
    intro i
    by_cases hik : i = k
    · filter_upwards with s; intro h; exact absurd hik h
    have hli := hl i hik
    rcases lt_or_eq_of_le hli with hs | he
    · filter_upwards [((tendsto_sep v k i t).eventually (lt_mem_nhds hs)).filter_mono nhdsWithin_le_nhds]
        with s hs' _ using hs'
    · obtain ⟨N, hN | hN⟩ := edge_of_eq he.symm
      · exact absurd hN (hnone i hik N)
      · -- on the entering edge: just before `t` the runner is strictly inside the band
        have hD := hpos i hik
        have hcont : Tendsto (fun s => sep v k i s) (𝓝 t) (𝓝 (sep v k i t)) := by
          have hc : Continuous fun s => sep v k i s := by
            simp only [sep_eq]; exact continuous_const.mul continuous_id
          exact hc.tendsto t
        have hlo : ∀ᶠ s in 𝓝 t, (N : ℝ) + 1 / 8 < sep v k i s :=
          hcont.eventually (lt_mem_nhds (by rw [hN]; linarith))
        filter_upwards [hlo.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs1 hs2 _
        refine strict_clear_of_band hs1 ?_
        rw [← hN, sep_eq, sep_eq]
        exact mul_lt_mul_of_pos_left hs2 hD
  obtain ⟨s, hs0, hs⟩ := hall.exists
  exact ⟨s, hs0, hs⟩

/-- **No runner on the entering edge ⇒ a slightly later instant has every runner strictly clear.** -/
theorem strict_after {v : Fin 8 → ℝ} {k : Fin 8} {t : ℝ} (hpos : ∀ i : Fin 8, i ≠ k → 0 < v i - v k)
    (ht : 0 < t) (hl : LonelyAt v k t)
    (hnone : ∀ i : Fin 8, i ≠ k → ∀ N : ℤ, sep v k i t ≠ (N : ℝ) + 7 / 8) :
    ∃ t' : ℝ, 0 < t' ∧ ∀ i : Fin 8, i ≠ k → (8 : ℝ)⁻¹ < circDist (sep v k i t') := by
  have hall : ∀ᶠ s in 𝓝[>] t, 0 < s ∧ ∀ i : Fin 8, i ≠ k → (8 : ℝ)⁻¹ < circDist (sep v k i s) := by
    refine Filter.Eventually.and ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with s hs using lt_trans ht hs
    rw [Filter.eventually_all]
    intro i
    by_cases hik : i = k
    · filter_upwards with s; intro h; exact absurd hik h
    have hli := hl i hik
    rcases lt_or_eq_of_le hli with hs | he
    · filter_upwards [((tendsto_sep v k i t).eventually (lt_mem_nhds hs)).filter_mono nhdsWithin_le_nhds]
        with s hs' _ using hs'
    · obtain ⟨N, hN | hN⟩ := edge_of_eq he.symm
      · have hD := hpos i hik
        have hcont : Tendsto (fun s => sep v k i s) (𝓝 t) (𝓝 (sep v k i t)) := by
          have hc : Continuous fun s => sep v k i s := by
            simp only [sep_eq]; exact continuous_const.mul continuous_id
          exact hc.tendsto t
        have hhi : ∀ᶠ s in 𝓝 t, sep v k i s < (N : ℝ) + 7 / 8 :=
          hcont.eventually (gt_mem_nhds (by rw [hN]; linarith))
        filter_upwards [hhi.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs1 hs2 _
        refine strict_clear_of_band ?_ hs1
        rw [← hN, sep_eq, sep_eq]
        exact mul_lt_mul_of_pos_left hs2 hD
      · exact absurd hN (hnone i hik N)
  obtain ⟨s, hs0, hs⟩ := hall.exists
  exact ⟨s, hs0, hs⟩

/-- **A lonely instant: a margin somewhere, or a pinch.** -/
theorem margin_or_pinch {v : Fin 8 → ℝ} {k : Fin 8} {t : ℝ} (hpos : ∀ i : Fin 8, i ≠ k → 0 < v i - v k)
    (ht : 0 < t) (hl : LonelyAt v k t) :
    (∃ t' ε : ℝ, 0 < t' ∧ 0 < ε ∧ ∀ i : Fin 8, i ≠ k → (8 : ℝ)⁻¹ + ε ≤ circDist (sep v k i t')) ∨
      ∃ a b : Fin 8, a ≠ k ∧ b ≠ k ∧ ∃ Na Nb : ℤ,
        (v a - v k) * t = (Na : ℝ) + 1 / 8 ∧ (v b - v k) * t = (Nb : ℝ) + 7 / 8 := by
  by_cases h1 : ∃ a : Fin 8, a ≠ k ∧ ∃ N : ℤ, sep v k a t = (N : ℝ) + 1 / 8
  · by_cases h2 : ∃ b : Fin 8, b ≠ k ∧ ∃ N : ℤ, sep v k b t = (N : ℝ) + 7 / 8
    · obtain ⟨a, hak, Na, ha⟩ := h1
      obtain ⟨b, hbk, Nb, hb⟩ := h2
      right; exact ⟨a, b, hak, hbk, Na, Nb, by rw [← sep_eq]; exact ha, by rw [← sep_eq]; exact hb⟩
    · push Not at h2
      obtain ⟨t', ht', hs⟩ := strict_after hpos ht hl h2
      obtain ⟨ε, hε, hm⟩ := margin_of_strict hs
      left; exact ⟨t', ε, ht', hε, hm⟩
  · push Not at h1
    obtain ⟨t', ht', hs⟩ := strict_before hpos ht hl h1
    obtain ⟨ε, hε, hm⟩ := margin_of_strict hs
    left; exact ⟨t', ε, ht', hε, hm⟩

/-- The two pinners are different runners. -/
theorem pinners_ne {x : ℝ} {Na Nb : ℤ} (ha : x = (Na : ℝ) + 1 / 8) (hb : x = (Nb : ℝ) + 7 / 8) : False := by
  have h : ((Na - Nb : ℤ) : ℝ) = 3 / 4 := by push_cast; linarith
  have h1 : (Na - Nb : ℤ) < 1 := by exact_mod_cast (by rw [h]; norm_num : ((Na - Nb : ℤ) : ℝ) < 1)
  have h2 : (0 : ℤ) < Na - Nb := by exact_mod_cast (by rw [h]; norm_num : (0 : ℝ) < ((Na - Nb : ℤ) : ℝ))
  omega

/-- **A pinch is simple or multi.** -/
theorem simple_or_multi {v : Fin 8 → ℝ} {k a b : Fin 8} {t : ℝ} (hl : LonelyAt v k t) :
    (∃ ε : ℝ, 0 < ε ∧ ∀ i : Fin 8, i ≠ k → i ≠ a → i ≠ b → (8 : ℝ)⁻¹ + ε ≤ circDist (sep v k i t)) ∨
      ∃ i : Fin 8, i ≠ k ∧ i ≠ a ∧ i ≠ b ∧ ∃ N : ℤ,
        (v i - v k) * t = (N : ℝ) + 1 / 8 ∨ (v i - v k) * t = (N : ℝ) + 7 / 8 := by
  by_cases h : ∀ i : Fin 8, i ≠ k → i ≠ a → i ≠ b → (8 : ℝ)⁻¹ < circDist (sep v k i t)
  · left; exact margin_of_strict_others h
  · push Not at h
    obtain ⟨i, h1, h2, h3, hle⟩ := h
    have he : circDist (sep v k i t) = (8 : ℝ)⁻¹ := le_antisymm hle (hl i h1)
    obtain ⟨N, hN⟩ := edge_of_eq he
    right; refine ⟨i, h1, h2, h3, N, ?_⟩
    rw [← sep_eq]; exact hN

/-- **Rational readings have a common period beyond any instant.** -/
theorem common_period {x : Fin 8 → ℝ} (hq : ∀ i : Fin 8, ∃ q : ℚ, x i = q) (t0 : ℝ) :
    ∃ P : ℝ, t0 < P ∧ ∀ i : Fin 8, ∃ z : ℤ, x i * P = z := by
  choose q hq using hq
  set Q : ℕ := ∏ i, (q i).den with hQ
  have hQpos : 0 < Q := Finset.prod_pos fun i _ => (q i).den_pos
  obtain ⟨m, hm⟩ := exists_nat_gt t0
  refine ⟨(Q : ℝ) * m, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQpos
    have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  · intro i
    have hd : (q i).den ∣ Q := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    obtain ⟨c, hc⟩ := hd
    refine ⟨(q i).num * c * m, ?_⟩
    rw [hq i, hc]
    have hden : ((q i).den : ℝ) ≠ 0 := by exact_mod_cast (q i).den_nz
    rw [Rat.cast_def]; push_cast
    field_simp

/-- **A pinch on a line with rational ends: inside its wall, or at a rational parameter.**  Readings along the line
are `(α i − α k) + s (β i − β k)` with rational coefficients.  Eliminating the instant from the two pinch equations
leaves one linear equation in `s`; either it holds identically (the direction keeps the pinners' ratio) or it fixes
`s` as a rational number. -/
theorem line_pinch_cases {α β : Fin 8 → ℝ} {k a b : Fin 8} {s t0 : ℝ} {Na Nb : ℤ}
    (hα : ∀ i : Fin 8, ∃ q : ℚ, α i - α k = q) (hβ : ∀ i : Fin 8, ∃ q : ℚ, β i - β k = q)
    (hA : ((α a - α k) + s * (β a - β k)) * t0 = (Na : ℝ) + 1 / 8)
    (hB : ((α b - α k) + s * (β b - β k)) * t0 = (Nb : ℝ) + 7 / 8) :
    (β b - β k) * ((α a - α k) + s * (β a - β k)) = (β a - β k) * ((α b - α k) + s * (β b - β k)) ∨
      ∃ q : ℚ, s = q := by
  obtain ⟨qa, hqa⟩ := hα a; obtain ⟨qb, hqb⟩ := hα b
  obtain ⟨ra, hra⟩ := hβ a; obtain ⟨rb, hrb⟩ := hβ b
  rw [hqa, hra] at hA ⊢; rw [hqb, hrb] at hB ⊢
  -- eliminate t0: (8 Nb + 7)(qa + s ra) = (8 Na + 1)(qb + s rb)
  have hel : ((8 * Nb + 7 : ℤ) : ℝ) * ((qa : ℝ) + s * ra) = ((8 * Na + 1 : ℤ) : ℝ) * ((qb : ℝ) + s * rb) := by
    push_cast
    have h1 : ((8 * (Nb : ℝ) + 7) * ((qa : ℝ) + s * ra)) * t0 = ((8 * (Na : ℝ) + 1) * ((qb : ℝ) + s * rb)) * t0 := by
      have e1 : ((8 * (Nb : ℝ) + 7) * ((qa : ℝ) + s * ra)) * t0 = (8 * (Nb : ℝ) + 7) * ((Na : ℝ) + 1 / 8) := by
        rw [mul_assoc, hA]
      have e2 : ((8 * (Na : ℝ) + 1) * ((qb : ℝ) + s * rb)) * t0 = (8 * (Na : ℝ) + 1) * ((Nb : ℝ) + 7 / 8) := by
        rw [mul_assoc, hB]
      rw [e1, e2]; ring
    have ht0 : t0 ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hA
      have : ((Na : ℝ) + 1 / 8) = 0 := hA.symm
      have h8 : ((8 * Na + 1 : ℤ) : ℝ) = 0 := by push_cast; linarith
      have : (8 * Na + 1 : ℤ) = 0 := by exact_mod_cast h8
      omega
    exact mul_right_cancel₀ ht0 h1
  set c : ℝ := ((8 * Nb + 7 : ℤ) : ℝ) * ra - ((8 * Na + 1 : ℤ) : ℝ) * rb with hc
  by_cases hc0 : c = 0
  · left
    have hN : ((8 * Na + 1 : ℤ) : ℝ) ≠ 0 := by
      have : (8 * Na + 1 : ℤ) ≠ 0 := by omega
      exact_mod_cast this
    apply mul_left_cancel₀ hN
    have : ((8 * Nb + 7 : ℤ) : ℝ) * ra = ((8 * Na + 1 : ℤ) : ℝ) * rb := by linarith [hc0]
    linear_combination (-((qa : ℝ) + s * ra)) * this + (ra : ℝ) * hel
  · right
    refine ⟨(((8 * Na + 1 : ℤ) : ℚ) * qb - ((8 * Nb + 7 : ℤ) : ℚ) * qa) /
      (((8 * Nb + 7 : ℤ) : ℚ) * ra - ((8 * Na + 1 : ℤ) : ℚ) * rb), ?_⟩
    have hc' : ((((8 * Nb + 7 : ℤ) : ℚ) * ra - ((8 * Na + 1 : ℤ) : ℚ) * rb : ℚ) : ℝ) = c := by
      rw [hc]; push_cast; ring
    rw [Rat.cast_div, hc']
    rw [eq_div_iff hc0]
    push_cast
    rw [hc]; push_cast at hel ⊢
    linear_combination hel

end LRC.PathRoute
