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

/-! ### Moving one runner at a time

The other runners do not move, so at a lonely instant `t1` only the moving runner's position changes.  Off an edge it
stays clear.  On an edge it moves inward for one sign of the change; for the other sign, the mirror instant `P − t1`
puts it on the opposite edge, where the same change moves it inward.  No wall condition, and no distinction between
one runner and two runners on an edge. -/

theorem sep_move_other {v w : Fin 8 → ℝ} {k i j : Fin 8} (hki : k ≠ i) (hji : j ≠ i)
    (hw : ∀ m : Fin 8, m ≠ i → w m = 0) (r t : ℝ) : sep (v + r • w) k j t = sep v k j t := by
  rw [sep_line, hw j hji, hw k hki, sep_eq]; ring

theorem sep_move_self {v w : Fin 8 → ℝ} {k i : Fin 8} (hki : k ≠ i)
    (hw : ∀ m : Fin 8, m ≠ i → w m = 0) (r t : ℝ) : sep (v + r • w) k i t = sep v k i t + r * w i * t := by
  rw [sep_line, hw k hki, sep_eq]; ring

/-- **One runner moved: strictly clear case.** -/
theorem move_one_strict {v w : Fin 8 → ℝ} {k i : Fin 8} {t1 : ℝ} (hki : k ≠ i)
    (hw : ∀ m : Fin 8, m ≠ i → w m = 0) (ht1 : 0 < t1) (hl : LonelyAt v k t1)
    (hs : (8 : ℝ)⁻¹ < circDist (sep v k i t1)) :
    ∀ᶠ r in 𝓝 (0 : ℝ), LRC.Spec.LonelyForSubject (v + r • w) k := by
  have hc : Tendsto (fun r : ℝ => circDist (sep v k i t1 + r * w i * t1)) (𝓝 0)
      (𝓝 (circDist (sep v k i t1 + 0 * w i * t1))) :=
    (circDist_lipschitz.continuous.comp (continuous_const.add
      ((continuous_id.mul continuous_const).mul continuous_const))).tendsto 0
  simp only [zero_mul, add_zero] at hc
  filter_upwards [hc.eventually (lt_mem_nhds hs)] with r hr
  refine ⟨t1, ht1, fun j hjk => ?_⟩
  by_cases hji : j = i
  · subst hji; rw [sep_move_self hki hw]; exact hr.le
  · rw [sep_move_other hki hji hw]; exact hl j hjk

/-- **One runner moved: the general case, with a common period.**  Readings with a common period `P > t1`: the
subject stays lonely under every small change of the one runner, at `t1` or at its mirror `P − t1`. -/
theorem move_one_period {v w : Fin 8 → ℝ} {k i : Fin 8} {t1 P : ℝ} (hki : k ≠ i)
    (hw : ∀ m : Fin 8, m ≠ i → w m = 0) (ht1 : 0 < t1) (hP : t1 < P) (hl : LonelyAt v k t1)
    (hper : ∀ j : Fin 8, ∃ z : ℤ, (v j - v k) * P = z) :
    ∀ᶠ r in 𝓝 (0 : ℝ), LRC.Spec.LonelyForSubject (v + r • w) k := by
  rcases lt_or_eq_of_le (hl i hki.symm) with hs | he
  · exact move_one_strict hki hw ht1 hl hs
  -- the mirror instant keeps every other runner exactly as clear
  have hmir : ∀ j : Fin 8, circDist (sep v k j (P - t1)) = circDist (sep v k j t1) := by
    intro j
    obtain ⟨z, hz⟩ := hper j
    have e : sep v k j (P - t1) = -(sep v k j t1) + (z : ℝ) := by rw [sep_eq, sep_eq, ← hz]; ring
    rw [e, circDist_add_int_po, circDist_neg_po]
  obtain ⟨zi, hzi⟩ := hper i
  have hPt : 0 < P - t1 := by linarith
  -- small changes: |r · w i| · P < 3/4
  have hsmall : ∀ᶠ r in 𝓝 (0 : ℝ), |r * w i| * P < 3 / 4 := by
    have hc : Tendsto (fun r : ℝ => |r * w i| * P) (𝓝 0) (𝓝 (|0 * w i| * P)) :=
      ((continuous_abs.comp (continuous_id.mul continuous_const)).mul continuous_const).tendsto 0
    simp only [zero_mul, abs_zero] at hc
    exact hc.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨N, hN | hN⟩ := edge_of_eq he.symm
  · -- on the leaving edge at `t1`; on the entering edge at the mirror
    filter_upwards [hsmall] with r hr
    have hb1 : |r * w i| * t1 < 3 / 4 := lt_of_le_of_lt (by gcongr) hr
    have hb2 : |r * w i| * (P - t1) < 3 / 4 := lt_of_le_of_lt (by gcongr; linarith) hr
    rcases le_or_gt 0 (r * w i) with hsg | hsg
    · refine ⟨t1, ht1, fun j hjk => ?_⟩
      by_cases hji : j = i
      · subst hji; rw [sep_move_self hki hw, hN]
        rw [abs_of_nonneg hsg] at hb1
        refine LRC.TwoPinner.clear_of_band (N := N) ?_ ?_ <;> nlinarith
      · rw [sep_move_other hki hji hw]; exact hl j hjk
    · refine ⟨P - t1, hPt, fun j hjk => ?_⟩
      by_cases hji : j = i
      · subst hji; rw [sep_move_self hki hw]
        have hx : sep v k j (P - t1) = ((zi - N - 1 : ℤ) : ℝ) + 7 / 8 := by
          rw [sep_eq]; push_cast; rw [mul_sub, hzi, ← sep_eq, hN]; ring
        rw [hx]; rw [abs_of_neg hsg] at hb2
        refine LRC.TwoPinner.clear_of_band (N := zi - N - 1) ?_ ?_ <;> nlinarith
      · rw [sep_move_other hki hji hw, hmir j]; exact hl j hjk
  · -- on the entering edge at `t1`; on the leaving edge at the mirror
    filter_upwards [hsmall] with r hr
    have hb1 : |r * w i| * t1 < 3 / 4 := lt_of_le_of_lt (by gcongr) hr
    have hb2 : |r * w i| * (P - t1) < 3 / 4 := lt_of_le_of_lt (by gcongr; linarith) hr
    rcases le_or_gt (r * w i) 0 with hsg | hsg
    · refine ⟨t1, ht1, fun j hjk => ?_⟩
      by_cases hji : j = i
      · subst hji; rw [sep_move_self hki hw, hN]
        rw [abs_of_nonpos hsg] at hb1
        refine LRC.TwoPinner.clear_of_band (N := N) ?_ ?_ <;> nlinarith
      · rw [sep_move_other hki hji hw]; exact hl j hjk
    · refine ⟨P - t1, hPt, fun j hjk => ?_⟩
      by_cases hji : j = i
      · subst hji; rw [sep_move_self hki hw]
        have hx : sep v k j (P - t1) = ((zi - N - 1 : ℤ) : ℝ) + 1 / 8 := by
          rw [sep_eq]; push_cast; rw [mul_sub, hzi, ← sep_eq, hN]; ring
        rw [hx]; rw [abs_of_pos hsg] at hb2
        refine LRC.TwoPinner.clear_of_band (N := zi - N - 1) ?_ ?_ <;> nlinarith
      · rw [sep_move_other hki hji hw, hmir j]; exact hl j hjk

/-- A positive rational reading on an edge makes the instant rational. -/
theorem instant_rat {q : ℚ} {t : ℝ} {N : ℤ} {e : ℚ} (hq : (q : ℝ) ≠ 0) (h : (q : ℝ) * t = (N : ℝ) + (e : ℝ)) :
    ∃ x : ℚ, t = x :=
  ⟨((N : ℚ) + e) / q, by rw [Rat.cast_div]; push_cast; field_simp; linarith⟩

/-- A reading on an edge at a rational instant is rational. -/
theorem reading_rat {x t : ℝ} {tq : ℚ} {N : ℤ} {e : ℚ} (ht : t = tq) (ht0 : t ≠ 0) (h : x * t = (N : ℝ) + (e : ℝ)) :
    ∃ q : ℚ, x = q := by
  have htq : (tq : ℝ) ≠ 0 := by rw [← ht]; exact ht0
  refine ⟨((N : ℚ) + e) / tq, ?_⟩
  rw [Rat.cast_div]; push_cast; rw [← ht]; field_simp; linarith

/-- **One segment of the path: one runner moved, lonely at the start ⇒ lonely at the end, given the window.**  The
other runners' readings are rational; every reading stays positive along the segment. -/
theorem segment_lonely {v w : Fin 8 → ℝ} {k i : Fin 8} {c T : ℝ} (hc : 0 < c) (hki : k ≠ i)
    (hw : ∀ m : Fin 8, m ≠ i → w m = 0)
    (hrat : ∀ j : Fin 8, j ≠ i → ∃ q : ℚ, v j - v k = q)
    (hpos : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ j : Fin 8, j ≠ k → 0 < (v + s • w) j - (v + s • w) k)
    (hbound : ∀ s ∈ Set.Icc (0 : ℝ) 1, LRC.Spec.LonelyForSubject (v + s • w) k →
      ∃ t ∈ Set.Icc c T, LonelyAt (v + s • w) k t)
    (h0 : LRC.Spec.LonelyForSubject v k) : LRC.Spec.LonelyForSubject (v + w) k := by
  have hp : Continuous (fun s : ℝ => v + s • w) := continuous_const.add (continuous_id.smul continuous_const)
  have h0' : LRC.Spec.LonelyForSubject (v + (0 : ℝ) • w) k := by simpa using h0
  have key := LRC.Deformation.lonely_along_path (p := fun s : ℝ => v + s • w) hp hc h0' ?_ hbound
  · simpa using key
  intro s hs hl
  obtain ⟨t1, ht1, hl1⟩ := hl
  set u := v + s • w with hu
  -- it suffices to work at `u` in the direction `w`
  suffices G : ∀ᶠ r in 𝓝 (0 : ℝ), LRC.Spec.LonelyForSubject (u + r • w) k by
    have htr : Tendsto (fun r : ℝ => r - s) (𝓝 s) (𝓝 0) := by
      simpa using ((continuous_id.sub continuous_const).tendsto s : Tendsto (fun r : ℝ => r - s) (𝓝 s) (𝓝 (s - s)))
    filter_upwards [htr.eventually G] with r hr
    have e : u + (r - s) • w = v + r • w := by rw [hu]; ext m; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e] at hr; exact hr
  have hposu : ∀ j : Fin 8, j ≠ k → 0 < u j - u k := hpos s hs
  have hfix : ∀ j : Fin 8, j ≠ i → u j - u k = v j - v k := by
    intro j hj; simp only [hu, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hw j hj, hw k hki]; ring
  rcases margin_or_pinch hposu ht1 hl1 with ⟨t', ε, ht', hε, hm⟩ | ⟨a, b, hak, hbk, Na, Nb, hA, hB⟩
  · have hq : Continuous (fun r : ℝ => u + r • w) := continuous_const.add (continuous_id.smul continuous_const)
    have hm' : ∀ m : Fin 8, m ≠ k → (8 : ℝ)⁻¹ + ε ≤ circDist (sep ((fun r : ℝ => u + r • w) 0) k m t') := by
      intro m hm0; simpa using hm m hm0
    exact LRC.Deformation.eventually_lonely_of_margin hq hε ht' hm'
  rcases lt_or_eq_of_le (hl1 i hki.symm) with hstr | heq
  · exact move_one_strict hki hw ht1 hl1 hstr
  -- runner `i` is on an edge; a fixed runner on an edge makes `t1` rational
  have ht1q : ∃ x : ℚ, t1 = x := by
    by_cases hai : a = i
    · have hbi : b ≠ i := by
        intro hbi; subst hai; subst hbi
        exact pinners_ne hA hB
      obtain ⟨q, hq⟩ := hrat b hbi
      have hqne : (q : ℝ) ≠ 0 := by rw [← hq, ← hfix b hbi]; exact (hposu b hbk).ne'
      exact instant_rat (e := 7 / 8) hqne (by rw [← hq, ← hfix b hbi, hB]; push_cast; ring)
    · obtain ⟨q, hq⟩ := hrat a hai
      have hqne : (q : ℝ) ≠ 0 := by rw [← hq, ← hfix a hai]; exact (hposu a hak).ne'
      exact instant_rat (e := 1 / 8) hqne (by rw [← hq, ← hfix a hai, hA]; push_cast; ring)
  obtain ⟨tq, htq⟩ := ht1q
  have hiq : ∃ q : ℚ, u i - u k = q := by
    obtain ⟨N, hN | hN⟩ := edge_of_eq heq.symm
    · exact reading_rat (e := 1 / 8) htq ht1.ne' (by rw [← sep_eq, hN]; push_cast; ring)
    · exact reading_rat (e := 7 / 8) htq ht1.ne' (by rw [← sep_eq, hN]; push_cast; ring)
  have hallq : ∀ j : Fin 8, ∃ q : ℚ, u j - u k = q := by
    intro j
    by_cases hji : j = i
    · subst hji; exact hiq
    · rw [hfix j hji]; exact hrat j hji
  obtain ⟨P, hP, hper⟩ := common_period hallq t1
  exact move_one_period hki hw ht1 hP hl1 hper

end LRC.PathRoute
