import LonelyRunner.LRC.Spec.DeformationN
import LonelyRunner.LRC.Spec.TwoPinnerN

/-!
# A simple pinch keeps the subject lonely under every small change of speeds

2026-09-27.  The local step `DeformationN.lonely_along_path` asks for (`hopen`), at an isolated lonely instant.

A **simple pinch** of arrangement `v`, subject `k`, at `t0 > 0`: runner `a` sits exactly on `+1/8` (leaving the
subject's slot, lap `Na`), runner `b` exactly on `−1/8` (entering, lap `Nb`), and every other runner is clear with a
margin `ε > 0`.  Change the speeds along a direction `w`, to `v + r • w`.

* `opens_at_leaving`: if `(w b − w k)(v a − v k) ≤ (w a − w k)(v b − v k)`, then for every small `r ≥ 0` the subject is
  lonely at the leaving runner's own opening `(Na + 1/8)/((v a − v k) + r (w a − w k))`: runner `a` stays on `1/8`,
  runner `b` does not cross into the slot, and the others keep their room.
* `pinch_eventually_lonely`: for readings with a common period `P > t0` the mirror `P − t0` is again a simple pinch, with `a`
  and `b` swapping roles (`TwoPinner.mirror_readings`), so the other sign of the condition is covered there.  One of the
  two signs always holds, and replacing `w` by `−w` covers `r ≤ 0`.  So the subject is lonely at every `r` near `0`,
  on both sides.
* `inside_wall_eventually_lonely`: if the direction keeps the pinners' ratio, both sides open at the leaving
  runner's opening, with no period needed.

This is `TwoPinnerN`'s mirror argument stated for arrangements and a direction, with the other runners' room carried
along, in the form the deformation theorem uses.  Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.PinchOpen

open Arrangement Filter Topology

theorem circDist_neg_po (x : ℝ) : circDist (-x) = circDist x := by
  unfold circDist
  rcases eq_or_ne (Int.fract x) 0 with h | h
  · rw [h, Int.fract_neg_eq_zero.mpr h]
  · rw [Int.fract_neg h, min_comm]
    congr 1; ring

theorem circDist_add_int_po (x : ℝ) (z : ℤ) : circDist (x + z) = circDist x := by
  unfold circDist
  rw [Int.fract_add_intCast]

theorem sep_line (v w : Fin 8 → ℝ) (r : ℝ) (k i : Fin 8) (t : ℝ) :
    sep (v + r • w) k i t = ((v i - v k) + r * (w i - w k)) * t := by
  simp only [sep, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem tendsto_line_reading (Di Wi Da Wa t0 : ℝ) (hDa : Da ≠ 0) :
    Tendsto (fun r : ℝ => (Di + r * Wi) * (t0 * Da / (Da + r * Wa))) (𝓝 0) (𝓝 (Di * t0)) := by
  have h1 : Tendsto (fun r : ℝ => Di + r * Wi) (𝓝 0) (𝓝 Di) := by
    simpa using ((continuous_const.add (continuous_id.mul continuous_const)).tendsto (0 : ℝ) :
      Tendsto (fun r : ℝ => Di + r * Wi) (𝓝 0) (𝓝 (Di + 0 * Wi)))
  have h2 : Tendsto (fun r : ℝ => Da + r * Wa) (𝓝 0) (𝓝 Da) := by
    simpa using ((continuous_const.add (continuous_id.mul continuous_const)).tendsto (0 : ℝ) :
      Tendsto (fun r : ℝ => Da + r * Wa) (𝓝 0) (𝓝 (Da + 0 * Wa)))
  have h4 : Tendsto (fun r : ℝ => t0 * Da / (Da + r * Wa)) (𝓝 0) (𝓝 (t0 * Da / Da)) :=
    (tendsto_const_nhds (x := t0 * Da)).div h2 hDa
  have h5 := h1.mul h4
  have e : Di * (t0 * Da / Da) = Di * t0 := by field_simp
  rwa [e] at h5

/-- **One side of a simple pinch.**  In the direction where the entering runner does not gain on the leaving one,
the leaving runner's own opening stays lonely. -/
theorem opens_at_leaving {v w : Fin 8 → ℝ} {k a b : Fin 8} {t0 ε : ℝ} {Na Nb : ℤ}
    (hak : a ≠ k) (hbk : b ≠ k) (hab : a ≠ b) (ht0 : 0 < t0) (hε : 0 < ε)
    (hDa : 0 < v a - v k) (hDb : 0 < v b - v k)
    (hA : (v a - v k) * t0 = Na + 1 / 8) (hB : (v b - v k) * t0 = Nb + 7 / 8)
    (hrest : ∀ i : Fin 8, i ≠ k → i ≠ a → i ≠ b → (8 : ℝ)⁻¹ + ε ≤ circDist (sep v k i t0))
    (hdir : (w b - w k) * (v a - v k) ≤ (w a - w k) * (v b - v k)) :
    ∀ᶠ r in 𝓝[≥] (0 : ℝ), 0 < t0 * (v a - v k) / ((v a - v k) + r * (w a - w k)) ∧
      LonelyAt (v + r • w) k (t0 * (v a - v k) / ((v a - v k) + r * (w a - w k))) := by
  set Da := v a - v k with hDa_def
  set Db := v b - v k with hDb_def
  set Wa := w a - w k
  set Wb := w b - w k
  have hden : ∀ᶠ r in 𝓝 (0 : ℝ), 0 < Da + r * Wa := by
    have : Tendsto (fun r : ℝ => Da + r * Wa) (𝓝 0) (𝓝 (Da + 0 * Wa)) :=
      ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0)
    simp only [zero_mul, add_zero] at this
    exact this.eventually (lt_mem_nhds hDa)
  -- runner b stays at or below its entering edge, and above the leaving edge of its lap
  have hb_lo : ∀ᶠ r in 𝓝 (0 : ℝ), (Nb : ℝ) + 1 / 8 ≤ (Db + r * Wb) * (t0 * Da / (Da + r * Wa)) := by
    have := tendsto_line_reading Db Wb Da Wa t0 hDa.ne'
    rw [hB] at this
    exact (this.eventually (lt_mem_nhds (by linarith : (Nb : ℝ) + 1 / 8 < Nb + 7 / 8))).mono fun _ h => h.le
  -- the other runners keep their room
  have hothers : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ i : Fin 8, i ≠ k → i ≠ a → i ≠ b →
      (8 : ℝ)⁻¹ ≤ circDist (sep (v + r • w) k i (t0 * Da / (Da + r * Wa))) := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : i ≠ k ∧ i ≠ a ∧ i ≠ b
    · have ht := tendsto_line_reading (v i - v k) (w i - w k) Da Wa t0 hDa.ne'
      have hc := (circDist_lipschitz.continuous.tendsto _).comp ht
      have hlim : (8 : ℝ)⁻¹ < circDist ((v i - v k) * t0) := by
        have := hrest i hi.1 hi.2.1 hi.2.2
        have e : sep v k i t0 = (v i - v k) * t0 := by simp only [sep]; ring
        rw [e] at this; linarith
      filter_upwards [hc.eventually (lt_mem_nhds hlim)] with r hr
      intro _ _ _
      rw [sep_line]; exact hr.le
    · filter_upwards with r
      intro h1 h2 h3; exact absurd ⟨h1, h2, h3⟩ hi
  have hge : ∀ᶠ r in 𝓝[≥] (0 : ℝ), 0 ≤ r := self_mem_nhdsWithin
  filter_upwards [hge, hden.filter_mono nhdsWithin_le_nhds, hb_lo.filter_mono nhdsWithin_le_nhds,
    hothers.filter_mono nhdsWithin_le_nhds] with r hr hd hlo hoth
  refine ⟨div_pos (mul_pos ht0 hDa) hd, ?_⟩
  intro i hik
  rw [sep_line]
  by_cases hia : i = a
  · subst hia
    have e : (Da + r * Wa) * (t0 * Da / (Da + r * Wa)) = (Na : ℝ) + 1 / 8 := by
      rw [← hA]; field_simp
    rw [e]; exact LRC.TwoPinner.clear_of_band (N := Na) le_rfl (by linarith)
  by_cases hib : i = b
  · subst hib
    refine LRC.TwoPinner.clear_of_band (N := Nb) hlo ?_
    rw [← hB, mul_div_assoc', div_le_iff₀ hd]
    have : r * (Wb * Da) ≤ r * (Wa * Db) := mul_le_mul_of_nonneg_left hdir hr
    nlinarith [mul_le_mul_of_nonneg_left this ht0.le]
  · have := hoth i hik hia hib
    rwa [sep_line] at this

/-- The mirror of a simple pinch, for readings with a common period `P` (every `(v i − v k)·P` a whole number): at
`P − t0` the two runners swap roles and every other runner is exactly as clear as before. -/
theorem mirror_pinch {v : Fin 8 → ℝ} {k a b : Fin 8} {t0 ε P : ℝ} {Na Nb : ℤ}
    (hper : ∀ i : Fin 8, ∃ z : ℤ, (v i - v k) * P = z)
    (hA : (v a - v k) * t0 = Na + 1 / 8) (hB : (v b - v k) * t0 = Nb + 7 / 8)
    (hrest : ∀ i : Fin 8, i ≠ k → i ≠ a → i ≠ b → (8 : ℝ)⁻¹ + ε ≤ circDist (sep v k i t0)) :
    (∃ Nb' : ℤ, (v b - v k) * (P - t0) = Nb' + 1 / 8) ∧ (∃ Na' : ℤ, (v a - v k) * (P - t0) = Na' + 7 / 8) ∧
      ∀ i : Fin 8, i ≠ k → i ≠ a → i ≠ b → (8 : ℝ)⁻¹ + ε ≤ circDist (sep v k i (P - t0)) := by
  obtain ⟨za, hza⟩ := hper a
  obtain ⟨zb, hzb⟩ := hper b
  refine ⟨⟨zb - Nb - 1, ?_⟩, ⟨za - Na - 1, ?_⟩, ?_⟩
  · push_cast; rw [mul_sub, hB, hzb]; ring
  · push_cast; rw [mul_sub, hA, hza]; ring
  · intro i h1 h2 h3
    obtain ⟨z, hz⟩ := hper i
    have e : sep v k i (P - t0) = -(sep v k i t0) + (z : ℝ) := by
      simp only [sep]; rw [← hz]; ring
    rw [e, circDist_add_int_po, circDist_neg_po]
    exact hrest i h1 h2 h3

/-- **The right side of a simple pinch, for readings with a common period `P > t0`.**  Whatever the direction, the
pinch itself or its mirror `P − t0` opens for small `r ≥ 0`. -/
theorem right_side {v w : Fin 8 → ℝ} {k a b : Fin 8} {t0 ε P : ℝ} {Na Nb : ℤ}
    (hak : a ≠ k) (hbk : b ≠ k) (hab : a ≠ b) (ht0 : 0 < t0) (hP : t0 < P) (hε : 0 < ε)
    (hDa : 0 < v a - v k) (hDb : 0 < v b - v k) (hper : ∀ i : Fin 8, ∃ z : ℤ, (v i - v k) * P = z)
    (hA : (v a - v k) * t0 = Na + 1 / 8) (hB : (v b - v k) * t0 = Nb + 7 / 8)
    (hrest : ∀ i : Fin 8, i ≠ k → i ≠ a → i ≠ b → (8 : ℝ)⁻¹ + ε ≤ circDist (sep v k i t0)) :
    ∀ᶠ r in 𝓝[≥] (0 : ℝ), LRC.Spec.LonelyForSubject (v + r • w) k := by
  rcases le_total ((w b - w k) * (v a - v k)) ((w a - w k) * (v b - v k)) with hdir | hdir
  · filter_upwards [opens_at_leaving hak hbk hab ht0 hε hDa hDb hA hB hrest hdir] with r hr
    exact ⟨_, hr.1, hr.2⟩
  · obtain ⟨⟨Nb', hB'⟩, ⟨Na', hA'⟩, hrest'⟩ := mirror_pinch (P := P) hper hA hB hrest
    have ht1 : 0 < P - t0 := by linarith
    have hrest'' : ∀ i : Fin 8, i ≠ k → i ≠ b → i ≠ a → (8 : ℝ)⁻¹ + ε ≤ circDist (sep v k i (P - t0)) :=
      fun i h1 h2 h3 => hrest' i h1 h3 h2
    filter_upwards [opens_at_leaving hbk hak hab.symm ht1 hε hDb hDa hB' hA' hrest'' hdir] with r hr
    exact ⟨_, hr.1, hr.2⟩

/-- Replacing `r` by `−r` and `w` by `−w`: a right-side statement for `−w` is a left-side statement for `w`. -/
theorem left_of_right {v w : Fin 8 → ℝ} {k : Fin 8}
    (hR : ∀ᶠ r in 𝓝[≥] (0 : ℝ), LRC.Spec.LonelyForSubject (v + r • (-w)) k) :
    ∀ᶠ r in 𝓝[≤] (0 : ℝ), LRC.Spec.LonelyForSubject (v + r • w) k := by
  have hneg : Tendsto (fun r : ℝ => -r) (𝓝[≤] (0 : ℝ)) (𝓝[≥] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have := ((continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds :
        Tendsto (fun r : ℝ => -r) (𝓝[≤] (0 : ℝ)) (𝓝 (-0)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simp only [Set.mem_Ici, Left.nonneg_neg_iff]; exact hr
  filter_upwards [hneg.eventually hR] with r hr
  have e : v + (-r) • (-w) = v + r • w := by ext i; simp
  rwa [e] at hr

/-- **A simple pinch is locally stable.**  For readings with a common period `P > t0`, the subject stays lonely under
every small change of speeds along any direction, on both sides.  `DeformationN.lonely_along_path`'s `hopen` at a
simple pinch. -/
theorem pinch_eventually_lonely {v w : Fin 8 → ℝ} {k a b : Fin 8} {t0 ε P : ℝ} {Na Nb : ℤ}
    (hak : a ≠ k) (hbk : b ≠ k) (hab : a ≠ b) (ht0 : 0 < t0) (hP : t0 < P) (hε : 0 < ε)
    (hDa : 0 < v a - v k) (hDb : 0 < v b - v k) (hper : ∀ i : Fin 8, ∃ z : ℤ, (v i - v k) * P = z)
    (hA : (v a - v k) * t0 = Na + 1 / 8) (hB : (v b - v k) * t0 = Nb + 7 / 8)
    (hrest : ∀ i : Fin 8, i ≠ k → i ≠ a → i ≠ b → (8 : ℝ)⁻¹ + ε ≤ circDist (sep v k i t0)) :
    ∀ᶠ r in 𝓝 (0 : ℝ), LRC.Spec.LonelyForSubject (v + r • w) k := by
  rw [← nhdsLE_sup_nhdsGE, Filter.eventually_sup]
  exact ⟨left_of_right (right_side (w := -w) hak hbk hab ht0 hP hε hDa hDb hper hA hB hrest),
    right_side (w := w) hak hbk hab ht0 hP hε hDa hDb hper hA hB hrest⟩

/-- **Inside the wall.**  If the direction keeps the two pinners' ratio (`(w b − w k)(v a − v k) =
(w a − w k)(v b − v k)`), the pinch persists on both sides at the leaving runner's opening; no period is needed. -/
theorem inside_wall_eventually_lonely {v w : Fin 8 → ℝ} {k a b : Fin 8} {t0 ε : ℝ} {Na Nb : ℤ}
    (hak : a ≠ k) (hbk : b ≠ k) (hab : a ≠ b) (ht0 : 0 < t0) (hε : 0 < ε)
    (hDa : 0 < v a - v k) (hDb : 0 < v b - v k)
    (hA : (v a - v k) * t0 = Na + 1 / 8) (hB : (v b - v k) * t0 = Nb + 7 / 8)
    (hrest : ∀ i : Fin 8, i ≠ k → i ≠ a → i ≠ b → (8 : ℝ)⁻¹ + ε ≤ circDist (sep v k i t0))
    (heq : (w b - w k) * (v a - v k) = (w a - w k) * (v b - v k)) :
    ∀ᶠ r in 𝓝 (0 : ℝ), LRC.Spec.LonelyForSubject (v + r • w) k := by
  rw [← nhdsLE_sup_nhdsGE, Filter.eventually_sup]
  refine ⟨left_of_right ?_, ?_⟩
  · have hdir : ((-w) b - (-w) k) * (v a - v k) ≤ ((-w) a - (-w) k) * (v b - v k) := by
      simp only [Pi.neg_apply]; nlinarith [heq]
    filter_upwards [opens_at_leaving hak hbk hab ht0 hε hDa hDb hA hB hrest hdir] with r hr
    exact ⟨_, hr.1, hr.2⟩
  · filter_upwards [opens_at_leaving hak hbk hab ht0 hε hDa hDb hA hB hrest heq.le] with r hr
    exact ⟨_, hr.1, hr.2⟩

end LRC.PinchOpen
