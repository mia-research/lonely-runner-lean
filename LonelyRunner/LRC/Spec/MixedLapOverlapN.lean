import LonelyRunner.LRC.Spec.LapDeadlineN

/-!
# Overlap of renewed windows with different integer lap labels

Every active runner has passed its own opening at the maximum-exit cascade
move. An active group bounded above by D remains clear until t+3/(4D).
If D<=3b for the actual setter b, this is a nonempty common window AFTER
the move, independently of the group's integer lap labels.

One outside runner must overlap this window if its remaining length is at
least 1/(4e). This yields a genuine at-most-two-move isolation criterion,
not an assumption of eventual overlap for arbitrary seven-reading sets.
-/

namespace LRC.MixedLapOverlap

open MomentIterationN

/-- The latest exit passes the opening of every runner currently captured. -/
theorem active_lower_at_move {ds : Finset ℝ} {d t : ℝ} {K : ℤ}
    (hdS : d ∈ ds) (hd : 0 < d)
    (hc : |d * t - K| < (8 : ℝ)⁻¹) :
    (K : ℝ) + 1 / 8 ≤ d * move 8 ds t := by
  have hw : inWay 8 d t :=
    lt_of_le_of_lt (ConstructionN.circDist_le_abs_sub_int _ K) hc
  have h := nextOpening_le_move hdS hw
  rw [nextOpening_eq hd hc, div_le_iff₀ hd] at h
  norm_num at h
  nlinarith

/-- A currently captured group shares a future clear window without sharing
an integer lap. The lower endpoint is the ACTUAL cascade move. -/
theorem active_clear_until {ds : Finset ℝ} {d D t s : ℝ}
    (hdS : d ∈ ds) (hd : 0 < d) (hD : 0 < D) (hdD : d ≤ D)
    (hw : inWay 8 d t) (hlo : move 8 ds t ≤ s)
    (hhi : s ≤ t + 3 / (4 * D)) :
    (8 : ℝ)⁻¹ ≤ circDist (d * s) := by
  obtain ⟨K, hc⟩ := exists_near_int hw
  have hl := active_lower_at_move hdS hd hc
  have hmono := mul_le_mul_of_nonneg_left hlo hd.le
  have ht : t ≤ s := (le_move ds t).trans hlo
  have hbound : D * (s - t) ≤ 3 / 4 := by
    have hh : s - t ≤ 3 / (4 * D) := by linarith
    rw [le_div_iff₀ (by positivity : 0 < 4 * D)] at hh
    nlinarith
  have hratio := mul_le_mul_of_nonneg_right hdD (sub_nonneg.mpr ht)
  have hu := (abs_lt.mp hc).2
  norm_num at hu
  apply LRC.TwoPinner.clear_of_band (N := K) <;> nlinarith

/-- A factor-three bound makes that mixed-lap common window nonempty. -/
theorem move_before_group_deadline {ds : Finset ℝ} {b D t : ℝ}
    (hb : 0 < b) (hD : 0 < D) (hDb : D ≤ 3 * b)
    (hw : inWay 8 b t) (hsetter : move 8 ds t = nextOpening 8 b t) :
    move 8 ds t < t + 3 / (4 * D) := by
  obtain ⟨K, hc⟩ := exists_near_int hw
  have h := LRC.PinchTransport.displacement_lt_three_quarters hb hDb hc
  rw [hsetter]
  have hh : nextOpening 8 b t - t < 3 / (4 * D) := by
    rw [lt_div_iff₀ (by positivity : 0 < 4 * D)]
    nlinarith
  linarith

/-- Any old blocker that is STILL blocked after the move must exceed three
times the setter's disparity. New blockers need not satisfy this bound. -/
theorem persistent_blocker_gt_three {ds : Finset ℝ} {b d t : ℝ}
    (hdS : d ∈ ds) (hd : 0 < d) (hb : 0 < b)
    (hbt : inWay 8 b t) (hdt : inWay 8 d t)
    (hsetter : move 8 ds t = nextOpening 8 b t)
    (hafter : inWay 8 d (move 8 ds t)) : 3 * b < d := by
  by_contra hn
  have hr : d ≤ 3 * b := le_of_not_gt hn
  have ht := move_before_group_deadline hb hd hr hbt hsetter
  have hc := active_clear_until hdS hd hd le_rfl hdt le_rfl ht.le
  exact (not_lt_of_ge hc) hafter

/-- An arbitrary outside runner cannot block a WHOLE retained interval of
length at least a quarter of its period. The witness is its next opening if
the interval's left endpoint is blocked, otherwise that endpoint itself. -/
theorem outsider_overlaps {e T U : ℝ} (he : 0 < e)
    (hwidth : T + 1 / (4 * e) ≤ U) :
    ∃ s : ℝ, T ≤ s ∧ s ≤ U ∧ (8 : ℝ)⁻¹ ≤ circDist (e * s) ∧
      (s = T ∨ s = nextOpening 8 e T) := by
  by_cases hw : inWay 8 e T
  · obtain ⟨K, hc⟩ := exists_near_int hw
    have h := LRC.PinchTransport.exit_shift_bounds he hc
    have hh : nextOpening 8 e T - T < 1 / (4 * e) := by
      rw [lt_div_iff₀ (by positivity : 0 < 4 * e)]
      nlinarith [h.2]
    exact ⟨nextOpening 8 e T, by linarith [h.1], by linarith,
      (circDist_at_nextOpening he).ge, Or.inr rfl⟩
  · have ht : T ≤ U := by
      have : 0 < 1 / (4 * e) := by positivity
      linarith
    exact ⟨T, le_rfl, ht, le_of_not_gt hw, Or.inl rfl⟩

/-- Renewed mixed-lap group windows must meet one outsider when the explicit
width budget holds. The resulting witness is at the first or second ACTUAL
cascade move, not at a freely chosen successful history. -/
theorem overlap_with_one_outsider {ds : Finset ℝ} {e D t : ℝ}
    (heS : e ∈ ds) (he : 0 < e) (hD : 0 < D)
    (hpos : ∀ d ∈ ds, 0 < d)
    (hgroup : ∀ d ∈ ds, d ≠ e → inWay 8 d t ∧ d ≤ D)
    (hwidth : move 8 ds t + 1 / (4 * e) ≤ t + 3 / (4 * D)) :
    Lonely 8 ds (move 8 ds t) ∨ Lonely 8 ds (move 8 ds (move 8 ds t)) := by
  obtain ⟨s, hslo, hshi, hse, hs⟩ := outsider_overlaps he hwidth
  have hlonely : Lonely 8 ds s := by
    intro d hd
    by_cases hde : d = e
    · simpa [hde] using hse
    · exact active_clear_until hd (hpos d hd) hD (hgroup d hd hde).2
        (hgroup d hd hde).1 hslo hshi
  rcases hs with h | h
  · exact Or.inl (h ▸ hlonely)
  · by_cases hw : inWay 8 e (move 8 ds t)
    · have hEq : move 8 ds (move 8 ds t) = s := by
        apply le_antisymm
        · exact move_le_of_lonely hpos hlonely hslo
        · rw [h]
          exact nextOpening_le_move heS hw
      exact Or.inr (hEq ▸ hlonely)
    · left
      intro d hd
      by_cases hde : d = e
      · simpa [hde] using (le_of_not_gt hw)
      · apply active_clear_until hd (hpos d hd) hD (hgroup d hd hde).2
          (hgroup d hd hde).1 le_rfl
        have : 0 < 1 / (4 * e) := by positivity
        linarith

/-- A purely disparity-based budget guarantees the width needed above.
No future loneliness or successful lap assignment is a hypothesis. -/
theorem two_moves_of_disparity_budget {ds : Finset ℝ} {b e D t : ℝ}
    (heS : e ∈ ds) (hb : 0 < b) (he : 0 < e) (hD : 0 < D)
    (hpos : ∀ d ∈ ds, 0 < d)
    (hgroup : ∀ d ∈ ds, d ≠ e → inWay 8 d t ∧ d ≤ D)
    (hbt : inWay 8 b t) (hsetter : move 8 ds t = nextOpening 8 b t)
    (hbudget : D * (b + e) ≤ 3 * b * e) :
    Lonely 8 ds (move 8 ds t) ∨ Lonely 8 ds (move 8 ds (move 8 ds t)) := by
  apply overlap_with_one_outsider heS he hD hpos hgroup
  obtain ⟨K, hc⟩ := exists_near_int hbt
  have hshift := LRC.PinchTransport.exit_shift_bounds hb hc
  have ht : move 8 ds t - t < 1 / (4 * b) := by
    rw [hsetter, lt_div_iff₀ (by positivity : 0 < 4 * b)]
    nlinarith [hshift.2]
  have heq : 1 / (4 * b) + 1 / (4 * e) = (b + e) / (4 * b * e) := by
    field_simp
    ring
  have hsum : 1 / (4 * b) + 1 / (4 * e) ≤ 3 / (4 * D) := by
    rw [heq, div_le_div_iff₀ (by positivity : 0 < 4 * b * e)
      (by positivity : 0 < 4 * D)]
    nlinarith
  linarith

/-- Waiting for one captured runner costs strictly less than a quarter period. -/
theorem opening_time_bound {d t : ℝ} (hd : 0 < d) (hw : inWay 8 d t) :
    t < nextOpening 8 d t ∧ nextOpening 8 d t < t + 1 / (4 * d) := by
  obtain ⟨K, hc⟩ := exists_near_int hw
  have h := LRC.PinchTransport.exit_shift_bounds hd hc
  refine ⟨by linarith [h.1], ?_⟩
  have hh : nextOpening 8 d t - t < 1 / (4 * d) := by
    rw [lt_div_iff₀ (by positivity : 0 < 4 * d)]
    nlinarith [h.2]
  linarith

/-- After the slower runner's opening, waiting for a faster runner preserves
the slower one's band. Thus their overlap costs at most one faster exit. -/
theorem pair_after_slow_opening {a b T : ℝ} {K : ℤ}
    (ha : 0 < a) (hab : a ≤ b) (hstart : a * T = (K : ℝ) + 1 / 8) :
    ∃ s : ℝ, T ≤ s ∧ s < T + 1 / (4 * b) ∧
      (8 : ℝ)⁻¹ ≤ circDist (a * s) ∧ (8 : ℝ)⁻¹ ≤ circDist (b * s) := by
  have hb : 0 < b := ha.trans_le hab
  by_cases hw : inWay 8 b T
  · obtain ⟨L, hc⟩ := exists_near_int hw
    have hpair := LRC.PinchTransport.handoff_pair_clear ha hb (by linarith) hstart hc
    have ht := opening_time_bound hb hw
    exact ⟨nextOpening 8 b T, ht.1.le, ht.2, hpair⟩
  · refine ⟨T, le_rfl, ?_, ?_, le_of_not_gt hw⟩
    · have : 0 < 1 / (4 * b) := by positivity
      linarith
    · exact LRC.TwoPinner.clear_of_band hstart.ge (by linarith)

/-- Two outside runners cannot jointly block a retained window this wide.
The proof follows their actual forward exits; it works for all initial phases
and all positive disparity ratios, including commensurate ones. -/
theorem two_outsiders_overlap {a b T U : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hwidth : T + 1 / (4 * a) + 1 / (2 * b) ≤ U) :
    ∃ s : ℝ, T ≤ s ∧ s ≤ U ∧
      (8 : ℝ)⁻¹ ≤ circDist (a * s) ∧ (8 : ℝ)⁻¹ ≤ circDist (b * s) := by
  have hb : 0 < b := ha.trans_le hab
  have hhalf : 1 / (2 * b) = 1 / (4 * b) + 1 / (4 * b) := by ring
  have haquarter : 0 < 1 / (4 * a) := by positivity
  have hbquarter : 0 < 1 / (4 * b) := by positivity
  have finish (R : ℝ) (hTR : T ≤ R) (hR : R < T + 1 / (4 * b))
      (hw : inWay 8 a R) :
      ∃ s : ℝ, T ≤ s ∧ s ≤ U ∧
        (8 : ℝ)⁻¹ ≤ circDist (a * s) ∧ (8 : ℝ)⁻¹ ≤ circDist (b * s) := by
    obtain ⟨K, hc⟩ := exists_near_int hw
    have hstart : a * nextOpening 8 a R = (K : ℝ) + 1 / 8 := by
      rw [nextOpening_eq ha hc]
      norm_num
      field_simp
    obtain ⟨s, hslo, hshi, hsa, hsb⟩ := pair_after_slow_opening ha hab hstart
    have hA := opening_time_bound ha hw
    exact ⟨s, hTR.trans (hA.1.le.trans hslo), by linarith, hsa, hsb⟩
  by_cases haw : inWay 8 a T
  · exact finish T le_rfl (by linarith) haw
  · by_cases hbw : inWay 8 b T
    · have hB := opening_time_bound hb hbw
      by_cases haB : inWay 8 a (nextOpening 8 b T)
      · exact finish (nextOpening 8 b T) hB.1.le hB.2 haB
      · exact ⟨nextOpening 8 b T, hB.1.le, by linarith,
          le_of_not_gt haB, (circDist_at_nextOpening hb).ge⟩
    · exact ⟨T, le_rfl, by linarith, le_of_not_gt haw, le_of_not_gt hbw⟩

/-- Previously clear readings can join the protected group using their stored
slack. Only explicit current-state inequalities are needed. -/
theorem protected_clear_until {ds : Finset ℝ} {d D t s : ℝ}
    (hdS : d ∈ ds) (hd : 0 < d) (hD : 0 < D)
    (hstate : (inWay 8 d t ∧ d ≤ D) ∨ d * (3 / (4 * D)) ≤ LRC.LapDeadline.slack d t)
    (hlo : move 8 ds t ≤ s) (hhi : s ≤ t + 3 / (4 * D)) :
    (8 : ℝ)⁻¹ ≤ circDist (d * s) := by
  rcases hstate with h | h
  · exact active_clear_until hdS hd hD h.2 h.1 hlo hhi
  · have ht : t ≤ s := (le_move ds t).trans hlo
    have hbudget : d * (s - t) ≤ LRC.LapDeadline.slack d t := by
      have hh : s - t ≤ 3 / (4 * D) := by linarith
      exact (mul_le_mul_of_nonneg_left hh hd.le).trans h
    have hc := (LRC.LapDeadline.retain_deadline hd.le (sub_nonneg.mpr ht) hbudget).2.2.2
    simpa only [add_sub_cancel] using hc

/-- One outsider can be combined with both renewed blockers and sufficiently
long previously calculated bands. -/
theorem protected_group_overlaps_one {ds : Finset ℝ} {e D t : ℝ}
    (he : 0 < e) (hD : 0 < D) (hpos : ∀ d ∈ ds, 0 < d)
    (hgroup : ∀ d ∈ ds, d ≠ e →
      (inWay 8 d t ∧ d ≤ D) ∨ d * (3 / (4 * D)) ≤ LRC.LapDeadline.slack d t)
    (hwidth : move 8 ds t + 1 / (4 * e) ≤ t + 3 / (4 * D)) :
    ∃ s : ℝ, move 8 ds t ≤ s ∧ s ≤ t + 3 / (4 * D) ∧ Lonely 8 ds s := by
  obtain ⟨s, hslo, hshi, hse, _⟩ := outsider_overlaps he hwidth
  refine ⟨s, hslo, hshi, fun d hd => ?_⟩
  by_cases hde : d = e
  · simpa [hde] using hse
  · exact protected_clear_until hd (hpos d hd) hD (hgroup d hd hde) hslo hshi

/-- Actual seven-reading applications may leave two outsiders: all other
readings are either renewed blockers or have enough retained slack. Under
the width budget, an isolation witness lies inside their common window. -/
theorem protected_group_overlaps_two {ds : Finset ℝ} {a b D t : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hD : 0 < D)
    (hpos : ∀ d ∈ ds, 0 < d)
    (hgroup : ∀ d ∈ ds, d ≠ a → d ≠ b →
      (inWay 8 d t ∧ d ≤ D) ∨ d * (3 / (4 * D)) ≤ LRC.LapDeadline.slack d t)
    (hwidth : move 8 ds t + 1 / (4 * a) + 1 / (2 * b) ≤ t + 3 / (4 * D)) :
    ∃ s : ℝ, move 8 ds t ≤ s ∧ s ≤ t + 3 / (4 * D) ∧ Lonely 8 ds s := by
  obtain ⟨s, hslo, hshi, hsa, hsb⟩ := two_outsiders_overlap ha hab hwidth
  refine ⟨s, hslo, hshi, fun d hd => ?_⟩
  by_cases hda : d = a
  · simpa [hda] using hsa
  · by_cases hdb : d = b
    · simpa [hdb] using hsb
    · exact protected_clear_until hd (hpos d hd) hD (hgroup d hd hda hdb) hslo hshi

end LRC.MixedLapOverlap
