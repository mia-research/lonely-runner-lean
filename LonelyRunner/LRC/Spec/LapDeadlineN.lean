import LonelyRunner.LRC.Spec.PinchTransportN

/-!
# Carrying lap deadlines through forward moves

`lap` records the last opening crossed, including while a runner is captured.
`slack` is the remaining distance to that band's upper edge. Negative slack
means captured. This state is computed from the reading, not assumed as a
certificate. Updates retain all whole laps, including multi-lap jumps.

Absolute deadlines are nondecreasing, but remaining slack need not be. Nothing
here asserts global termination or that all groups eventually clear together.
-/

namespace LRC.LapDeadline

noncomputable def lap (d t : ℝ) : ℤ := ⌊d * t - 1 / 8⌋

noncomputable def slack (d t : ℝ) : ℝ := (lap d t : ℝ) + 7 / 8 - d * t

noncomputable def deadline (d t : ℝ) : ℝ := ((lap d t : ℝ) + 7 / 8) / d

/-- A runner's last-opening ledger always lies in this exact phase range. -/
theorem slack_bounds (d t : ℝ) : -(1 / 4 : ℝ) < slack d t ∧ slack d t ≤ 3 / 4 := by
  have hl := Int.floor_le (d * t - 1 / 8)
  have hu := Int.lt_floor_add_one (d * t - 1 / 8)
  dsimp [slack, lap]
  constructor <;> linarith

/-- The ledger's sign is precisely clearance, including equality endpoints. -/
theorem clear_iff_slack (d t : ℝ) :
    (8 : ℝ)⁻¹ ≤ circDist (d * t) ↔ 0 ≤ slack d t := by
  constructor
  · intro h
    obtain ⟨hl, hu⟩ := le_min_iff.mp h
    simp only [Int.fract] at hl hu
    have he : lap d t = ⌊d * t⌋ := by
      apply Int.floor_eq_iff.mpr
      constructor <;> linarith
    unfold slack
    rw [he]
    linarith
  · intro h
    apply LRC.TwoPinner.clear_of_band (N := lap d t)
    · have hf := Int.floor_le (d * t - 1 / 8)
      change (⌊d * t - 1 / 8⌋ : ℝ) + 1 / 8 ≤ d * t
      linarith
    · dsimp [slack] at h
      linarith

/-- Capture is the negative-slack case, not a separate geometric assumption. -/
theorem captured_iff_slack (d t : ℝ) :
    MomentIterationN.inWay 8 d t ↔ slack d t < 0 := by
  unfold MomentIterationN.inWay
  constructor
  · intro h
    exact lt_of_not_ge (fun hs => (not_le_of_gt h) ((clear_iff_slack d t).mpr hs))
  · intro h
    exact lt_of_not_ge (fun hc => (not_le_of_gt h) ((clear_iff_slack d t).mp hc))

/-- Actual clearance is equivalently being no later than the stored deadline. -/
theorem clear_iff_deadline {d t : ℝ} (hd : 0 < d) :
    (8 : ℝ)⁻¹ ≤ circDist (d * t) ↔ t ≤ deadline d t := by
  rw [clear_iff_slack]
  unfold slack deadline
  rw [le_div_iff₀ hd]
  constructor <;> intro h <;> nlinarith

/-- The integer label update accounts for every opening crossed in a move. -/
theorem lap_update (d t h : ℝ) :
    lap d (t + h) = lap d t + ⌊Int.fract (d * t - 1 / 8) + d * h⌋ := by
  have he : d * (t + h) - 1 / 8 =
      (lap d t : ℝ) + (Int.fract (d * t - 1 / 8) + d * h) := by
    simp only [lap, Int.fract]
    ring
  change ⌊d * (t + h) - 1 / 8⌋ = _
  rw [he, Int.floor_intCast_add]

/-- Each new opening adds one full lap of clearance; travel consumes d*h. -/
theorem slack_update (d t h : ℝ) :
    slack d (t + h) = slack d t + ((lap d (t + h) - lap d t : ℤ) : ℝ) - d * h := by
  unfold slack
  push_cast
  ring

/-- A closed-form update from the old phase and the elapsed time alone. -/
theorem slack_update_from_phase (d t h : ℝ) :
    slack d (t + h) = slack d t +
      (⌊Int.fract (d * t - 1 / 8) + d * h⌋ : ℝ) - d * h := by
  rw [slack_update, lap_update]
  simp

/-- Absolute deadlines advance by exactly one period per new opening. -/
theorem deadline_update (d t h : ℝ) :
    deadline d (t + h) = deadline d t +
      ((lap d (t + h) - lap d t : ℤ) : ℝ) / d := by
  unfold deadline
  push_cast
  ring

/-- Forward motion cannot decrease a positive disparity's stored lap label. -/
theorem lap_mono {d t T : ℝ} (hd : 0 ≤ d) (ht : t ≤ T) : lap d t ≤ lap d T := by
  apply Int.floor_mono
  dsimp
  nlinarith

/-- No opening is crossed until a quarter lap past the old deadline. -/
theorem lap_unchanged_iff {d t h : ℝ} (hd : 0 ≤ d) (hh : 0 ≤ h) :
    lap d (t + h) = lap d t ↔ d * h < slack d t + 1 / 4 := by
  unfold lap
  rw [Int.floor_eq_iff]
  have hl := Int.floor_le (d * t - 1 / 8)
  have hp := mul_nonneg hd hh
  unfold slack lap
  constructor
  · intro h
    linarith [h.2]
  · intro h
    constructor <;> nlinarith

/-- A runner with sufficient stored clearance needs no lap update at all. -/
theorem retain_deadline {d t h : ℝ} (hd : 0 ≤ d) (hh : 0 ≤ h)
    (hbudget : d * h ≤ slack d t) :
    lap d (t + h) = lap d t ∧ deadline d (t + h) = deadline d t ∧
      slack d (t + h) = slack d t - d * h ∧
      (8 : ℝ)⁻¹ ≤ circDist (d * (t + h)) := by
  have he := (lap_unchanged_iff hd hh).mpr (by linarith : d * h < slack d t + 1 / 4)
  have hs : slack d (t + h) = slack d t - d * h := by
    rw [slack_update, he]
    simp
  refine ⟨he, ?_, hs, (clear_iff_slack d (t + h)).mpr ?_⟩
  · unfold deadline
    rw [he]
  · rw [hs]
    linarith

/-- A known clear band identifies the stored lap without any search. -/
theorem lap_of_band {d t : ℝ} {K : ℤ}
    (hl : (K : ℝ) + 1 / 8 ≤ d * t) (hu : d * t ≤ K + 7 / 8) : lap d t = K := by
  apply Int.floor_eq_iff.mpr
  constructor <;> linarith

/-- During capture around K, the last opening was on lap K-1. -/
theorem lap_of_capture {d t : ℝ} {K : ℤ}
    (hc : |d * t - K| < (8 : ℝ)⁻¹) : lap d t = K - 1 := by
  apply Int.floor_eq_iff.mpr
  obtain ⟨hl, hu⟩ := abs_lt.mp hc
  push_cast
  norm_num at hl hu ⊢
  constructor <;> linarith

/-- The setter gets exactly three quarters of a lap of fresh clearance. -/
theorem setter_reset {b t : ℝ} {K : ℤ} (hb : 0 < b)
    (hc : |b * t - K| < (8 : ℝ)⁻¹) :
    lap b (MomentIterationN.nextOpening 8 b t) = K ∧
      slack b (MomentIterationN.nextOpening 8 b t) = 3 / 4 := by
  have he : b * MomentIterationN.nextOpening 8 b t = (K : ℝ) + 1 / 8 := by
    rw [MomentIterationN.nextOpening_eq hb hc]
    norm_num
    field_simp
  have hl := lap_of_band (d := b) (t := MomentIterationN.nextOpening 8 b t)
    (K := K) he.ge (by linarith)
  refine ⟨hl, ?_⟩
  unfold slack
  rw [hl, he]
  ring

/-- Carrying a whole positive-lap group: every member advances exactly ONE
opening label, and its absolute deadline advances by its own period 1/d.
The old capture hypotheses imply this; no future clearance is assumed. -/
theorem group_deadline_advance {d m t : ℝ} {K : ℤ}
    (hm : 0 < m) (hmd : m ≤ d) (hK : 1 ≤ K)
    (hmc : |m * t - K| < (8 : ℝ)⁻¹)
    (hdc : |d * t - K| < (8 : ℝ)⁻¹) :
    let T := MomentIterationN.nextOpening 8 m t
    lap d t = K - 1 ∧ lap d T = K ∧
      deadline d T = deadline d t + 1 / d ∧
      slack d T = slack d t + 1 - d * (T - t) ∧ 0 ≤ slack d T := by
  dsimp
  have hold := lap_of_capture hdc
  have hband := LRC.PinchTransport.same_lap_group_band hm hmd hK hmc hdc
  have hnew := lap_of_band hband.1 hband.2.le
  refine ⟨hold, hnew, ?_, ?_, ?_⟩
  · unfold deadline
    rw [hold, hnew]
    push_cast
    ring
  · unfold slack
    rw [hold, hnew]
    push_cast
    ring
  · unfold slack
    rw [hnew]
    linarith [hband.2]

/-- For a common clear lap, the slowest disparity controls the opening and
the fastest controls the deadline. Every interior reading is redundant for
this group's interval, even when the group has more than two members. -/
theorem group_window_iff (C : Finset ℝ) {m D s : ℝ} {K : ℤ}
    (hm : m ∈ C) (hD : D ∈ C) (hmpos : 0 < m) (hK : 0 ≤ K)
    (hmin : ∀ d ∈ C, m ≤ d) (hmax : ∀ d ∈ C, d ≤ D) :
    (∀ d ∈ C, (K : ℝ) + 1 / 8 ≤ d * s ∧ d * s ≤ K + 7 / 8) ↔
      ((K : ℝ) + 1 / 8) / m ≤ s ∧ s ≤ ((K : ℝ) + 7 / 8) / D := by
  have hDpos : 0 < D := hmpos.trans_le (hmin D hD)
  have hKR : (0 : ℝ) ≤ K := by exact_mod_cast hK
  constructor
  · intro h
    refine ⟨(div_le_iff₀ hmpos).mpr ?_, (le_div_iff₀ hDpos).mpr ?_⟩
    · nlinarith [(h m hm).1]
    · nlinarith [(h D hD).2]
  · rintro ⟨hl, hu⟩ d hd
    have hs : 0 ≤ s := (div_pos (by linarith : (0 : ℝ) < K + 1 / 8) hmpos).le.trans hl
    have hml := (div_le_iff₀ hmpos).mp hl
    have hDu := (le_div_iff₀ hDpos).mp hu
    have h1 := mul_le_mul_of_nonneg_right (hmin d hd) hs
    have h2 := mul_le_mul_of_nonneg_right (hmax d hd) hs
    constructor <;> nlinarith

/-- Positive-lap capture of the two extreme disparities forces a nonzero
common clear window after the slowest exit. -/
theorem group_window_nonempty {m D t : ℝ} {K : ℤ}
    (hm : 0 < m) (hmD : m ≤ D) (hK : 1 ≤ K)
    (hmc : |m * t - K| < (8 : ℝ)⁻¹)
    (hDc : |D * t - K| < (8 : ℝ)⁻¹) :
    ((K : ℝ) + 1 / 8) / m < ((K : ℝ) + 7 / 8) / D := by
  have h := LRC.PinchTransport.same_lap_group_band hm hmD hK hmc hDc
  rw [MomentIterationN.nextOpening_eq hm hmc] at h
  have hD : 0 < D := hm.trans_le hmD
  apply (lt_div_iff₀ hD).mpr
  norm_num at h
  nlinarith [h.2]

/-- The speed spread D-m gives the EXACT remaining length of that group
window; this is not a first-order approximation. -/
theorem group_window_width {m D : ℝ} (hm : m ≠ 0) (hD : D ≠ 0) (K : ℤ) :
    ((K : ℝ) + 7 / 8) / D - ((K : ℝ) + 1 / 8) / m =
      ((3 / 4 : ℝ) * m - ((K : ℝ) + 1 / 8) * (D - m)) / (m * D) := by
  field_simp
  ring

/-- The whole arrangement can be tested from the updated ledgers; the next
lap counts are computed, not supplied as a global grid certificate. -/
theorem lonely_after_shift_iff (ds : Finset ℝ) (t h : ℝ) :
    MomentIterationN.Lonely 8 ds (t + h) ↔
    ∀ d ∈ ds, d * h ≤ slack d t +
      (⌊Int.fract (d * t - 1 / 8) + d * h⌋ : ℝ) := by
  unfold MomentIterationN.Lonely
  apply forall_congr'; intro d
  apply forall_congr'; intro hd
  norm_num only [Nat.cast_ofNat]
  rw [one_div, clear_iff_slack, slack_update_from_phase]
  constructor <;> intro h <;> linarith

end LRC.LapDeadline
