import LonelyRunner.LRC.Cascade.Iteration

/-!
# The first nearest-reading gate

Readings are normalised so that the minimum is 1. R = 8t.
The width argument proves that a move from R ≤ 7 ends strictly below 9,
and no lonely instant lies in (7,9). It does not alone prove that an
arbitrary run visits 9. A sufficient additional separation hypothesis
for a forced move to 9 is proved below, not assumed universally.
-/

namespace LRC.FirstGate

open MomentIterationN ConstructionN

theorem zone_width {ρ : ℝ} (_hρ : 0 < ρ) (K : ℤ) :
    (8 * (K : ℝ) + 1) / ρ - (8 * (K : ℝ) - 1) / ρ = 2 / ρ := by ring

theorem faster_zone_width {ρ : ℝ} (hρ : 1 < ρ) (K : ℤ) :
    (8 * (K : ℝ) + 1) / ρ - (8 * (K : ℝ) - 1) / ρ < 2 := by
  rw [zone_width (by linarith) K]
  exact (div_lt_iff₀ (by linarith : 0 < ρ)).mpr (by linarith)

/-- A captured reading exits less than one whole zone-width later. -/
theorem opening_increment {d t : ℝ} (hd : 0 < d) (hw : inWay 8 d t) :
    nextOpening 8 d t < t + 1 / (4 * d) := by
  obtain ⟨K, hK⟩ := exists_near_int hw
  rw [nextOpening_eq hd hK]
  have hlo := (abs_lt.mp hK).1
  norm_num at hlo ⊢
  apply (div_lt_iff₀ hd).mpr
  have he : (1 / (4 * d)) * d = (1 : ℝ) / 4 := by field_simp
  norm_num at he
  nlinarith

/-- Even equality R=7 cannot jump directly to R=9: zones are open. -/
theorem move_lt_nine_of_le_seven {S : Finset ℝ} {t : ℝ}
    (hmin : ∀ d ∈ S, 1 ≤ d) (ht : t ≤ 7 / 8) :
    move 8 S t < 9 / 8 := by
  rcases move_eq_self_or_opening (n := 8) S t with h | ⟨d, hd, hw, he⟩
  · linarith
  · have hd1 := hmin d hd
    have hp : 0 < d := by linarith
    have hi := opening_increment hp hw
    have hwidth : 1 / (4 * d) ≤ (1 : ℝ) / 4 :=
      (div_le_iff₀ (by positivity : 0 < 4 * d)).mpr (by linarith)
    linarith

theorem nearest_inWay {t : ℝ} (hl : 7 / 8 < t) (hu : t < 9 / 8) :
    inWay 8 1 t := by
  unfold inWay
  have hdist := circDist_le_abs_sub_int (1 * t) (1 : ℤ)
  have h : |1 * t - (1 : ℤ)| < (8 : ℝ)⁻¹ := by
    rw [abs_lt]
    norm_num
    constructor <;> linarith
  exact lt_of_le_of_lt hdist h

theorem nearest_opening {t : ℝ} (hl : 7 / 8 < t) (hu : t < 9 / 8) :
    nextOpening 8 1 t = 9 / 8 := by
  have h : |1 * t - (1 : ℤ)| < (8 : ℝ)⁻¹ := by
    rw [abs_lt]
    norm_num
    constructor <;> linarith
  rw [nextOpening_eq (by norm_num : (0 : ℝ) < 1) h]
  norm_num

/-- This concerns a lonely endpoint, and asserts no termination theorem. -/
theorem lonely_above_seven_iff {S : Finset ℝ} {t : ℝ}
    (hone : 1 ∈ S) (hlonely : Lonely 8 S t) :
    7 / 8 < t ↔ 9 / 8 ≤ t := by
  constructor
  · intro h
    by_contra hn
    have hw := nearest_inWay h (lt_of_not_ge hn)
    exact (not_lt_of_ge (hlonely 1 hone)) hw
  · intro h
    linarith

/-- Inside the nearest zone, the max-exit move reaches at least 9. -/
theorem move_ge_nine {S : Finset ℝ} {t : ℝ} (hone : 1 ∈ S)
    (hl : 7 / 8 < t) (hu : t < 9 / 8) : 9 / 8 ≤ move 8 S t := by
  have h := nextOpening_le_move (n := 8) hone (nearest_inWay hl hu)
  rwa [nearest_opening hl hu] at h

/-- A genuine sufficient rule forcing 9, rather than merely passing it:
before R=8, all other readings ≥2 exit strictly before 9. -/
theorem forced_nearest_move {S : Finset ℝ} {t : ℝ}
    (hone : 1 ∈ S) (hgap : ∀ d ∈ S, d = 1 ∨ 2 ≤ d)
    (hl : 7 / 8 < t) (hu : t ≤ 1) : move 8 S t = 9 / 8 := by
  have hu9 : t < 9 / 8 := by linarith
  have hlow := move_ge_nine hone hl hu9
  rcases move_eq_self_or_opening (n := 8) S t with h | ⟨d, hd, hw, he⟩
  · linarith
  · rcases hgap d hd with hd1 | hd2
    · subst d
      rw [he, nearest_opening hl hu9]
    · have hi := opening_increment (by linarith : 0 < d) hw
      have hwidth : 1 / (4 * d) ≤ (1 : ℝ) / 8 :=
        (div_le_iff₀ (by positivity : 0 < 4 * d)).mpr (by linarith)
      linarith

theorem nearest_clear_first_window {t : ℝ} (hl : 1 / 8 ≤ t) (hu : t ≤ 7 / 8) :
    ¬ inWay 8 1 t := by
  intro hw
  obtain ⟨K, hK⟩ := exists_near_int hw
  have h1 := (abs_lt.mp hK).1
  have h2 := (abs_lt.mp hK).2
  norm_num at h1 h2
  have ha : (0 : ℝ) < K := by linarith
  have hb : (K : ℝ) < 1 := by linarith
  have hai : (0 : ℤ) < K := by exact_mod_cast ha
  have hbi : K < 1 := by exact_mod_cast hb
  omega

/-- With every other reading at least 2, the first crossing stays below R=8. -/
theorem first_crossing_below_eight {S : Finset ℝ} {t : ℝ}
    (hgap : ∀ d ∈ S, d = 1 ∨ 2 ≤ d)
    (hl : 1 / 8 ≤ t) (hu : t ≤ 7 / 8) : move 8 S t < 1 := by
  rcases move_eq_self_or_opening (n := 8) S t with h | ⟨d, hd, hw, he⟩
  · linarith
  · rcases hgap d hd with hd1 | hd2
    · subst d
      exact (nearest_clear_first_window hl hu hw).elim
    · have hi := opening_increment (by linarith : 0 < d) hw
      have hwidth : 1 / (4 * d) ≤ (1 : ℝ) / 8 :=
        (div_le_iff₀ (by positivity : 0 < 4 * d)).mpr (by linarith)
      linarith

/-- A conditional run-level equivalence, without a termination assumption.
The extra speed-gap hypothesis is essential to this proof, not asserted
as a universal property of eight-runner arrangements. -/
theorem crossing_iff_visits_nine {S : Finset ℝ}
    (hone : 1 ∈ S) (hgap : ∀ d ∈ S, d = 1 ∨ 2 ≤ d) :
    (∃ N : ℕ, 7 / 8 < (move 8 S)^[N] (1 / 8)) ↔
      ∃ N : ℕ, (move 8 S)^[N] (1 / 8) = 9 / 8 := by
  constructor
  · rintro ⟨N, hN⟩
    induction N with
    | zero => norm_num at hN
    | succ N ih =>
      by_cases hp : 7 / 8 < (move 8 S)^[N] (1 / 8)
      · exact ih hp
      · have hlo := iterate_ge (n := 8) S (1 / 8) N
        have hhi := first_crossing_below_eight hgap hlo (le_of_not_gt hp)
        rw [Function.iterate_succ_apply'] at hN
        refine ⟨N + 2, ?_⟩
        rw [show N + 2 = (N + 1) + 1 by omega, Function.iterate_succ_apply',
          Function.iterate_succ_apply']
        exact forced_nearest_move hone hgap hN hhi.le
  · rintro ⟨N, hN⟩
    exact ⟨N, by rw [hN]; norm_num⟩

/-- Under the same explicit gap hypothesis, a crossing forces the nearest
reading to attain the maximum exit on some move, not merely to be blocked. -/
theorem crossing_forces_nearest_setter {S : Finset ℝ}
    (hone : 1 ∈ S) (hgap : ∀ d ∈ S, d = 1 ∨ 2 ≤ d) {N : ℕ}
    (hN : 7 / 8 < (move 8 S)^[N] (1 / 8)) :
    ∃ j : ℕ, inWay 8 1 ((move 8 S)^[j] (1 / 8)) ∧
      move 8 S ((move 8 S)^[j] (1 / 8)) =
        nextOpening 8 1 ((move 8 S)^[j] (1 / 8)) := by
  induction N with
  | zero => norm_num at hN
  | succ N ih =>
    by_cases hp : 7 / 8 < (move 8 S)^[N] (1 / 8)
    · exact ih hp
    · have hhi := first_crossing_below_eight hgap
        (iterate_ge (n := 8) S (1 / 8) N) (le_of_not_gt hp)
      rw [Function.iterate_succ_apply'] at hN
      refine ⟨N + 1, ?_⟩
      rw [Function.iterate_succ_apply']
      have hu9 : move 8 S ((move 8 S)^[N] (1 / 8)) < 9 / 8 := by linarith
      exact ⟨nearest_inWay hN hu9,
        (forced_nearest_move hone hgap hN hhi.le).trans (nearest_opening hN hu9).symm⟩

/-- The three events in the gate claim are equivalent for this separated
region. A lonely finite iterate is supplied; termination is not assumed proved. -/
theorem terminal_gate_equivalences {S : Finset ℝ}
    (hone : 1 ∈ S) (hgap : ∀ d ∈ S, d = 1 ∨ 2 ≤ d) (N : ℕ)
    (hlonely : Lonely 8 S ((move 8 S)^[N] (1 / 8))) :
    ((7 / 8 < (move 8 S)^[N] (1 / 8)) ↔
      ∃ j : ℕ, (move 8 S)^[j] (1 / 8) = 9 / 8) ∧
    ((7 / 8 < (move 8 S)^[N] (1 / 8)) ↔
      ∃ j : ℕ, inWay 8 1 ((move 8 S)^[j] (1 / 8)) ∧
        move 8 S ((move 8 S)^[j] (1 / 8)) =
          nextOpening 8 1 ((move 8 S)^[j] (1 / 8))) := by
  have hpos : ∀ d ∈ S, 0 < d := by
    intro d hd
    rcases hgap d hd with h | h <;> linarith
  have hbound := iterate_le_of_lonely hpos hlonely (iterate_ge (n := 8) S (1 / 8) N)
  constructor
  · constructor
    · intro h
      exact (crossing_iff_visits_nine hone hgap).mp ⟨N, h⟩
    · rintro ⟨j, hj⟩
      have hb := hbound j
      rw [hj] at hb
      linarith
  · constructor
    · exact crossing_forces_nearest_setter hone hgap
    · rintro ⟨j, hw, _⟩
      have hjlo := iterate_ge (n := 8) S (1 / 8) j
      have hjhi : 7 / 8 < (move 8 S)^[j] (1 / 8) := by
        by_contra h
        exact nearest_clear_first_window hjlo (le_of_not_gt h) hw
      exact hjhi.trans_le (hbound j)

end LRC.FirstGate
