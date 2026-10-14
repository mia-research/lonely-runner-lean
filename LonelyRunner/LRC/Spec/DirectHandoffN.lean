import LonelyRunner.LRC.Spec.TwoPinnerN
import LonelyRunner.LRC.Cascade.Iteration

/-!
# Direct protection of the previous setter

At b's opening r, suppose c is captured about its actual integer centre J.
Its next opening is s=(J+1/8)/c. If b<=3c, that opening strictly clears b
in b's current band. Thus compatibility of these two readings is DERIVED
from their speed ratio and current positions, not assumed at the new instant.

Conversely, immediate recapture of b at c's opening forces b>3c. This is
a restriction on a handoff, not a decreasing quantity for an entire cascade.
Other readings can still obstruct s. No period, approximation, strict old
isolation witness, or lower-order loneliness theorem is required.
-/

namespace LRC.DirectHandoff

/-- A captured successor at least one third as fast as the previous setter
exits before that setter's clear band closes. Capture inequalities are strict;
consequently b's clearance is strict even at the ratio endpoint b=3c. -/
theorem successor_bands {b c r : ℝ} (K J : ℤ)
    (hb : 0 < b) (hc : 0 < c)
    (hopen : b * r = (K : ℝ) + 1 / 8)
    (hcaplo : (J : ℝ) - 1 / 8 < c * r)
    (hcaphi : c * r < (J : ℝ) + 1 / 8)
    (hratio : b ≤ 3 * c) :
    let s := ((J : ℝ) + 1 / 8) / c
    r < s ∧ c * s = (J : ℝ) + 1 / 8 ∧
      (K : ℝ) + 1 / 8 < b * s ∧ b * s < (K : ℝ) + 7 / 8 := by
  dsimp only
  let s : ℝ := ((J : ℝ) + 1 / 8) / c
  have hs : c * s = (J : ℝ) + 1 / 8 := by
    dsimp [s]
    field_simp
  have hstep : 0 < s - r := by nlinarith
  have hwidth : c * (s - r) < 1 / 4 := by nlinarith
  have hbound : b * (s - r) ≤ (3 * c) * (s - r) :=
    mul_le_mul_of_nonneg_right hratio hstep.le
  have hmove : 0 < b * (s - r) := mul_pos hb hstep
  change r < s ∧ c * s = _ ∧ _ < b * s ∧ b * s < _
  exact ⟨by linarith, hs, by nlinarith, by nlinarith⟩

/-- The derived place is an actual positive clear instant for both readings.
There is no hypothesis asserting their clearance at that place. -/
theorem successor_clear {b c r : ℝ} (K J : ℤ)
    (hb : 0 < b) (hc : 0 < c) (hr : 0 < r)
    (hopen : b * r = (K : ℝ) + 1 / 8)
    (hcaplo : (J : ℝ) - 1 / 8 < c * r)
    (hcaphi : c * r < (J : ℝ) + 1 / 8)
    (hratio : b ≤ 3 * c) :
    let s := ((J : ℝ) + 1 / 8) / c
    0 < s ∧ (8 : ℝ)⁻¹ ≤ circDist (b * s) ∧
      (8 : ℝ)⁻¹ ≤ circDist (c * s) := by
  obtain ⟨hrs, hs, hlo, hhi⟩ := successor_bands K J hb hc hopen hcaplo hcaphi hratio
  refine ⟨hr.trans hrs, TwoPinner.clear_of_band hlo.le hhi.le, ?_⟩
  apply TwoPinner.clear_of_band (N := J)
  · exact hs.ge
  · linarith

/-- If the previous setter is captured again at its successor's opening,
the change of setter necessarily decreases disparity by more than factor 3.
This does not constrain later returns after intervening handoffs. -/
theorem recapture_requires_drop {b c r : ℝ} (K J : ℤ)
    (hb : 0 < b) (hc : 0 < c)
    (hopen : b * r = (K : ℝ) + 1 / 8)
    (hcaplo : (J : ℝ) - 1 / 8 < c * r)
    (hcaphi : c * r < (J : ℝ) + 1 / 8)
    (hreturn : circDist (b * (((J : ℝ) + 1 / 8) / c)) < (8 : ℝ)⁻¹) :
    3 * c < b := by
  by_contra hn
  have hratio : b ≤ 3 * c := le_of_not_gt hn
  obtain ⟨_, _, hlo, hhi⟩ := successor_bands K J hb hc hopen hcaplo hcaphi hratio
  exact (not_lt_of_ge (TwoPinner.clear_of_band hlo.le hhi.le)) hreturn

/-- After an immediate return to the first setter, its next exit necessarily
clears the second setter. An alternating two-reading obstruction cannot
persist through this third exit; other readings are not covered by this fact.
The third exit is b's own opening: the maximum-exit cascade may instead
select a later opening belonging to another captured reading. -/
theorem return_exit_clears_pair {b c r : ℝ} (K J I : ℤ)
    (hb : 0 < b) (hc : 0 < c) (hr : 0 < r)
    (hopen : b * r = (K : ℝ) + 1 / 8)
    (hcaplo : (J : ℝ) - 1 / 8 < c * r)
    (hcaphi : c * r < (J : ℝ) + 1 / 8)
    (hreturn : circDist (b * (((J : ℝ) + 1 / 8) / c)) < (8 : ℝ)⁻¹)
    (hbacklo : (I : ℝ) - 1 / 8 < b * (((J : ℝ) + 1 / 8) / c))
    (hbackhi : b * (((J : ℝ) + 1 / 8) / c) < (I : ℝ) + 1 / 8) :
    let u := ((I : ℝ) + 1 / 8) / b
    0 < u ∧ (8 : ℝ)⁻¹ ≤ circDist (c * u) ∧
      (8 : ℝ)⁻¹ ≤ circDist (b * u) := by
  have hdrop := recapture_requires_drop K J hb hc hopen hcaplo hcaphi hreturn
  have hs : c * (((J : ℝ) + 1 / 8) / c) = (J : ℝ) + 1 / 8 := by field_simp
  have hrs : r < ((J : ℝ) + 1 / 8) / c := by nlinarith
  exact successor_clear J I hc hb (hr.trans hrs) hs hbacklo hbackhi (by linarith)

/-- The successor is the cascade's computed opening, with its lap centre
derived from capture rather than supplied as a future label. -/
theorem nextOpening_bands {b c r : ℝ} (K : ℤ)
    (hb : 0 < b) (hc : 0 < c)
    (hopen : b * r = (K : ℝ) + 1 / 8)
    (hcap : MomentIterationN.inWay 8 c r) (hratio : b ≤ 3 * c) :
    r < MomentIterationN.nextOpening 8 c r ∧
      (K : ℝ) + 1 / 8 < b * MomentIterationN.nextOpening 8 c r ∧
        b * MomentIterationN.nextOpening 8 c r < (K : ℝ) + 7 / 8 := by
  obtain ⟨J, hJ⟩ := MomentIterationN.exists_near_int hcap
  have he := MomentIterationN.nextOpening_eq hc hJ
  norm_num at hJ he
  have hh := abs_lt.mp hJ
  obtain ⟨hrs, _, hlo, hhi⟩ := successor_bands K J hb hc hopen
    (by linarith [hh.1]) (by linarith [hh.2]) hratio
  rw [he]
  exact ⟨hrs, hlo, hhi⟩

/-- If every currently captured reading has disparity at least b/3, the
actual maximum-exit cascade move preserves b's current clear band. In
particular this applies whenever b is at most three times d_min. -/
theorem move_preserves_setter (S : Finset ℝ) {b r : ℝ} (K : ℤ)
    (hpos : ∀ c ∈ S, 0 < c) (hb : 0 < b)
    (hopen : b * r = (K : ℝ) + 1 / 8)
    (hratio : ∀ c ∈ S, MomentIterationN.inWay 8 c r → b ≤ 3 * c) :
    (K : ℝ) + 1 / 8 ≤ b * MomentIterationN.move 8 S r ∧
      b * MomentIterationN.move 8 S r ≤ (K : ℝ) + 7 / 8 := by
  rcases MomentIterationN.move_eq_self_or_opening (n := 8) S r with he | ⟨c, hcS, hcap, he⟩
  · rw [he, hopen]
    constructor <;> linarith
  · obtain ⟨_, hlo, hhi⟩ := nextOpening_bands K hb (hpos c hcS) hopen hcap
      (hratio c hcS hcap)
    rw [he]
    exact ⟨hlo.le, hhi.le⟩

/-- A genuine recapture by the actual cascade move identifies a currently
captured maximum-exit setter c with 3*c<b. This is an arrangement-derived
restriction, not an assertion that such recaptures can never happen. -/
theorem move_recapture_requires_small_setter (S : Finset ℝ) {b r : ℝ} (K : ℤ)
    (hpos : ∀ c ∈ S, 0 < c) (hb : 0 < b)
    (hopen : b * r = (K : ℝ) + 1 / 8)
    (hreturn : MomentIterationN.inWay 8 b (MomentIterationN.move 8 S r)) :
    ∃ c ∈ S, MomentIterationN.inWay 8 c r ∧
      MomentIterationN.move 8 S r = MomentIterationN.nextOpening 8 c r ∧ 3 * c < b := by
  rcases MomentIterationN.move_eq_self_or_opening (n := 8) S r with he | ⟨c, hcS, hcap, he⟩
  · have hclear : (8 : ℝ)⁻¹ ≤ circDist (b * r) := by
      apply TwoPinner.clear_of_band (N := K)
      · exact hopen.ge
      · linarith
    rw [he] at hreturn
    exact False.elim ((not_lt_of_ge hclear) hreturn)
  · refine ⟨c, hcS, hcap, he, ?_⟩
    by_contra hn
    obtain ⟨_, hlo, hhi⟩ := nextOpening_bands K hb (hpos c hcS) hopen hcap (le_of_not_gt hn)
    have hclear := TwoPinner.clear_of_band hlo.le hhi.le
    rw [he] at hreturn
    exact (not_lt_of_ge hclear) hreturn

end LRC.DirectHandoff
