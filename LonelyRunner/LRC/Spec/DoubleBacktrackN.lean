import LonelyRunner.LRC.Spec.LapDeadlineN
import LonelyRunner.LRC.Spec.PinchReflectionN

/-!
# A direct selector for a useful replacement window

Double the old time and backtrack to the latest preceding opening. The new
label is 2*q plus a single carry bit, determined at old phase 9/16. Only old
phases strictly between 7/16 and 9/16 can obstruct the doubled instant.
An exact backward allowance test decides clearance; it is not always true.
-/

namespace LRC.DoubleBacktrack

/-- The selector reads old phases; no future isolation witness is supplied. -/
theorem doubled_label {x : ℝ} (q : ℤ)
    (hl : (q : ℝ) + 1/8 ≤ x) (hu : x ≤ q + 7/8) :
    ⌊2*x - 1/8⌋ = 2*q + if 9/16 ≤ x-(q : ℝ) then 1 else 0 := by
  split_ifs with h
  · apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith
  · apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith

/-- Exactly the old middle phases can be captured when the time is doubled. -/
theorem doubled_clear_iff {x : ℝ} (q : ℤ)
    (hl : (q : ℝ) + 1/8 ≤ x) (hu : x ≤ q + 7/8) :
    (8 : ℝ)⁻¹ ≤ circDist (2*x) ↔
      x-(q : ℝ) ≤ 7/16 ∨ 9/16 ≤ x-(q : ℝ) := by
  have hc := LapDeadline.clear_iff_slack 1 (2*x)
  simp only [LapDeadline.slack, LapDeadline.lap, one_mul] at hc
  rw [hc, doubled_label q hl hu]
  split_ifs with h
  · push_cast
    constructor
    · intro _; exact Or.inr h
    · intro _; linarith
  · push_cast
    constructor
    · intro hs; left; linarith
    · rintro (hs | hs)
      · linarith
      · exact False.elim (h hs)

/-- Provided the backward shift has not crossed anyone's preceding opening,
the exact remaining condition is that it cover the required backward repair. -/
theorem backtrack_band_iff {d t h : ℝ} (q c : ℤ)
    (hd : 0 < d) (hh : 0 ≤ h)
    (hage : h ≤ (2*(d*t-(q : ℝ))-(c : ℝ)-1/8)/d) :
    ((((2*q+c : ℤ) : ℝ)+1/8 ≤ d*(2*t-h)) ∧
      d*(2*t-h) ≤ ((2*q+c : ℤ) : ℝ)+7/8) ↔
      max 0 ((2*(d*t-(q : ℝ))-(c : ℝ)-7/8)/d) ≤ h := by
  rw [max_le_iff, div_le_iff₀ hd]
  have ha := (le_div_iff₀ hd).mp hage
  push_cast
  constructor
  · rintro ⟨hl, hu⟩
    exact ⟨hh, by nlinarith⟩
  · rintro ⟨_, hu⟩
    constructor <;> nlinarith

/-- A strict upper margin in a common band gives strict pairwise slacks,
including when one or more runners set the lower endpoint. -/
theorem strict_slack {di dj t : ℝ} {qi qj : ℤ}
    (hi : 0 < di) (hj : 0 < dj)
    (hl : (qi : ℝ)+1/8 ≤ di*t) (hu : dj*t < qj+7/8) :
    0 < ((qj : ℝ)+7/8)*di - ((qi : ℝ)+1/8)*dj := by
  have h1 := mul_le_mul_of_nonneg_left hl hj.le
  have h2 := mul_lt_mul_of_pos_left hu hi
  nlinarith

/-- A replacement with strict pairwise slacks is available beyond the pinch
in ANY deformation direction, without needing period reflection. -/
theorem strict_slacks_extend (S : Finset ι) (hS : S.Nonempty)
    (d v : ι → ℝ) (q : ι → ℤ)
    (hstrict : ∀ i ∈ S, ∀ j ∈ S,
      0 < ((q j : ℝ)+7/8)*d i - ((q i : ℝ)+1/8)*d j) :
    ∃ e : ℝ, 0 < e ∧ ∀ h : ℝ, 0 ≤ h → h ≤ e → ∀ i ∈ S, ∀ j ∈ S,
      ((q i : ℝ)+1/8)*(d j+h*v j) ≤ ((q j : ℝ)+7/8)*(d i+h*v i) := by
  let C := fun p : ι × ι => ((q p.2 : ℝ)+7/8)*d p.1 - ((q p.1 : ℝ)+1/8)*d p.2
  let B := fun p : ι × ι => ((q p.2 : ℝ)+7/8)*v p.1 - ((q p.1 : ℝ)+1/8)*v p.2
  have hc : ∀ p ∈ S ×ˢ S, 0 < C p := by
    intro p hp
    exact hstrict p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2
  obtain ⟨e, he, hw⟩ := PinchReflection.affine_right (S ×ˢ S) (hS.product hS) C B
    (fun p hp => (hc p hp).le) (fun p hp hz => False.elim ((ne_of_gt (hc p hp)) hz))
  refine ⟨e, he, ?_⟩
  intro h hh heh i hi j hj
  have hw' := hw h hh heh (i,j) (Finset.mem_product.mpr ⟨hi,hj⟩)
  dsimp [C,B] at hw'
  nlinarith

noncomputable def readings (r2 r3 r4 r6 r7 : ℝ) : Fin 7 → ℝ :=
  ![1, r2, r3, r4, 15, r6, r7]

def replacement : Fin 7 → ℤ := ![0, 1, 2, 2, 3, 4, 5]

/-- The region really is an old pinched AP-label event, not an unrelated
collection of speeds with a new witness. Readings 1 and 15 pin its boundaries. -/
theorem region_old_bands (r2 r3 r4 r6 r7 : ℝ)
    (h2 : 5 ≤ r2 ∧ r2 ≤ 6) (h3 : 10 ≤ r3 ∧ r3 ≤ 11)
    (h4 : 23/2 ≤ r4 ∧ r4 ≤ 12) (h6 : 19 ≤ r6 ∧ r6 ≤ 20)
    (h7 : 43/2 ≤ r7 ∧ r7 ≤ 22) (i : Fin 7) :
    ((![0,0,1,1,1,2,2] : Fin 7 → ℤ) i : ℝ)+1/8 ≤
        readings r2 r3 r4 r6 r7 i / 8 ∧
      readings r2 r3 r4 r6 r7 i / 8 ≤
        ((![0,0,1,1,1,2,2] : Fin 7 → ℤ) i : ℝ)+7/8 := by
  fin_cases i <;> norm_num [readings] <;> constructor <;> linarith

/-- The normalized pinch ratios are linear-fractional expressions in the
target speeds. Interval bounds on these ratios become linear inequalities
after multiplying by the positive denominator d5-5*d1. -/
theorem first_pinch_ratio (a di d1 d5 : ℝ)
    (hD : 10-(15*d1-d5) ≠ 0) (hW : d5-5*d1 ≠ 0) :
    ((1-10/(10-(15*d1-d5)))*a+(10/(10-(15*d1-d5)))*di) /
      ((1-10/(10-(15*d1-d5)))+(10/(10-(15*d1-d5)))*d1) =
      (10*di-a*(15*d1-d5))/(d5-5*d1) := by
  have hnum : (1-10/(10-(15*d1-d5)))*a+(10/(10-(15*d1-d5)))*di =
      (10*di-a*(15*d1-d5))/(10-(15*d1-d5)) := by
    field_simp
    <;> ring
  have hden : (1-10/(10-(15*d1-d5)))+(10/(10-(15*d1-d5)))*d1 =
      (d5-5*d1)/(10-(15*d1-d5)) := by
    field_simp
    <;> ring
  rw [hnum, hden]
  field_simp

/-- On a broad five-parameter pinch region, the labels come directly from
the doubled reading. The old event is nearest-runner phase 1/8. -/
theorem region_labels (r2 r3 r4 r6 r7 : ℝ)
    (h2 : 5 ≤ r2 ∧ r2 ≤ 6) (h3 : 10 ≤ r3 ∧ r3 ≤ 11)
    (h4 : 23/2 ≤ r4 ∧ r4 ≤ 12) (h6 : 19 ≤ r6 ∧ r6 ≤ 20)
    (h7 : 43/2 ≤ r7 ∧ r7 ≤ 22) (i : Fin 7) :
    ⌊readings r2 r3 r4 r6 r7 i / 4 - 1/8⌋ = replacement i := by
  apply Int.floor_eq_iff.mpr
  fin_cases i <;> norm_num [readings, replacement] <;> constructor <;> linarith

/-- The far runner's fifth opening clears the entire region, with strict
upper margins. This derives clearance from speed bounds, not from a certificate. -/
theorem region_bands (r2 r3 r4 r6 r7 : ℝ)
    (h2 : 5 ≤ r2 ∧ r2 ≤ 6) (h3 : 10 ≤ r3 ∧ r3 ≤ 11)
    (h4 : 23/2 ≤ r4 ∧ r4 ≤ 12) (h6 : 19 ≤ r6 ∧ r6 ≤ 20)
    (h7 : 43/2 ≤ r7 ∧ r7 ≤ 22) (i : Fin 7) :
    (replacement i : ℝ)+1/8 ≤ readings r2 r3 r4 r6 r7 i * (41/(8*r7)) ∧
      readings r2 r3 r4 r6 r7 i * (41/(8*r7)) < replacement i+7/8 := by
  have hp : 0 < 8*r7 := by linarith [h7.1]
  rw [show readings r2 r3 r4 r6 r7 i * (41/(8*r7)) =
    (41*readings r2 r3 r4 r6 r7 i)/(8*r7) by ring]
  rw [le_div_iff₀ hp, div_lt_iff₀ hp]
  fin_cases i <;> norm_num [readings, replacement] <;> constructor <;> linarith

/-- The chosen time really is the latest preceding opening, as the rule
requires; it is not a separately guessed witness attached to the region. -/
theorem region_selected_time (r2 r3 r4 r6 r7 : ℝ)
    (h2 : 5 ≤ r2 ∧ r2 ≤ 6) (h3 : 10 ≤ r3 ∧ r3 ≤ 11)
    (h4 : 23/2 ≤ r4 ∧ r4 ≤ 12) (h6 : 19 ≤ r6 ∧ r6 ≤ 20)
    (h7 : 43/2 ≤ r7 ∧ r7 ≤ 22) :
    (Finset.univ : Finset (Fin 7)).sup' Finset.univ_nonempty
      (fun i => ((⌊readings r2 r3 r4 r6 r7 i / 4 - 1/8⌋ : ℝ)+1/8) /
        readings r2 r3 r4 r6 r7 i) = 41/(8*r7) := by
  have hd : ∀ i : Fin 7, 0 < readings r2 r3 r4 r6 r7 i := by
    intro i
    fin_cases i <;> norm_num [readings] <;> linarith
  have hlabel := region_labels r2 r3 r4 r6 r7 h2 h3 h4 h6 h7
  apply le_antisymm
  · apply (Finset.sup'_le_iff _ _).mpr
    intro i hi
    rw [hlabel i, div_le_iff₀ (hd i)]
    have := (region_bands r2 r3 r4 r6 r7 h2 h3 h4 h6 h7 i).1
    nlinarith
  · have h := Finset.le_sup'
      (fun i : Fin 7 => ((⌊readings r2 r3 r4 r6 r7 i / 4 - 1/8⌋ : ℝ)+1/8) /
        readings r2 r3 r4 r6 r7 i) (Finset.mem_univ (6 : Fin 7))
    rw [hlabel 6] at h
    have hv : ((replacement 6 : ℝ)+1/8) / readings r2 r3 r4 r6 r7 6 =
        41/(8*r7) := by
      change ((5 : ℝ)+1/8)/r7 = 41/(8*r7)
      ring
    rwa [hv] at h

/-- The first runner of the corresponding eight-runner arrangement really is
lonely at the selected time. The whole continuous pinch region is covered. -/
theorem region_lonely (r2 r3 r4 r6 r7 : ℝ)
    (h2 : 5 ≤ r2 ∧ r2 ≤ 6) (h3 : 10 ≤ r3 ∧ r3 ≤ 11)
    (h4 : 23/2 ≤ r4 ∧ r4 ≤ 12) (h6 : 19 ≤ r6 ∧ r6 ≤ 20)
    (h7 : 43/2 ≤ r7 ∧ r7 ≤ 22) :
    0 < 41/(8*r7) ∧ Arrangement.LonelyAt
      (Fin.cases 0 (readings r2 r3 r4 r6 r7)) 0 (41/(8*r7)) := by
  refine ⟨div_pos (by norm_num) (by linarith [h7.1]), ?_⟩
  intro i hi
  cases i using Fin.cases with
  | zero => exact False.elim (hi rfl)
  | succ j =>
    have h := region_bands r2 r3 r4 r6 r7 h2 h3 h4 h6 h7 j
    have hc := TwoPinner.clear_of_band h.1 h.2.le
    simpa [Arrangement.sep] using hc

end LRC.DoubleBacktrack
