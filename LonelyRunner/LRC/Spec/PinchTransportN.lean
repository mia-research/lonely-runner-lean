import LonelyRunner.LRC.Spec.WindowPinchN

/-!
# Quantitative forward transport after a pinch

The remaining phase of a captured runner, not just its residue class, determines
the next exit. A factor-three disparity bound preserves a previous setter's
clear band. Runners captured around the SAME positive lap integer are close
enough in disparity that their slowest exit clears the whole group.

"Same lap" here retains the integer winding label; it does not mean only the
same residue modulo eight. These are local transport theorems, not global
termination for groups with different lap labels.
-/

namespace LRC.PinchTransport

open MomentIterationN

/-- A captured runner has less than a quarter lap left before its next exit. -/
theorem exit_shift_bounds {b t : ℝ} {K : ℤ} (hb : 0 < b)
    (hcap : |b * t - K| < (8 : ℝ)⁻¹) :
    0 < nextOpening 8 b t - t ∧ b * (nextOpening 8 b t - t) < 1 / 4 := by
  have he : b * nextOpening 8 b t = (K : ℝ) + 1 / 8 := by
    rw [nextOpening_eq hb hcap]
    norm_num
    field_simp
  obtain ⟨hl, hu⟩ := abs_lt.mp hcap
  norm_num at hl hu
  constructor
  · have hp : 0 < b * (nextOpening 8 b t - t) := by nlinarith
    exact pos_of_mul_pos_right hp hb.le
  · nlinarith

/-- The full phase, retained as a real number, gives the exact relocation of
EVERY reading. This identity includes all whole laps. -/
theorem reading_shift {b d t : ℝ} {K : ℤ} (hb : 0 < b)
    (hcap : |b * t - K| < (8 : ℝ)⁻¹) :
    d * nextOpening 8 b t = d * t +
      (d / b) * ((K : ℝ) + 1 / 8 - b * t) := by
  rw [nextOpening_eq hb hcap]
  norm_num
  field_simp
  ring

/-- A runner with at most three times the setter's disparity moves less than
three quarters of a lap during this exit. -/
theorem displacement_lt_three_quarters {a b t : ℝ} {K : ℤ}
    (hb : 0 < b) (hab : a ≤ 3 * b)
    (hcap : |b * t - K| < (8 : ℝ)⁻¹) :
    a * (nextOpening 8 b t - t) < 3 / 4 := by
  obtain ⟨hshift, hbound⟩ := exit_shift_bounds hb hcap
  have hmul := mul_le_mul_of_nonneg_right hab hshift.le
  nlinarith

/-- Handoff from an old setter `a` to a captured `b`: if a<=3b, the old
setter remains strictly inside its original clear band after b's exit.
This conclusion is derived from capture and the disparity ratio, not assumed. -/
theorem old_setter_band {a b t : ℝ} {P K : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≤ 3 * b)
    (hstart : a * t = (P : ℝ) + 1 / 8)
    (hcap : |b * t - K| < (8 : ℝ)⁻¹) :
    (P : ℝ) + 1 / 8 < a * nextOpening 8 b t ∧
      a * nextOpening 8 b t < P + 7 / 8 := by
  have hp := mul_pos ha (exit_shift_bounds hb hcap).1
  have hu := displacement_lt_three_quarters hb hab hcap
  constructor <;> nlinarith

/-- Under that ratio bound both participants are clear at the new exit.
Other runners may still block it; they have not been discarded. -/
theorem handoff_pair_clear {a b t : ℝ} {P K : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≤ 3 * b)
    (hstart : a * t = (P : ℝ) + 1 / 8)
    (hcap : |b * t - K| < (8 : ℝ)⁻¹) :
    (8 : ℝ)⁻¹ ≤ circDist (a * nextOpening 8 b t) ∧
      (8 : ℝ)⁻¹ ≤ circDist (b * nextOpening 8 b t) := by
  have h := old_setter_band ha hb hab hstart hcap
  exact ⟨TwoPinner.clear_of_band h.1.le h.2.le, (circDist_at_nextOpening hb).ge⟩

/-- Same positive blocking lap forces a strict factor-three bound. There may
be any number of readings in this lap; no two-runner restriction is assumed. -/
theorem same_lap_ratio {d m t : ℝ} {K : ℤ}
    (hm : 0 < m) (hK : 1 ≤ K)
    (hmcap : |m * t - K| < (8 : ℝ)⁻¹)
    (hdcap : |d * t - K| < (8 : ℝ)⁻¹) : d < 3 * m := by
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  obtain ⟨hml, hmu⟩ := abs_lt.mp hmcap
  obtain ⟨hdl, hdu⟩ := abs_lt.mp hdcap
  norm_num at hml hmu hdl hdu
  have ht : 0 < t := pos_of_mul_pos_right (by linarith : 0 < m * t) hm.le
  apply (mul_lt_mul_iff_left₀ ht).mp
  nlinarith

/-- The minimum-disparity exit clears every member of one positive-lap
capture group. This is a clearance theorem, not just a bound on an assumed
clearance certificate. -/
theorem same_lap_group_band {d m t : ℝ} {K : ℤ}
    (hm : 0 < m) (hmd : m ≤ d) (hK : 1 ≤ K)
    (hmcap : |m * t - K| < (8 : ℝ)⁻¹)
    (hdcap : |d * t - K| < (8 : ℝ)⁻¹) :
    (K : ℝ) + 1 / 8 ≤ d * nextOpening 8 m t ∧
      d * nextOpening 8 m t < K + 7 / 8 := by
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have he : m * nextOpening 8 m t = (K : ℝ) + 1 / 8 := by
    rw [nextOpening_eq hm hmcap]
    norm_num
    field_simp
  have hT : 0 < nextOpening 8 m t :=
    pos_of_mul_pos_right (by linarith : 0 < m * nextOpening 8 m t) hm.le
  have hl := mul_le_mul_of_nonneg_right hmd hT.le
  have hratio := same_lap_ratio hm hK hmcap hdcap
  have hshift := displacement_lt_three_quarters hm hratio.le hmcap
  have hu := (abs_lt.mp hdcap).2
  norm_num at hu
  constructor <;> nlinarith

/-- If ALL current readings are captured in one positive lap, the cascade's
actual maximum-exit move is already lonely. The minimum is selected from the
finite arrangement, with no assumed terminating history. -/
theorem same_lap_move_lonely (ds : Finset ℝ) (hne : ds.Nonempty)
    {t : ℝ} {K : ℤ} (hK : 1 ≤ K) (hpos : ∀ d ∈ ds, 0 < d)
    (hcap : ∀ d ∈ ds, |d * t - K| < (8 : ℝ)⁻¹) :
    t < move 8 ds t ∧ Lonely 8 ds (move 8 ds t) := by
  classical
  obtain ⟨m, hm, hmin⟩ := Finset.exists_mem_eq_inf' hne id
  simp only [id_eq] at hmin
  have hmd : ∀ d ∈ ds, m ≤ d := by
    intro d hd
    rw [← hmin]
    exact Finset.inf'_le id hd
  have hmpos := hpos m hm
  have hmc := hcap m hm
  have hmw : inWay 8 m t :=
    lt_of_le_of_lt (ConstructionN.circDist_le_abs_sub_int _ K) hmc
  have hlonely : Lonely 8 ds (nextOpening 8 m t) := by
    intro d hd
    have h := same_lap_group_band hmpos (hmd d hd) hK hmc (hcap d hd)
    exact TwoPinner.clear_of_band h.1 h.2.le
  have ht := lt_nextOpening hmpos hmw
  have he : move 8 ds t = nextOpening 8 m t := by
    apply le_antisymm
    · exact move_le_of_lonely hpos hlonely ht.le
    · exact nextOpening_le_move hm hmw
  rw [he]
  exact ⟨ht, hlonely⟩

/-- Distinct disparities cannot remain captured around the same unwrapped lap
integer past the reciprocal-gap time. This does NOT exclude captures with
different lap labels, even when their circle residues coincide. -/
theorem same_lap_separation_time {a b t : ℝ} {K : ℤ} (hab : b < a)
    (ha : |a * t - K| < (8 : ℝ)⁻¹)
    (hb : |b * t - K| < (8 : ℝ)⁻¹) :
    t < 1 / (4 * (a - b)) := by
  have hu := (abs_lt.mp ha).2
  have hl := (abs_lt.mp hb).1
  norm_num at hu hl
  rw [lt_div_iff₀ (by linarith : 0 < 4 * (a - b))]
  nlinarith

/-- Reuse a previously calculated clear band's lower endpoint. Its survival
at the new opening is EXACTLY one upper-deadline comparison, linear in d,b
for fixed integer laps. No recomputation of fractional parts is required. -/
theorem retained_band_iff {d b t : ℝ} {M K : ℤ}
    (hd : 0 ≤ d) (hb : 0 < b)
    (hcap : |b * t - K| < (8 : ℝ)⁻¹)
    (hlo : (M : ℝ) + 1 / 8 ≤ d * t) :
    ((M : ℝ) + 1 / 8 ≤ d * nextOpening 8 b t ∧
      d * nextOpening 8 b t ≤ M + 7 / 8) ↔
    d * ((K : ℝ) + 1 / 8) ≤ b * ((M : ℝ) + 7 / 8) := by
  have hshift := mul_nonneg hd (exit_shift_bounds hb hcap).1.le
  have hl : (M : ℝ) + 1 / 8 ≤ d * nextOpening 8 b t := by nlinarith
  have he : d * nextOpening 8 b t = d * ((K : ℝ) + 1 / 8) / b := by
    rw [nextOpening_eq hb hcap]
    norm_num
    ring
  rw [and_iff_right hl, he, div_le_iff₀ hb]
  constructor <;> intro h <;> nlinarith

/-- Full transport: the close same-lap group separates, while all other
readings reuse their computed bands. If the group's exit precedes their
deadlines, it is both lonely and exactly the next cascade move. -/
theorem group_exit_lonely_of_deadlines (ds C : Finset ℝ)
    {m t : ℝ} {K : ℤ} (q : ℝ → ℤ)
    (hsub : C ⊆ ds) (hm : m ∈ C) (hK : 1 ≤ K)
    (hpos : ∀ d ∈ ds, 0 < d) (hmin : ∀ d ∈ C, m ≤ d)
    (hcap : ∀ d ∈ C, |d * t - K| < (8 : ℝ)⁻¹)
    (hstart : ∀ d ∈ ds, d ∉ C →
      (q d : ℝ) + 1 / 8 ≤ d * t ∧ d * t ≤ q d + 7 / 8)
    (hdeadline : ∀ d ∈ ds, d ∉ C →
      d * ((K : ℝ) + 1 / 8) ≤ m * ((q d : ℝ) + 7 / 8)) :
    move 8 ds t = nextOpening 8 m t ∧
      t < nextOpening 8 m t ∧ Lonely 8 ds (nextOpening 8 m t) := by
  have hmS := hsub hm
  have hmpos := hpos m hmS
  have hmcap := hcap m hm
  have hmw : inWay 8 m t :=
    lt_of_le_of_lt (ConstructionN.circDist_le_abs_sub_int _ K) hmcap
  have ht := lt_nextOpening hmpos hmw
  have hlonely : Lonely 8 ds (nextOpening 8 m t) := by
    intro d hd
    by_cases hc : d ∈ C
    · have h := same_lap_group_band hmpos (hmin d hc) hK hmcap (hcap d hc)
      exact TwoPinner.clear_of_band h.1 h.2.le
    · have h := (retained_band_iff (hpos d hd).le hmpos hmcap
        (hstart d hd hc).1).mpr (hdeadline d hd hc)
      exact TwoPinner.clear_of_band h.1 h.2
  refine ⟨le_antisymm (move_le_of_lonely hpos hlonely ht.le)
    (nextOpening_le_move hmS hmw), ht, hlonely⟩

end LRC.PinchTransport
