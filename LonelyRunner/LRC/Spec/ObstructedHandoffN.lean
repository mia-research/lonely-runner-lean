import LonelyRunner.LRC.Spec.DirectHandoffN
import LonelyRunner.LRC.Spec.HandoffDriftN

/-!
# A third obstruction and protection of earlier setters

At c's opening, all possible obstructing readings d are characterised by
exact homogeneous inequalities, including their actual capture lap L.
Their forced exit is (L+1/8)/d. Two capture displacements, not merely the
last one, must be carried to protect an older setter b.

The cumulative sufficient test b/c+b/d<=3 protects b; c<=3d protects c.
These are genuine restrictions, not claimed consequences of arbitrary speed
ordering. A finite fragment can satisfy both adjacent pair tests and still
recapture b. Nothing here asserts global termination or isolation of all seven.
-/

namespace LRC.ObstructedHandoff

/-- Which readings obstruct this opening: the capture lap is existentially
derived, not an assumed successful replacement label. Boundary equality is clear. -/
theorem obstructs_opening_iff {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (J : ℤ) :
    MomentIterationN.inWay 8 d (((J : ℝ) + 1 / 8) / c) ↔
      ∃ L : ℤ, (8 * (L : ℝ) - 1) * c < (8 * (J : ℝ) + 1) * d ∧
        (8 * (J : ℝ) + 1) * d < (8 * (L : ℝ) + 1) * c := by
  constructor
  · intro h
    obtain ⟨L, hL⟩ := MomentIterationN.exists_near_int h
    exact ⟨L, by simpa using (HandoffDrift.captured_iff_linear hc J L).mp hL⟩
  · rintro ⟨L, hL⟩
    have habs := (HandoffDrift.captured_iff_linear hc J L).mpr hL
    norm_num at habs
    have hh := abs_lt.mp habs
    apply (MomentIterationN.inWay_iff_zone (n := 8) hd).mpr
    refine ⟨L, ?_, ?_⟩
    · unfold MomentIterationN.zoneLo
      rw [div_lt_iff₀ hd]
      norm_num
      linarith [hh.1]
    · unfold MomentIterationN.zoneHi
      rw [lt_div_iff₀ hd]
      norm_num
      linarith [hh.2]

/-- A captured reading's own next opening advances by strictly less than
its capture width. This does not bound a different reading's later opening. -/
theorem exit_displacement {d r s : ℝ} (L : ℤ) (hd : 0 < d)
    (hlo : (L : ℝ) - 1 / 8 < d * r)
    (hhi : d * r < (L : ℝ) + 1 / 8)
    (hs : d * s = (L : ℝ) + 1 / 8) :
    0 < s - r ∧ s - r < 1 / (4 * d) := by
  constructor
  · nlinarith
  · rw [lt_div_iff₀ (by positivity : 0 < 4 * d)]
    nlinarith

/-- Carry both displacements. This derives the old setter's surviving band
without assuming its clearance at the new candidate. -/
theorem two_exits_protect_first {b c d r s u : ℝ} (K J L : ℤ)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hr : b * r = (K : ℝ) + 1 / 8)
    (hc0 : (J : ℝ) - 1 / 8 < c * r) (hc1 : c * r < (J : ℝ) + 1 / 8)
    (hs : c * s = (J : ℝ) + 1 / 8)
    (hd0 : (L : ℝ) - 1 / 8 < d * s) (hd1 : d * s < (L : ℝ) + 1 / 8)
    (hu : d * u = (L : ℝ) + 1 / 8)
    (hratio : b / c + b / d ≤ 3) :
    (K : ℝ) + 1 / 8 < b * u ∧ b * u < (K : ℝ) + 7 / 8 := by
  obtain ⟨hstep1, hwidth1⟩ := exit_displacement J hc hc0 hc1 hs
  obtain ⟨hstep2, hwidth2⟩ := exit_displacement L hd hd0 hd1 hu
  have htotal : b * (u - r) < 3 / 4 := calc
    b * (u - r) = b * (s - r) + b * (u - s) := by ring
    _ < b * (1 / (4 * c)) + b * (1 / (4 * d)) :=
      add_lt_add (mul_lt_mul_of_pos_left hwidth1 hb) (mul_lt_mul_of_pos_left hwidth2 hb)
    _ = (b / c + b / d) / 4 := by ring
    _ ≤ 3 / 4 := by linarith
  have hpositive : 0 < b * (u - r) := mul_pos hb (by linarith)
  constructor <;> nlinarith

/-- A genuine return of the older setter forces failure of the cumulative
ratio test, even when both immediately adjacent pair tests succeed. -/
theorem older_recapture_requires_ratio {b c d r s u : ℝ} (K J L : ℤ)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hr : b * r = (K : ℝ) + 1 / 8)
    (hc0 : (J : ℝ) - 1 / 8 < c * r) (hc1 : c * r < (J : ℝ) + 1 / 8)
    (hs : c * s = (J : ℝ) + 1 / 8)
    (hd0 : (L : ℝ) - 1 / 8 < d * s) (hd1 : d * s < (L : ℝ) + 1 / 8)
    (hu : d * u = (L : ℝ) + 1 / 8)
    (hreturn : MomentIterationN.inWay 8 b u) : 3 < b / c + b / d := by
  by_contra hn
  obtain ⟨hlo, hhi⟩ := two_exits_protect_first K J L hb hc hd hr hc0 hc1 hs hd0 hd1 hu
    (le_of_not_gt hn)
  exact (not_lt_of_ge (TwoPinner.clear_of_band hlo.le hhi.le)) hreturn

/-- The forced third opening clears all three selected readings under two
speed tests. There is no assertion about the remaining readings. -/
theorem third_opening_clear {b c d r s : ℝ} (K J L : ℤ)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hrpos : 0 < r)
    (hr : b * r = (K : ℝ) + 1 / 8)
    (hc0 : (J : ℝ) - 1 / 8 < c * r) (hc1 : c * r < (J : ℝ) + 1 / 8)
    (hs : c * s = (J : ℝ) + 1 / 8)
    (hd0 : (L : ℝ) - 1 / 8 < d * s) (hd1 : d * s < (L : ℝ) + 1 / 8)
    (hratio : b / c + b / d ≤ 3) (hcd : c ≤ 3 * d) :
    let u := ((L : ℝ) + 1 / 8) / d
    0 < u ∧ (8 : ℝ)⁻¹ ≤ circDist (b * u) ∧
      (8 : ℝ)⁻¹ ≤ circDist (c * u) ∧ (8 : ℝ)⁻¹ ≤ circDist (d * u) := by
  have hu : d * (((L : ℝ) + 1 / 8) / d) = (L : ℝ) + 1 / 8 := by field_simp
  obtain ⟨hlo, hhi⟩ := two_exits_protect_first K J L hb hc hd hr hc0 hc1 hs hd0 hd1 hu hratio
  have hspos : 0 < s := by
    have := (exit_displacement J hc hc0 hc1 hs).1
    linarith
  obtain ⟨hupos, hclearc, hcleard⟩ := DirectHandoff.successor_clear J L hc hd hspos hs hd0 hd1 hcd
  exact ⟨hupos, TwoPinner.clear_of_band hlo.le hhi.le, hclearc, hcleard⟩

end LRC.ObstructedHandoff
