import LonelyRunner.LRC.Spec.MirrorCentreN

/-!
# The two-pinner lemma: an isolated instant survives deformation at itself or at its mirror

2026-09-25.  Let disparities `d₊, d₋` pin an isolated lonely instant `t*`: `d₊·t* = N₊ + 1/8`
(on the threshold just ahead) and `d₋·t* = N₋ + 7/8` (on the threshold just behind).  They are the
subject's two circle neighbours at `t*`.  Deform them to `d₊·λ₊` and `d₋·λ₋`.

* If `λ₋ ≤ λ₊`, the opening `(N₊ + 1/8)/(d₊λ₊)` keeps both pinners clear (`pinners_clear_at_opening`).
* If `λ₊ ≤ λ₋`: for whole-number disparities the mirror `1 − t*` has the pinners on the other sides,
  `d₋(1 − t*) = M₋ + 1/8` and `d₊(1 − t*) = M₊ + 7/8`, `M = d − N − 1` (`mirror_readings`), and the
  same lemma with the roles swapped keeps both clear at `(M₋ + 1/8)/(d₋λ₋)`.

One of `λ₋ ≤ λ₊`, `λ₊ ≤ λ₋` always holds (`two_pinner`), so the pinners never both lose the
isolation.  The condition compares `λ₊` with `λ₋`, so it is scale invariant.  Each case asks only
that the ratio stay within the band's slack, a small-deformation hypothesis.  The other runners'
slack is a separate, set-specific radius (e.g. `1/85` at the arithmetic progression,
`experiments/nN/ap_local_v1.out`) and is not part of this lemma.

Evidence: the three tight configurations of `[1,28]` keep isolation under 2,000/2,000 small
deformations each at the openings of their `{1,7}` pinners (`experiments/nN/tight_local_v1.out`).
Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.TwoPinner

open LRC.MirrorCentre

/-- A reading in `[N + 1/8, N + 7/8]` is clear at `1/8`. -/
theorem clear_of_band {x : ℝ} {N : ℤ} (h1 : (N : ℝ) + 1 / 8 ≤ x) (h2 : x ≤ (N : ℝ) + 7 / 8) :
    (8 : ℝ)⁻¹ ≤ circDist x := by
  have := circDist_ge_of_window (m := N) (a := 1 / 8) h1 (by linarith) (by norm_num)
  simpa using this

/-- **At the pinned instant.**  With `λ₋ ≤ λ₊` and the ratio inside the band's slack, the opening
`(N₊ + 1/8)/(d₊λ₊)` keeps both pinners clear. -/
theorem pinners_clear_at_opening {dp dm lp lm tstar : ℝ} {Np Nm : ℤ} (hdp : 0 < dp) (hdm : 0 < dm)
    (hlp : 0 < lp) (hlm : 0 < lm) (htpos : 0 < tstar)
    (hp : dp * tstar = Np + 1 / 8) (hm : dm * tstar = Nm + 7 / 8)
    (hle : lm ≤ lp) (hslack : ((Nm : ℝ) + 1 / 8) * lp ≤ ((Nm : ℝ) + 7 / 8) * lm) :
    (8 : ℝ)⁻¹ ≤ circDist (dp * lp * (((Np : ℝ) + 1 / 8) / (dp * lp))) ∧
      (8 : ℝ)⁻¹ ≤ circDist (dm * lm * (((Np : ℝ) + 1 / 8) / (dp * lp))) := by
  have hts : ((Np : ℝ) + 1 / 8) / (dp * lp) = tstar / lp := by rw [← hp]; field_simp
  rw [hts]
  refine ⟨?_, ?_⟩
  · have : dp * lp * (tstar / lp) = (Np : ℝ) + 1 / 8 := by rw [← hp]; field_simp
    rw [this]; exact clear_of_band (N := Np) le_rfl (by linarith)
  · have hread : dm * lm * (tstar / lp) = ((Nm : ℝ) + 7 / 8) * (lm / lp) := by
      rw [← hm]; field_simp
    have hNm : (0 : ℝ) ≤ (Nm : ℝ) + 7 / 8 := by rw [← hm]; positivity
    rw [hread]
    refine clear_of_band (N := Nm) ?_ ?_
    · rw [← mul_div_assoc, le_div_iff₀ hlp]; linarith
    · have : lm / lp ≤ 1 := (div_le_one hlp).mpr hle
      nlinarith

/-- **The mirror readings.**  For whole-number disparities pinned at `t*`, the mirror `1 − t*` has
the pinners on the other sides of the threshold. -/
theorem mirror_readings {P Q : ℤ} {tstar : ℝ} {Np Nm : ℤ}
    (hp : (P : ℝ) * tstar = Np + 1 / 8) (hm : (Q : ℝ) * tstar = Nm + 7 / 8) :
    (P : ℝ) * (1 - tstar) = ((P - Np - 1 : ℤ) : ℝ) + 7 / 8 ∧
      (Q : ℝ) * (1 - tstar) = ((Q - Nm - 1 : ℤ) : ℝ) + 1 / 8 := by
  constructor
  · push_cast; linarith [hp]
  · push_cast; linarith [hm]

/-- **The two-pinner lemma.**  Whole-number pinners `P` (just ahead) and `Q` (just behind) of an
isolated instant `0 < t* < 1`, deformed by `λ₊, λ₋ > 0` within the bands' slack.  Then one of the
two named openings keeps both pinners clear: `(N₊ + 1/8)/(Pλ₊)` when `λ₋ ≤ λ₊`, and the mirror
opening `(M₋ + 1/8)/(Qλ₋)`, `M₋ = Q − N₋ − 1`, when `λ₊ ≤ λ₋`. -/
theorem two_pinner {P Q : ℤ} {tstar lp lm : ℝ} {Np Nm : ℤ} (hP : 0 < (P : ℝ)) (hQ : 0 < (Q : ℝ))
    (hlp : 0 < lp) (hlm : 0 < lm) (ht0 : 0 < tstar) (ht1 : tstar < 1)
    (hp : (P : ℝ) * tstar = Np + 1 / 8) (hm : (Q : ℝ) * tstar = Nm + 7 / 8)
    (hslack1 : ((Nm : ℝ) + 1 / 8) * lp ≤ ((Nm : ℝ) + 7 / 8) * lm)
    (hslack2 : (((P - Np - 1 : ℤ) : ℝ) + 1 / 8) * lm ≤ (((P - Np - 1 : ℤ) : ℝ) + 7 / 8) * lp) :
    (lm ≤ lp ∧ (8 : ℝ)⁻¹ ≤ circDist (P * lp * (((Np : ℝ) + 1 / 8) / (P * lp))) ∧
        (8 : ℝ)⁻¹ ≤ circDist (Q * lm * (((Np : ℝ) + 1 / 8) / (P * lp)))) ∨
      (lp ≤ lm ∧ (8 : ℝ)⁻¹ ≤ circDist (Q * lm * ((((Q - Nm - 1 : ℤ) : ℝ) + 1 / 8) / (Q * lm))) ∧
        (8 : ℝ)⁻¹ ≤ circDist (P * lp * ((((Q - Nm - 1 : ℤ) : ℝ) + 1 / 8) / (Q * lm)))) := by
  rcases le_total lm lp with h | h
  · exact Or.inl ⟨h, pinners_clear_at_opening hP hQ hlp hlm ht0 hp hm h hslack1⟩
  · obtain ⟨hpm, hqm⟩ := mirror_readings hp hm
    exact Or.inr ⟨h, pinners_clear_at_opening hQ hP hlm hlp (by linarith) hqm hpm h hslack2⟩

end LRC.TwoPinner
