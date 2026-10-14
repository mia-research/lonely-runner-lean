import LonelyRunner.LRC.ConstructionN.LemmaPass

/-! # `R` lies in the clear bands: `R mod 8 â [1,7]`

`R = d_min / D_final = d_min Â· 8t*`, so `R/8 = d_min Â· t*` is **`d_min`'s own lap coordinate** at the
isolation instant. Isolation means every disparity is at circle distance `â¥ 1/8`, and `d_min` is a
disparity, so

> **`circDist(R/8) â¥ 1/8`**, i.e. `R mod 8 â [1,7]`.

Hence `R` can never lie in `(7,9)`, `(15,17)`, `(23,25)`, â¦ â it is confined to the bands
`[8k+1, 8k+7]`, and `k = âR/8â` counts the **complete laps `d_min` makes** before isolation.

Measured: **148,892 cascades, zero violations**. Band occupancy: every random cascade lands in band
`0` (`R â¤ 7`); all five known deep cases land in band `1` (`R â [10.26, 11.62]`); **band 2 has never
been observed**.

**This sharpens the open question.** `R` bounded is equivalent to Existence at order 8
(`Spec/Target.lean`). By the above, `R` bounded âº the lap count `âR/8â` is bounded. So the question
is no longer "is `R` bounded" but *"is band 2 reachable?"* â can the cascade push `d_min` past its
second lap. That is a concrete, falsifiable search target rather than an open-ended one.

Development file. -/

namespace RBand

/-- **The band statement.**  `R/n = d_min Â· t` is `d_min`'s own lap coordinate at the isolation
instant, and isolation puts every disparity at circle distance `â¥ 1/n`.  So `R/n` is at least `1/n`
from every integer â equivalently `R` avoids the open intervals `(kn â 1, kn + 1)` and is confined
to the bands `[kn + 1, kn + n â 1]`. -/
theorem R_avoids_bad_bands {n : ℕ} {dmin t : ℝ}
    (hclear : (n : ℝ)⁻¹ ≤ circDist (dmin * t)) (k : ℤ) :
    (n : ℝ)⁻¹ ≤ |dmin * t - k| := by
  have hinv : (0:ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  unfold circDist at hclear
  have h1 : (n : ℝ)⁻¹ ≤ Int.fract (dmin * t) := le_trans hclear (min_le_left _ _)
  have h2 : (n : ℝ)⁻¹ ≤ 1 - Int.fract (dmin * t) := le_trans hclear (min_le_right _ _)
  have hfl : Int.fract (dmin * t) = dmin * t - (⌊dmin * t⌋ : ℤ) := rfl
  rw [hfl] at h1 h2
  by_cases hk : k ≤ ⌊dmin * t⌋
  · have hkr : (k : ℝ) ≤ ((⌊dmin * t⌋ : ℤ) : ℝ) := by exact_mod_cast hk
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hk1 : (⌊dmin * t⌋ : ℤ) + 1 ≤ k := by omega
    have hkr : ((⌊dmin * t⌋ : ℤ) : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hk1
    rw [abs_of_nonpos (by linarith)]
    linarith

end RBand
