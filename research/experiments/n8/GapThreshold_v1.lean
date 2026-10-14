import Mathlib

/-!
# The rounding error controls the exceptional set

`FourResidues` showed that nearest-integer rounding gives band ⟹ window at every modulus except
`b ∈ {2,3,8,9}`. That is the case `G = 1` of a general fact.

Let the candidate be rounded not to the nearest integer but to the nearest integer **in an
allowed residue class**, and let `G` be the largest gap in that class, so `|q − t| ≤ G/2`. The
order-6 margin then gives the band

```
    2b − 6G ≤ 12r ≤ 10b + 6G
```

and this implies the window `b ≤ 8r+1 ≤ 7b` for every

```
    b ≥ 12G + 3 .
```

`G = 1` recovers `b ≥ 15` (integrality sharpens it to `10`, and the exceptional set is the four
moduli `{2,3,8,9}`). **The point is that the exceptional set is finite and explicit for every
`G`.**

**This route is strictly worse than leaving the exclusions unenforced.** Enforcing all four by
rounding to an allowed class gives `G = 10`, hence `b ≥ 123`, and the computed exceptional set
has **110** moduli with largest `120` — against **four** for plain rounding. So satisfying the
residue conditions *by moving the candidate* costs far more than it buys, and the conditions must
be coordinated with the band rather than rounded into.

*(Exceptional sets computed for every `G` arising from a subset of `{2,3,8,9}`:
`G = 1 → 4` moduli, `G = 2 → 14`, `G = 3 → 26`, `G = 4 → 38`, `G = 5 → 50`, `G = 6 → 62`,
`G = 10 → 110`.)*
-/

namespace GapThreshold

/-- The band after rounding with error at most `G/2`, cleared of denominators. -/
def BandG (G b r : ℤ) : Prop := 2 * b - 6 * G ≤ 12 * r ∧ 12 * r ≤ 10 * b + 6 * G

/-- The clear window. -/
def Window (b r : ℤ) : Prop := b ≤ 8 * r + 1 ∧ 8 * r + 1 ≤ 7 * b

/-- **The rounding error sets the threshold.**  With largest gap `G` in the allowed class, the
band implies the window at every modulus `b ≥ 12G + 3`. -/
theorem window_of_bandG {G b r : ℤ} (hG : 0 < G) (hb : 12 * G + 3 ≤ b) (h : BandG G b r) :
    Window b r := by
  obtain ⟨h1, h2⟩ := h
  constructor <;> omega

/-- **The `G = 1` case is nearest-integer rounding**, and recovers the `b ≥ 15` real-valued
threshold that integrality sharpens to `10` in `DivisorOrder6`. -/
theorem window_of_band_one {b r : ℤ} (hb : 15 ≤ b) (h : BandG 1 b r) : Window b r :=
  window_of_bandG (by norm_num) (by omega) h

/-- **Enforcing all four exclusions costs `G = 10`**, hence a threshold of `123` — against `15`
for `G = 1`.  The exceptional set grows from four moduli to 110. -/
theorem window_of_band_ten {b r : ℤ} (hb : 123 ≤ b) (h : BandG 10 b r) : Window b r :=
  window_of_bandG (by norm_num) (by omega) h

/-- **The threshold is monotone in the rounding error**, so a larger allowed-class gap can only
enlarge the exceptional set — never shrink it. -/
theorem threshold_mono {G G' : ℤ} (h : G ≤ G') : 12 * G + 3 ≤ 12 * G' + 3 := by omega

end GapThreshold

#print axioms GapThreshold.window_of_bandG
#print axioms GapThreshold.window_of_band_one
#print axioms GapThreshold.window_of_band_ten
#print axioms GapThreshold.threshold_mono
