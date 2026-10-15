import Mathlib

/-!
# Return lap and lap skips (observations formalised)

Observed exactly on all 1,188 returns in `[1,40]` (`six_return_exceptions_v1.out`): a runner `x` that left
at its lap-`P` opening `t` and is in the way at `t' = g·t` reads `(P + 1/6)·g` there, so it returns at the
integer `P'` within `1/6` of that reading; it skips a lap (`P' ≥ P + 2`) exactly when
`g > (6P + 11)/(6P + 1)`. And each move multiplies time by `(Q + 1/6)/(Q − δ)` for a setter caught at depth
`δ` below lap `Q`.
-/

namespace CascadeReturnLap

/-- The reading of `x` at `t' = g·t`, where `t = (P + 1/6)/x`. -/
theorem return_reading {x P g : ℝ} (hx : x ≠ 0) :
    x * (g * ((P + 1 / 6) / x)) = (P + 1 / 6) * g := by
  field_simp

/-- **Lap skip.** If `x` is in the way near the integer `P'` at reading `r = (P + 1/6)·g`
(`|r − P'| < 1/6`), then `P' ≥ P + 2` iff `r > P + 11/6`, i.e. `g > (6P + 11)/(6P + 1)` (`P ≥ 0`). -/
theorem lap_skip_iff {P P' : ℤ} {g : ℝ} (hP : 0 ≤ P) (hg : 0 < g)
    (hnear : |((P : ℝ) + 1 / 6) * g - P'| < 1 / 6) :
    P + 2 ≤ P' ↔ (6 * (P : ℝ) + 11) / (6 * P + 1) < g := by
  have hP' : (0 : ℝ) ≤ P := by exact_mod_cast hP
  have hden : (0 : ℝ) < 6 * P + 1 := by linarith
  rw [div_lt_iff₀ hden]
  have h := abs_lt.mp hnear
  constructor
  · intro h2
    have : ((P : ℝ) + 2) ≤ P' := by exact_mod_cast h2
    nlinarith [h.1]
  · intro h2
    have hr : (P : ℝ) + 11 / 6 < ((P : ℝ) + 1 / 6) * g := by nlinarith
    have : (P : ℝ) + 1 < P' := by linarith [h.2]
    have : P + 1 < P' := by exact_mod_cast this
    omega

/-- **Growth of one move.** A setter `d` caught at `d·t = Q − δ` moves time to `(Q + 1/6)/d`, a factor
`(Q + 1/6)/(Q − δ)`. -/
theorem move_factor {d t Q δ : ℝ} (hd : 0 < d) (ht : 0 < t) (hc : d * t = Q - δ) :
    ((Q + 1 / 6) / d) / t = (Q + 1 / 6) / (Q - δ) := by
  rw [← hc]; field_simp

end CascadeReturnLap

#print axioms CascadeReturnLap.return_reading
#print axioms CascadeReturnLap.lap_skip_iff
#print axioms CascadeReturnLap.move_factor
