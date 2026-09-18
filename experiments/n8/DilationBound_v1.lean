import LonelyRunner.LRC.ConstructionN.LemmaPass

/-! # The dilation is bounded: `λ < 9/7`

At scale `D` a blocking disparity has reading `s` with `|s − 8M| < 1`, and `move_lap` gives the next
scale `D' = D·s/(8M+1)`. So the contraction per step is

```
    λ = D/D' = (8M+1)/s,      with  8M − 1 < s < 8M + 1.
```

Hence `λ < (8M+1)/(8M−1)`, which decreases in `M`, so the largest possible value is at `M = 1`:

> **`λ < 9/7`** — `dilation_lt_nine_sevenths`

`M ≥ 1` because `d_min` never blocks at its own scale (`DminClearance.dmin_always_clear`), so no
blocker sits at `M = 0`. Measured: 45,199 cascade steps, **zero** with `λ ≥ 9/7`, maximum observed
`1.284105` against `9/7 = 1.285714`, attained at `M = 1`.

**Consequence.** The total contraction after `K` steps is `R = ∏λⱼ < (9/7)^K`, so

```
    K  >  log R / log(9/7).
```

That is a *lower* bound on depth given `R` — and there is no matching upper bound, because `λ → 1`
as `M → ∞`. Steps can be arbitrarily unproductive, which is exactly why a depth ceiling does not
follow from the step structure. Measured: `M` rises along every deep cascade (23-move: mean `M`
1.73 → 3.58 between halves, `λ` 1.148 → 1.075), so the cascade **self-slows**.

Development file. -/

namespace DilationBound

/-- The per-step contraction, given the setter's reading `s` and lap `M`. -/
noncomputable def lam (M : ℕ) (s : ℝ) : ℝ := (8 * M + 1) / s

/-- **`λ < 9/7`.**  A blocker at lap `M ≥ 1` has reading `s > 8M − 1`, so the contraction is less
than `(8M+1)/(8M−1) ≤ 9/7`. -/
theorem dilation_lt_nine_sevenths {M : ℕ} {s : ℝ} (hM : 1 ≤ M) (hs : 8 * (M:ℝ) - 1 < s) :
    lam M s < 9 / 7 := by
  have hM1 : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have hspos : 0 < s := by nlinarith
  unfold lam
  rw [div_lt_iff₀ hspos]
  nlinarith

/-- The bound is attained in the limit only at `M = 1`: for `M ≥ 2` the contraction is below
`17/15`, and the ceiling falls as `M` grows. -/
theorem dilation_lt_of_two_le {M : ℕ} {s : ℝ} (hM : 2 ≤ M) (hs : 8 * (M:ℝ) - 1 < s) :
    lam M s < 17 / 15 := by
  have hM1 : (2:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have hspos : 0 < s := by nlinarith
  unfold lam
  rw [div_lt_iff₀ hspos]
  nlinarith

end DilationBound
