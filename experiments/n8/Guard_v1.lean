import LonelyRunner.LRC.ConstructionN.LemmaPass

/-! # The guard lemma: a reading that lands on a lower band edge blocks just below it

The AP covers `[1,7] ∪ [9,15]` because each of its eight clear points is **guarded from below**.
At a clear point `R` the guard is the reading `s` with `s·R ≡ 1 (mod 8)` — and since `(ℤ/8)ˣ` is the
Klein four-group, `s ≡ R⁻¹ ≡ R (mod 8)`. So:

```
    R =  1,  9   guard  s ≡ 1      (that is s₁ = 1 itself)
    R =  3, 11   guard  s = 3
    R =  5, 13   guard  s = 5
    R =  7, 15   guard  s ≡ 7      →  s₇ = S
```

`S` guards the **right endpoint of both regions**. Raising `S` past `7` un-guards both at once, and
the uncovered set opens as exactly two intervals

```
    [7 − 7ε/(7+ε), 7]   ∪   [15 − 15ε/(7+ε), 15],     total  22ε/(7+ε)
```

verified to ten decimal places at `ε = 10⁻², 10⁻³, 10⁻⁴` (`ap_mechanism_v1.py`). That is the
measured `(22/7)(S−7)` rate of `AP_ISOLATION_v1`, now derived rather than fitted.

`guard_blocks_below` is the step the derivation rests on: a reading sitting exactly on a lower band
edge is in the way immediately below it. -/

namespace Guard

/-- **The guard lemma.**  If reading `s > 0` has `s·R = 8k+1` — exactly the lower edge of a clear
band — then for every `δ` with `0 < δ < 1/s` the reading at `R − δ` lies strictly between `8k` and
`8k+1`, i.e. within `1` of the multiple `8k`: the runner is in the way just below `R`. -/
theorem guard_blocks_below {s R δ : ℝ} {k : ℤ} (hs : 0 < s) (hR : s * R = 8 * k + 1)
    (hδ : 0 < δ) (hδ' : δ < 1 / s) :
    8 * (k : ℝ) < s * (R - δ) ∧ s * (R - δ) < 8 * k + 1 := by
  have hsδ : s * δ < 1 := by
    rw [lt_div_iff₀ hs] at hδ'
    linarith [hδ']
  constructor
  · have : s * (R - δ) = 8 * (k : ℝ) + 1 - s * δ := by rw [mul_sub, hR]
    rw [this]; linarith
  · have : s * (R - δ) = 8 * (k : ℝ) + 1 - s * δ := by rw [mul_sub, hR]
    rw [this]
    nlinarith [mul_pos hs hδ]

/-- **The un-guarding.**  If instead the reading is `s' > s`, its value at `R` exceeds the edge:
`s'·R > 8k+1`, so it has moved *into* the clear band and no longer blocks at `R`.  With `s` the
unique guard of `R`, raising it opens a gap immediately below `R`. -/
theorem raising_unguards {s s' R : ℝ} {k : ℤ} (hR : 0 < R) (hs : s * R = 8 * k + 1) (hlt : s < s') :
    8 * (k : ℝ) + 1 < s' * R := by
  have : s * R < s' * R := by exact mul_lt_mul_of_pos_right hlt hR
  linarith [hs ▸ this]

end Guard
