import LonelyRunner.LRC.ConstructionN.LemmaPass

/-! # The gap rule: for integer readings, every gap is `N/(s·s')` with `N` a positive integer

This is the mechanism the search was implicitly exploiting, made explicit — and it generalises off
order 8 without change.

A bad interval of reading `s` at level `m` ends at `(nm+1)/s`; the next one, of reading `s'` at level
`m'`, begins at `(nm'−1)/s'`. If there is a gap between them its width is

```
        (nm'−1)/s' − (nm+1)/s  =  [ s(nm'−1) − s'(nm+1) ] / (s·s')
```

and for **integer** readings the numerator is an **integer**. A gap means it is positive, hence at
least `1`. So:

> **every gap has width exactly `N/(s·s')` with `N ≥ 1` — in particular at least `1/(s·s')`.**

Verified on 126,258 gaps across 4,000 profiles: width `= N/(s·s')` in every case, `N ≥ 1` in every
case, zero violations. The Branch-B minimiser `[3,4,5,7,11,24]` has all four of its gaps at `N = 1`
— `1/168, 1/44, 1/44, 1/168`, summing to `53/924`, exactly half the joint `53/462`.

**Two consequences.**

* *Quantitative.* A gap, once present, cannot be arbitrarily small for fixed readings: it is at least
  `1/(s·s')`. The minimum over profiles with readings `≤ H` therefore decays like `H⁻²` — measured, a
  gap of `1/3080` at readings `55, 56`. So Branch B has **no uniform floor**, and the `53/462`
  recorded at readings `≤ 40` is a statement about that range only.
* *Structural.* Covering with no gap at a junction is exactly the **integer** inequality
  `s(nm'−1) ≤ s'(nm+1)`. So for integer readings the whole covering condition is a system of linear
  inequalities **over the integers**, not the reals — rigid in a way the real relaxation is not. -/

namespace GapRule

/-- **The gap width, exactly.**  Between the right endpoint `(nm+1)/s` of one bad interval and the
left endpoint `(nm'−1)/s'` of the next. -/
theorem gap_eq {n s s' m m' : ℤ} (hs : 0 < s) (hs' : 0 < s') :
    ((n * m' - 1 : ℤ) : ℚ) / s' - ((n * m + 1 : ℤ) : ℚ) / s
      = ((s * (n * m' - 1) - s' * (n * m + 1) : ℤ) : ℚ) / (s * s') := by
  have hs0 : ((s : ℚ)) ≠ 0 := by exact_mod_cast hs.ne'
  have hs'0 : ((s' : ℚ)) ≠ 0 := by exact_mod_cast hs'.ne'
  field_simp
  push_cast
  ring

/-- **Integrality forces the floor.**  If the numerator is positive it is at least `1`, so the gap
is at least `1/(s·s')`. -/
theorem gap_ge {n s s' m m' : ℤ} (hs : 0 < s) (hs' : 0 < s')
    (hpos : 0 < s * (n * m' - 1) - s' * (n * m + 1)) :
    (1 : ℚ) / (s * s')
      ≤ ((n * m' - 1 : ℤ) : ℚ) / s' - ((n * m + 1 : ℤ) : ℚ) / s := by
  rw [gap_eq hs hs']
  have hden : (0 : ℚ) < (s : ℚ) * s' := by
    have : (0:ℚ) < (s:ℚ) := by exact_mod_cast hs
    have : (0:ℚ) < (s':ℚ) := by exact_mod_cast hs'
    positivity
  rw [div_le_div_iff_of_pos_right hden]
  exact_mod_cast hpos

/-- **No gap is an integer inequality.**  The two intervals meet or overlap exactly when
`s(nm'−1) ≤ s'(nm+1)` — a linear inequality over `ℤ`, not over `ℝ`. -/
theorem no_gap_iff {n s s' m m' : ℤ} (hs : 0 < s) (hs' : 0 < s') :
    ((n * m' - 1 : ℤ) : ℚ) / s' ≤ ((n * m + 1 : ℤ) : ℚ) / s
      ↔ s * (n * m' - 1) ≤ s' * (n * m + 1) := by
  have h1 : (0:ℚ) < (s:ℚ) := by exact_mod_cast hs
  have h2 : (0:ℚ) < (s':ℚ) := by exact_mod_cast hs'
  rw [div_le_div_iff₀ h2 h1]
  constructor
  · intro h
    have : ((n * m' - 1 : ℤ) : ℚ) * (s : ℚ) ≤ ((n * m + 1 : ℤ) : ℚ) * (s' : ℚ) := h
    have h' : (n * m' - 1) * s ≤ (n * m + 1) * s' := by exact_mod_cast this
    linarith [h']
  · intro h
    have h' : (n * m' - 1) * s ≤ (n * m + 1) * s' := by linarith [h]
    exact_mod_cast h'

end GapRule
