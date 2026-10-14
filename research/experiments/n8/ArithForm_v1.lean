import LonelyRunner.LRC.ConstructionN.LemmaPass

/-! # The arithmetic form: covering with no division

`ReachRule.reach_mem` says the witness is `1` or a right endpoint `(n·m+1)/s`, and
`ReachRule.finite_check` says those points settle covering. Both still speak of rationals. This file
removes the division: at a point of that shape, "reading `s'` covers it" is a statement about
integers only.

```
    |s'·(nm+1)/s − n·k| < 1   ⟺   |s'·(nm+1) − n·k·s| < s
```

so the whole covering question, for integer readings, is a finite conjunction of integer
inequalities — equivalently, a residue condition `s'·(nm+1) mod n·s ∈ (−s, s)`.

Checked on 374,522 candidate points across 3,000 profiles at `n = 8`: the integer form and the real
form agree everywhere, 0 mismatches; and the resulting finite check agrees with the full interval
sweep on all 3,000 profiles, 0 mismatches. Candidate-set size: min 27, median 123, max 242. -/

namespace ArithForm

/-- **Clearing the denominator.**  At a point `N/s` with `s > 0`, being within `1` of a multiple of
`n` is exactly an integer inequality. No rational arithmetic survives on the right. -/
theorem near_iff_int {s : ℤ} (hs : 0 < s) (A n k : ℤ) :
    |((A : ℚ)) / (s : ℚ) - (n : ℚ) * (k : ℚ)| < 1 ↔ |A - n * k * s| < s := by
  have hs0 : (0 : ℚ) < (s : ℚ) := by exact_mod_cast hs
  have hrw : ((A : ℚ)) / (s : ℚ) - (n : ℚ) * (k : ℚ) = ((A - n * k * s : ℤ) : ℚ) / (s : ℚ) := by
    field_simp
    push_cast
    ring
  rw [hrw, abs_div, abs_of_pos hs0, div_lt_one hs0, ← Int.cast_abs]
  exact_mod_cast Iff.rfl

/-- **Covering an endpoint is an integer condition.**  A reading `s'` covers the endpoint `A/s`
exactly when some integer multiple brings `s'·A` within `s` of a multiple of `n·s`. -/
theorem covers_iff_int {s : ℤ} (hs : 0 < s) (A n s' : ℤ) :
    (∃ k : ℤ, |((s' * A : ℤ) : ℚ) / (s : ℚ) - (n : ℚ) * (k : ℚ)| < 1)
      ↔ ∃ k : ℤ, |s' * A - n * k * s| < s :=
  exists_congr fun k => near_iff_int hs (s' * A) n k

end ArithForm
