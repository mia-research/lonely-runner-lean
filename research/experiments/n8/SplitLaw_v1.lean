import LonelyRunner.LRC.ConstructionN.LemmaPass

/-! # The split law, proved

`PAIR_STRUCTURE_v2` proved the **symmetric** half — `blocked(α') = blocked(8−α')`, by an involution —
and left the **antisymmetric** half owed: that `{1,7}` and `{3,5}` differ by exactly `±2` when
`b ≡ 2,3,6,7 (mod 8)` and agree otherwise, with the favoured pair flipping under `b ↦ b+4`.

`Rescale.blocker_class` supplies the missing mechanism. Clearance at modulus `b` for a reading of
class `α` is a band on `t`:

```
    clear  ⟺  t ∈ [ ⌈(b − α)/8⌉ , ⌊(7b − α)/8⌋ ]
```

Writing `b = 8j + r`, the endpoints **separate**:

```
    ⌈(b − α)/8⌉  =  j + ⌈(r − α)/8⌉ ,        ⌊(7b − α)/8⌋  =  7j + ⌊(7r − α)/8⌋
```

and the `j` parts do not depend on `α`. So the blocked count is `2j + r − ⌊(7r−α)/8⌋ + ⌈(r−α)/8⌉ − 1`,
and **all of the `α`-dependence sits in a function of `r` and `α` alone** — 32 integers. The split is
therefore a finite check, and that is what closes it.

Checked against direct enumeration first: 1,592 cases, `b < 400`, 0 mismatches. -/

namespace SplitLaw

/-- The blocked count at modulus `b` for residue class `α`, in the form the band gives it. -/
def blocked (al b : ℤ) : ℤ := b - ((7 * b - al) / 8 - (b - al + 7) / 8 + 1)

/-- **The endpoints separate.**  For `b = 8j + r` the lower edge is `j` plus a term in `r` and `α`
only. -/
theorem lo_split (j r al : ℤ) : (8 * j + r - al + 7) / 8 = j + (r - al + 7) / 8 := by
  have : 8 * j + r - al + 7 = (r - al + 7) + 8 * j := by ring
  rw [this, Int.add_mul_ediv_left _ _ (by norm_num : (8:ℤ) ≠ 0)]
  omega

/-- **And so does the upper edge**, with `7j`. -/
theorem hi_split (j r al : ℤ) : (7 * (8 * j + r) - al) / 8 = 7 * j + (7 * r - al) / 8 := by
  have : 7 * (8 * j + r) - al = (7 * r - al) + 8 * (7 * j) := by ring
  rw [this, Int.add_mul_ediv_left _ _ (by norm_num : (8:ℤ) ≠ 0)]
  omega

/-- **The `α`-dependence is a function of `r` alone.**  The blocked count splits as a part linear in
`j` and `r`, identical for every class, plus a correction depending only on `r` and `α`. -/
theorem blocked_split (j r al : ℤ) :
    blocked al (8 * j + r) = 2 * j + r - (7 * r - al) / 8 + (r - al + 7) / 8 - 1 := by
  unfold blocked
  rw [hi_split, lo_split]
  ring

/-- **The split law.**  For `b = 8j + r`, the difference `(blocked 1 + blocked 7) − (blocked 3 +
blocked 5)` depends only on `r`, and is `+2` at `r = 2,3`, `−2` at `r = 6,7`, and `0` otherwise.
Everything in `j` cancels. -/
theorem split_law (j r : ℤ) (h0 : 0 ≤ r) (h7 : r ≤ 7) :
    (blocked 1 (8 * j + r) + blocked 7 (8 * j + r))
      - (blocked 3 (8 * j + r) + blocked 5 (8 * j + r))
    = if r = 2 ∨ r = 3 then 2 else if r = 6 ∨ r = 7 then -2 else 0 := by
  rw [blocked_split, blocked_split, blocked_split, blocked_split]
  interval_cases r <;> simp <;> omega

end SplitLaw
