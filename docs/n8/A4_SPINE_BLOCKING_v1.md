# A4 — which relocations put every spine instant in the way, at one scale

2026-09-15. From `FRAMEWORK_BOUNDARY_AUDIT_v3.md` action A4. Script `experiments/n8/a4_spine_blocking_v1.py` (output `.out`),
exact rationals.

## 1. Setting

At a scale `D`, read from the subject (slot 0, deviation 0), runner `j` has reading `s_j = a_j + e_j`, with `a_j` a whole slot and
`e_j ∈ [0, 1)`. At the spine instant `u = r/8` of that scale (`r` odd) it sits at `r·a_j + r·e_j` eighths. It is in the way iff
that is within 1 of a multiple of 8 (strict; `position_in_eighths`, `clear_iff`, real-valued).

For `r ∈ {1, 3, 5, 7}`, put `c = r·a mod 8`. Then `c + r·e ∈ [0, 14)`, so

    in the way at spine r   ⟺   c + r·e < 1   or   7 < c + r·e < 9.

**The pattern depends only on `a mod 8` and `e`.** It is the same at every scale: the ideal does not depend on the scale.
`[PROVED — arithmetic]`

## 2. The table  `[PROVED — arithmetic; checked 95,776 spine instants from speeds, 0 disagreements]`

Spines each runner is in the way at, by slot residue and deviation. Pieces are open intervals; at every breakpoint the runner is
clear at the spine whose edge it is, by boundary discipline.

| `a mod 8` | `e` pieces and the spines in the way |
|---|---|
| 0 | `[0, 1/7)`: 1,3,5,7 · `(1/7, 1/5)`: 1,3,5 · `(1/5, 1/3)`: 1,3 · `(1/3, 1)`: 1 |
| 1 | `(0, 2/7)`: 7 · `(2/7, 2/5)`: — · `(2/5, 4/5)`: 5 · `(4/5, 1)`: — · at `e = 0`: — |
| 2 | `(0, 1/7)`: — · `(1/7, 1/3)`: 7 · `(1/3, 3/7)`: 3,7 · `(3/7, 1)`: 3 |
| 3 | `(0, 2/7)`: 5 · `(2/7, 2/5)`: 5,7 · `(2/5, 4/7)`: 7 · `(4/7, 1)`: — |
| 4 | `(0, 3/7)`: — · `(3/7, 3/5)`: 7 · `(3/5, 5/7)`: 5,7 · `(5/7, 1)`: 5 |
| 5 | `(0, 4/7)`: 3 · `(4/7, 2/3)`: 3,7 · `(2/3, 6/7)`: 7 · `(6/7, 1)`: — |
| 6 | `(0, 1/5)`: — · `(1/5, 3/5)`: 5 · `(3/5, 5/7)`: — · `(5/7, 1)`: 7 |
| 7 | `(0, 2/3)`: 1 · `(2/3, 4/5)`: 1,3 · `(4/5, 6/7)`: 1,3,5 · `(6/7, 1)`: 1,3,5,7 · at `e = 0`: — |

**Symmetry.** Slot `a` with deviation `e` behaves like slot `7 − a` with deviation `1 − e` (the reading reflected through the
nearest multiple of 8).

## 3. What the table says  `[PROVED — arithmetic]`

**(i) Spine 1 is in the way only for a near-sharer.** Only readings within 1 of a multiple of 8 are in the way at `r = 1`: slot
`≡ 0`, or slot `≡ 7` with `e > 0`. This is the band identity at the bound.

**(ii) Depth rule.** Let a near-sharer's reading be at distance `δ < 1` from its multiple of 8 (`δ = e` for slot `≡ 0`, `δ = 1 − e`
for slot `≡ 7`). It is in the way at exactly the spines `r < 1/δ`: all four when `δ < 1/7`, `{1, 3, 5}` for `1/7 ≤ δ < 1/5`,
`{1, 3}` for `1/5 ≤ δ < 1/3`, `{1}` for `δ ≥ 1/3`. An exact slot-sharer (`δ = 0`) is in the way at all of them (Prop 6.6).

**(iii) Every other runner is in the way at two spines at most**, and only as `{3, 7}` (slot 2 on `(1/3, 3/7)`, slot 5 on
`(4/7, 2/3)`) or `{5, 7}` (slot 3 on `(2/7, 2/5)`, slot 4 on `(3/5, 5/7)`). No slot in 1–6 is ever in the way at spine 1, and none
at both 3 and 5.

**(iv) When all four spines are in the way.** They are all in the way exactly when there is a near-sharer of depth `δ`, and the
spines `r ≥ 1/δ` it leaves are each in the way for some other runner from the table:

| near-sharer depth | spines left to the others | fewest other runners that can do it |
|---|---|---|
| `δ < 1/7` | none | 0 |
| `1/7 ≤ δ < 1/5` | 7 | 1 (slots 1, 2, 3, 4, 5, 6 on their spine-7 windows) |
| `1/5 ≤ δ < 1/3` | 5, 7 | 1 (slot 3 on `(2/7, 2/5)`, slot 4 on `(3/5, 5/7)`); otherwise 2 |
| `δ ≥ 1/3` | 3, 5, 7 | 2 (one `{3, 7}` and one `{5}`, or one `{5, 7}` and one `{3}`); otherwise 3 |

Several near-sharers can share the work. The spines in the way are the union of the runners' sets.

## 4. The directed step, read in the same coordinates  `[PROVED — arithmetic; the step itself is Lean: nextOpening_at_scale]`

When spine 1 is in the way, the cascade's step is fixed by the speeds. The next scale is `D′ = D·s_x/(8M + 1)` for the in-the-way
runner `x` with the largest `(8M + 1)/s_x`. In the coordinates above:

- **Every reading is multiplied by the same factor** `λ = (8M + 1)/s_x > 1`: `s′_j = λ·s_j`.
- **The setter lands in slot `≡ 1` with deviation 0**, since `s′_x = 8M + 1`. By the table's `a ≡ 1`, `e = 0` entry it is clear at
  every spine of the new scale. More generally, an odd reading `8M + 1` is never within 1 of a multiple of 8 at odd `r`.
- **Every other runner's deviation drifts by `(λ − 1)·s_j`**: `a′_j + e′_j = a_j + e_j + (λ − 1)·s_j`. Its slot changes only when the
  drift carries it past a whole number.

So a step of the cascade is a single dilation of all the readings. The setter is placed exactly on the ideal, and every other
runner is relocated by an amount proportional to its reading.

## 5. What this gives next

The single-scale question is now closed-form: §3 (iv) is the complete list of ways every spine of one scale can be in the way.
The next native question follows from §4: **starting from a configuration in §3 (iv)'s list, where does the dilation `λ` place
each runner in the table?**
- The setter is always moved to a clear position.
- A near-sharer of depth `δ` is moved by `(λ − 1)·s`.
- The runners that were in the way at spines 3, 5, 7 drift by amounts proportional to their readings.

Whether some sequence of such dilations can keep every spine in the way at every scale is Existence in these coordinates.
