# Every obstacle sits at zero, and a window covers its divisors

Lean: `experiments/n8/WindowGeometry_v1.lean` (5 theorems, 0 errors, axiom-clean). Scripts:
`step_interval_v1.py`, `tower_greedy_v1.py`, `tower_greedy_v2.py`, `tower_invariant_v1.py`,
`tower_step_v1.py`, `tower_step_v2.py`.

---

## 1. The geometry, proved

**[PROVED — `clear_iff_window`]** `q` clears modulus `b` iff `b ≤ 8*(q mod b)+1 ≤ 7b`, iff the
residue lies in `[L(b), U(b)]`, `L(b) = ⌈(b-1)/8⌉`, `U(b) = ⌊(7b-1)/8⌋`.

**[PROVED — `blocked_iff_near_zero`]** So the blocked set is `[0, L-1] ∪ [U+1, b-1]`: a single
**cyclic interval centred on 0**, of radius about `b/8`. Every obstacle in the divisor-closed
problem sits at `0`, and the clear set is **one** interval, not a scattered set.

**[PROVED — `window_ge_half`]** The window width `w(b) = U(b) - L(b) + 1` satisfies
`2*w(b) ≥ b` for every `b ≥ 2`. **[VERIFIED to `b = 50000`]** before proving.

**[PROVED — `window_covers_divisor`]** Hence for any proper divisor `b' ∣ b`, since
`2b' ≤ b ≤ 2*w(b)` we get `b' ≤ w(b)`: **the clear window of `b` always contains a complete
period of `b'`.** This is the geometric fact that licenses a nested construction down a divisor
tower — the window is never too narrow to see all of a smaller modulus.

## 2. Divisor towers: greedy nesting works — **[VERIFIED, not proved]**

Take the moduli in decreasing order `b₁ > b₂ > ... `, each dividing the previous. Start with
`[L(b₁), U(b₁)]`; at each step intersect with the next window and keep the **longest surviving
piece**.

**[VERIFIED]** 200,000 / 200,000 random towers (up to 6 levels) and **50,894 / 50,894**
exhaustive divisor towers drawn from the divisors of highly composite `m`. No failures.

## 3. Why it is not yet a proof, exactly

The induction needs an invariant on the surviving interval. Two length-only candidates were
tried and **both are refuted**:

| invariant | refuted by |
|---|---|
| `\|I\| ≥ w(b) - 1` | `b = 18, b' = 9`: surviving run `5`, needed `6` |
| `\|I\| ≥ ⌈b/2⌉` | `b = 6, b' = 3`: surviving run `1`, needed `2` |

The reason is identifiable rather than mysterious. Greedy's surviving interval is not an
arbitrary interval of a given length — it sits at a **specific position** inside `[L(b), U(b)]`,
and because `b' ∣ b` the `b'`-arcs are *aligned* to that frame. A length-only invariant throws
away exactly the information that makes the step work. **The owed piece is a positional
invariant**, and that is a precise statement of what remains, not a vague one.

### A correction made on the way

The first greedy implementation demanded a **full** window run of length `w(b)` at each level.
That needs `|I| ≥ b + w(b) - 1 ≈ 7b/4`, while the construction only supplies `≈ 3b/4`, so it
failed 82,599 of 200,000 towers. A truncated run is enough provided it still covers the next
modulus. With the longest surviving piece instead, the failures go to zero. The first version
was wrong and the exhaustive check caught it.

## 4. The step reduction, and its limit

Writing `q = L(m) + T`: at a collider the residue of `L(m)` is `0` (proved,
`CanonicalCandidate.collider_blocked`), so `q`'s residue is `T`; at a non-collider it is
`R_b + T`. If `R_b + T ≤ U(b)` there is no wraparound and clearing becomes a plain interval
condition on `T` — no modular arithmetic:

```
    T ∈ [L(b), U(b)]              at every collider b
    T ∈ [L(b) - R_b, U(b) - R_b]  at every non-collider b
```

**[VERIFIED — 25,000 Branch B profiles]** the intersection is non-empty **44.82%** of the time,
and wherever it is non-empty `q = L(m) + T` really clears (11,205 / 11,205 checked).

That is **lower** than the single choice `T = L(b*)`, which reached 59.84%. The gap is the
no-wraparound restriction: `L(m) + L(b*)` sometimes clears *by* wrapping a modulus past `b`,
which the interval form excludes by construction. Allowing wrap turns each condition back into
a union of arcs, which is the original problem — so the interval form is a genuine but strictly
partial simplification, and its 44.82% should not be read as a regression.

## 5. Grades

* **[PROVED]** §1, five theorems, axiom-clean.
* **[VERIFIED]** the tower construction (§2), the step reduction's reach (§4).
* **[OPEN]** the positional invariant of §3, and with it the divisor-tower class.

Existence at order 8 remains open.
