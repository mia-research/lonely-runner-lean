# A top-gap theorem for `n = 8`, from the nearest prime below

2026-09-07. Pursuing the suggestion that `n = 8` be viewed in relation to the nearest
prime. The nearest prime **below** is `n = 7`, and this project owns `intLRC_seven`
machine-verified and axiom-clean. That input, plus the Boundary Set Method, gives a
structural constraint on any counterexample to LRC(8).

Scripts: `experiments/n8/drop_one_measure_v1.py` (measure form),
`drop_one_measure_v2.py` (component form). Level `1/8` throughout, exact rationals.

## 1. The geometry that makes the drop-one idea work

For a speed `v`, its **bad set** is `B(v) = {t ∈ [0,1) : ‖tv‖ < 1/8}` — exactly `v`
intervals of length `1/(4v)`, at period `1/v`, separated by gaps of length `3/(4v) > 0`.
Total measure `1/4`, independent of `v`.

**Lemma 1.** *If `C` is a connected component of a set covered by `B(v)`, then
`|C| ≤ 1/(4v)`.* The gaps are positive, so a connected set inside `B(v)` lies inside a
single one of its intervals. ∎

**Lemma 2 (from LRC(7)).** *Let `T₆` be six distinct positive integers with maximum `V`.
Then the lonely set `L₆ = {t : ‖t v‖ ≥ 1/8 ∀v ∈ T₆}` contains an interval of length
`≥ 1/(28V)`.*

*Proof.* `intLRC_seven` gives `t₀` with `min_{v∈T₆} ‖t₀ v‖ ≥ 1/7`. For `|δ| < 1/(56V)`,
`‖(t₀+δ)v‖ ≥ 1/7 − |δ|V > 1/7 − 1/56 = 1/8`. So the open interval of radius `1/(56V)`
about `t₀` lies in `L₆`, and has length `1/(28V)`. ∎

## 2. The theorem

**Theorem (top gap).** *Let `v₁ < ⋯ < v₇` be the speeds of an LRC(8) instance. If
`v₇ > 7·v₆` then LRC(8) holds for that tuple. Equivalently: **any counterexample
satisfies `v₇ ≤ 7·v₆`**.*  `[PROVED, given intLRC_seven]`

*Proof.* Apply Lemma 2 to `T₆ = {v₁,…,v₆}`, `V = v₆`: `L₆` holds an interval `C` of length
`≥ 1/(28 v₆)`. If `v₇ > 7v₆` then `1/(4v₇) < 1/(28v₆) ≤ |C|`, so by Lemma 1 `B(v₇)` cannot
cover `C`. `B(v₇)` is open, so some `t ∈ C` has `‖t v₇‖ ≥ 1/8`, and `t` is lonely for all
seven speeds. ∎

**General `n`.** The same two lemmas with level `1/n` and `LRC(n−1)` give: a counterexample
to LRC(`n`) has `v_{n−1} ≤ (n−1)·v_{n−2}`. This is the `n = 8` instance. The argument is
elementary and may well be known in the literature; what is new here is only that its input
for `n = 8` is a machine-verified `LRC(7)`.

## 3. Verification, and how loose the constant is

Frame fixed before running: all `C(24,6) = 134 596` six-subsets of `[1,24]`, level `1/8`,
exact rationals, BSM components merged.

- **Lemma 2 check.** Six-subsets violating `λ(T₆) ≥ 1/(28·max T₆)`: **0 of 134 596**, as
  LRC(7) requires. Also **0 of 134 596** have a lonely set with no positive-length
  component at all.
- **Sharpness.** The worst observed bound is `v₇ ≤ (10/3)·max(T₆)`, at
  `T₆ = {1,2,5,6,7,8}`. So the proved constant `7` is loose by a factor `2.1` on this
  frame; the true constant for `n = 8` is at most `10/3` and at least `10/3`
  on the frame. `[EMPIRICAL, scope: six-subsets of [1,24]]`
- **Absolute bound on the frame.** `v ≤ 1/(4λ) ≤ 80` for every six-subset, the worst being
  `T₆ = {3,6,15,18,21,24} = 3·{1,2,5,6,7,8}` — a scaled tuple, whose components are `1/3`
  as long, consistent with the scaling lemma of `RIGID_CLASS_v2.md` §3. For
  `134 297 / 134 596` of them the seventh speed is forced `≤ 24`.

## 4. The weaker measure form, recorded so it is not re-tried

The crude version of this idea tests `|L₆| > 1/4` — if the six-speed lonely set has measure
exceeding the `1/4` that one speed's bad set can cover, LRC(8) follows at once. **It almost
never fires:** only `186 of 134 596` six-subsets (`0.138 %`) clear it, and
`min |L₆| = 29/1232 ≈ 0.0235`, attained at `{1,4,5,6,7,11}` and its double
`{2,8,10,12,14,22}`. Measure ignores *where* the mass sits; Lemma 1 uses the fact that it
must sit in one piece, and that is what makes the component form work.

## 5. Ledger

**Decided cells: 2 of 135, unchanged.** This decides no cell and does not prove `n = 8`.
What it gives is a proved structural constraint on counterexamples — no large gap at the
top — with an explicit constant, resting on a theorem this project has machine-verified.
Whether `v₇ ≤ 7v₆` prunes the `x = 3` sector enumeration usefully is **untested**.
