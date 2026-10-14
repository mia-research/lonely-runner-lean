# Order 5 in Lean: what is proved, and the one statement that is not

2026-09-21, version 1. Works through the difficulty list at the end of `WHY_FIVE_v1.md` §5.

Artefacts: `LonelyRunner/LRC/Spec/FlankFiniteN.lean` (13 declarations, all axiom-clean, no
`sorry`, no `native_decide`) · `experiments/n8/flankfinite_axioms_v1.{lean,out}` ·
`experiments/nN/blocker_trace.py` · `blocker_gcd_v1.{py,out}` · `union_slack_v1.{py,out}` ·
`last_opening_v1.{py,out}`

**Headline grade: `n = 5` is NOT proved.** One statement, `FourClears`, is outstanding. It is a
`Prop` in the Lean and appears only as a hypothesis.

---

## 1. The difficulty list, worked

| item | status |
|---|---|
| decidable integer predicate + bridge to the reals | **done** — `lonely_of_flankWorks` |
| finite check, `d_max ≤ 15` | **done** — `four_clears_small`, by `decide`, **no axioms at all** |
| `Finset ℝ` plumbing | **done** — `lonely_of_small_cover` |
| rational ⟹ whole-number by scaling | **done** — `lonely_flank_smul_iff`, both directions |
| ratio-condition region `d_max ≤ (n−1)d_min` | **done** — `clear_at_last_opening`, `lonely_last_of_ratio` |
| reduction of the `n = 5` door to a statement with no 5 in it | **done** — `doorLargestFlank_of_fourClears` |
| irrational ratios | **blocked** — needs multi-dimensional Kronecker/Weyl; Mathlib has only the 1-D `AddCircle.denseRange_zsmul_coe_iff` |
| **margin argument, `d_max > (n−1)·d_min`** | **NOT DONE — the whole remaining gap** |

The finite check is stated over sorted quadruples `a ≤ b ≤ c ≤ e`, which by scale invariance
needs no primitivity hypothesis and by repeated entries covers the collapsed cards too.

---

## 2. Instrumentation: what each blocker does, where and when

`experiments/nN/blocker_trace.py` is a reusable library, not a one-off: for each blocker
separately it records the blocked openings as **runs**, the run count and lengths, and the
per-opening attribution (which blockers blocked each `j`). Nothing is aggregated away. It
carries the predictions to check against, and they hold:

- **the flank is never blocked** — at a flank opening of `e`, `d = e` sits at exactly `1/n`;
- **every non-flank blocker blocks `j = 0`** — the reading is `d/(n e) < 1/n` whenever `d < e`,
  so overlap at the start is structural;
- blocker `d` blocks about `d` runs of length about `2e/(n d)`, total about `2e/n`.

Two things the aggregate measure had hidden:

- **Coarse lattices over-block.** With `g = gcd(d,e)` the readings lie on a lattice of only
  `e/g` points, so `d = 8` at `e = 16, n = 8` blocks 8 openings, not the predicted 4. But this
  is **not** the discriminator: failures and successes have the same `g` distributions
  (`blocker_gcd_v1.out`), and the maximum over-block ratio is `n/4` at every order, i.e. one
  blocker never blocks more than `e/2`.
- **Pigeonhole cannot work.** Blocking capacity (sum of blocked counts over `e`) reaches 1.50
  at `n = 5` and exceeds 1 for 1,472,573 of 1,473,833 sets. The blocked sets must overlap
  heavily; counting alone will never prove this.

---

## 3. The ratio-condition region is a theorem, and why

Exhaustively there are **zero** largest-flank failures inside `d_max ≤ (n−1)·d_min`, at every
order. The reason is exact: at the **last** opening `j = e − 1` the reading of `d` is
`d − d(n−1)/(n e)`, so for whole-number `d` the circle distance is `circDist(d(n−1)/(n e))`,
which reaches `1/n` exactly when `e ≤ (n−1)d ≤ (n−1)e`. Verified with **0 mismatches over
17,690 `(n,e,d)` triples** (`last_opening_v1.out`), and it accounts for every ratio-condition
set in the sweeps.

**This is not a new criterion.** It is `Flanks.clear_at_opening_of_band` — the framework's
general, real-valued band test at every `(flank, opening)` pair, which already has a converse
making it an `iff` — instantiated at `k = e − 1` with `M = d − 1`. What is new is only the
identification of *which* instance covers the ratio condition. `clear_at_last_opening` is proved
that way in the file, so the attribution is visible in the proof term.

Coverage: at `n = 5` over `[1,260]`, the ratio-condition region is 72,887,168 of 172,352,957
sets — about **42%**. The other 58% is what `FourClears` still owes.

---

## 4. The gap, stated precisely

```lean
def FourClears (n : ℕ) : Prop :=
  ∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) → ds.card ≤ 4 → ∀ e ∈ ds, (∀ d ∈ ds, d ≤ e) →
    ∃ j : ℕ, Lonely n ds (flankOpening n e j)
```

`[EMPIRICAL]` — no counterexample in 172,352,957 exhaustive sets at `n = 5`, nor across
`n = 5 … 50`. **Not proved.**

What is known about the outstanding 58%:

- **the target is a margin statement.** At `n = 5` the union of the blocked sets never exceeds
  `31/33` of the openings — attained at `(5,15,20,33)` and unchanged from `[1,40]` to `[1,80]`
  across 1.47M sets — while `n = 6, 7, 8` all reach exactly 1 (`union_slack_v1.out`). So the
  statement to prove is `union/e ≤ c < 1`, uniformly.
- **the slack grows with `e`.** Minimum survivors rise roughly like `e/10`: 1 at `e ≤ 12`, 2 at
  `e = 18`, 3 at `e = 30`, 6 at `e = 60`. The tight cases (exactly one survivor) are 57 sets,
  all with `d_max ≤ 15` — which is what the finite check already discharges.
- **it is not a counting argument** (§2), so the proof must use the forced overlap, not measure.

---

## 5. Grades

| claim | grade |
|---|---|
| the 13 declarations of `FlankFiniteN.lean` | `[PROVED — flankfinite_axioms_v1.out, 13/13 axiom-clean]` |
| `four_clears_small` | `[PROVED — by `decide`, depends on NO axioms]` |
| `clear_at_last_opening` is an instance of `clear_at_opening_of_band` | `[PROVED — it is proved that way]` |
| the last opening clears exactly `e/(n−1) ≤ d ≤ e` | `[VERIFIED — 0 mismatches, 17,690 triples]` |
| every non-flank blocker blocks `j = 0` | `[PROVED — `d/(ne) < 1/n` for `d < e`]` |
| pigeonhole cannot prove `FourClears` | `[VERIFIED — capacity ≥ 1 for 1,472,573 of 1,473,833 sets at `n = 5`]` |
| `union/e ≤ 31/33` at `n = 5` | `[EMPIRICAL — exhaustive to [1,80]; not a proof]` |
| `FourClears n` | **not proved** |
| Mathlib lacks multi-dimensional Kronecker/Weyl | `[VERIFIED — only `AddCircle.denseRange_zsmul_coe_iff` (1-D) found]` |

**Scope.** All sweeps are over whole-number difference sets, hence by `lonely_flank_smul_iff`
all rational ones. Irrational ratios are covered by no sweep and by no proof here.
