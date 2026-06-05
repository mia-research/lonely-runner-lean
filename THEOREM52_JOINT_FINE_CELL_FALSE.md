# `joint_fine_cell_exists` is FALSE as stated — counterexample report

**Session:** 2026-05-26 (continued)
**File:** `LonelyRunner/LRC/Theorem52_Weyl.lean` line 1379
**Build status:** clean (2485 jobs); the sorry remains but now carries a FALSE annotation.

---

## Summary

The lemma `joint_fine_cell_exists` in `Theorem52_Weyl.lean` is **provably false** under
its stated hypotheses. An exhaustive harness over

- `n ∈ {3, 4, 5, 6, 7}`,
- `G_speeds, A_speeds ⊆ {1, …, 8}` of size 1–3 (G) and 1–2 (A),
- primes `p ≤ 19`,

with LRC-like restrictions (disjoint `G_speeds`/`A_speeds`, `p ∉ G_speeds ∪ A_speeds`,
`gcd(p, G_speeds ∪ A_speeds) = 1`, hard case `p < n · L_G`), found **681 counterexamples**.

Without the LRC restrictions, the raw count is **1696 / 64842 = 2.6%** of eligible inputs.

---

## Smallest counterexample (manually verified)

| Item | Value |
|---|---|
| `n` | 3 |
| `G_speeds` | `[3]` |
| `A_speeds` | `[1, 5]` |
| `p` | 2 |
| `L_G = lcm G_speeds` | 3 |
| `L_A = lcm A_speeds` | 5 |
| `M_A = n · L_G · L_A` | 45 |
| `n · L_G · L_A · p` | 90 |
| `goodCellIdx G_speeds n L_G` | `{1, 4, 7}` (3 elements) |
| `goodCellIdx A_speeds n L_A` | `{7}` (1 element) |
| `gcd(p, L_G) = 1` | ✓ (gcd(2,3) = 1) |
| `gcd(p, n · L_G · L_A) = 1` | ✓ (gcd(2, 45) = 1) — even strengthened coprimality holds! |
| Hard case `p < n · L_G` | ✓ (2 < 9) |
| Lemma conclusion: ∃ m'' < 90 satisfying both | **FALSE** — exhaustive search returns 0 |

**Manual verification (matches Lean exactly):**

- The α-constraint `m'' / (L_A · p) = m'' / 10 ∈ {1, 4, 7}` gives `m'' ∈ [10,20) ∪ [40,50) ∪ [70,80)`.
- The β-constraint `(m'' mod 45) / 3 ∈ {7}` gives `m'' mod 45 ∈ [21, 24)`, i.e. `m'' ∈ [21,24) ∪ [66,69)`.
- Intersection of these two sets in `[0, 90)`: **∅**.

---

## What this means

### The lemma is structurally false

The fine-cell decomposition is a **sufficient** condition for joint occupancy:
if `m''` is a joint-good fine cell, then the open cell at `m''` contains a `t₀` with
both `t₀ ∈ jointGoodSet G_speeds n` AND `Int.fract(p · t₀) ∈ jointGoodSet A_speeds n`.

It is **not a necessary** condition. The downstream conclusion (existence of *some*
`t₀`) can hold via `t₀`s that are not aligned to any 1/(n·L_G·L_A·p) cell.

For the counterexample above:
- Conclusion of `theorem52_nonempty_structured` translates to:
  ∃ `t` with `circDist(3·t) ≥ 1/3` AND `circDist(2·t) ≥ 1/3` AND `circDist(10·t) ≥ 1/3`
  (using Lemma 2.1 `circDist(v·fract(w·t)) = circDist(vw·t)`).
- This is LRC for the 4-runner instance {2, 3, 10}, which is **true** (LRC for n ≤ 7 is classical).
- So the conclusion is provable, but the proof via fine-cell counting is not viable.

### Earlier memory was aware of the issue

`memory/lean_theorem52_blocker_analysis_2026_05_25.md` (Step 7) already noted:
> ⌊m''/p⌋ and m'' mod (n·L) are NOT independent functions of m'' …
> Pure cell counting cannot give μ(G ∩ p⁻¹(A)) ≥ μ(G)·μ(A) in general.

`memory/lean_theorem52_option_a_restructuring_2026_05_25.md` flagged that the hard
case "may not suffice" without stronger hypotheses. **This session confirms the
hardest form: even the lemma's STATEMENT is false.**

---

## Remediation options

### (A) Strengthen hypothesis to a cardinality bound

Add `(hCard : |goodCellIdx_G| · L_A · p + |goodCellIdx_A| · L_G > n · L_G · L_A)`.

- **Pros:** straightforward inclusion-exclusion proof. The easy case (`p ≥ n·L_G`)
  satisfies it automatically since `L_A · p ≥ n · L_G · L_A`.
- **Cons:** at the DI/ModDI call sites, `|goodCellIdx_G|` is derived from positive
  measure on `[0,1)`, but `μ(G ∩ [0,1)) · n · L_G` may be much smaller than `n·L_G`
  in absolute count terms. Need to audit whether the bound ever holds in the
  hard-case call shapes.

### (B) Reformulate without the fine-cell reduction

Skip `joint_fine_cell_exists` and `theorem52_structured_of_joint_exists`. Instead
prove `theorem52_nonempty_structured` directly via:

- **Measure-theoretic argument:** consider the pushforward of Lebesgue measure on
  `[0,1)` under `t ↦ (t, fract(p·t))`. Show its restriction to `G × A` is positive
  for almost all `(G, A)` with both positive-measure. Requires either ergodicity
  for the multiplication-by-p map on `AddCircle 1` (in Mathlib as `ergodic_nsmul`)
  combined with mixing (NOT in Mathlib), OR direct Fourier-analytic argument.

- **Lipschitz pushforward bound:** `t ↦ fract(p·t)` is `p`-Lipschitz with slope `p`.
  The image of an interval of length `δ` under fract(p·t) covers `[0,1)` with
  multiplicity `pδ` (approximately). Sharpen to get a quantitative intersection
  with `A` when `A` has interval witness.

### (C) Add structural hypothesis `gcd(p, n · L_G · L_A) = 1`

- **Pros:** makes `α ↦ (α·p) mod (n·L_G)` a bijection; arcs cover [0, M_A) with
  multiplicity exactly p.
- **Cons:** the counterexample above already satisfies this (gcd(2, 45) = 1).
  So necessary but NOT sufficient.

### (D) Switch to interval-witness hypothesis (recommended)

Add `(hG_witness : ∃ a b : ℝ, a < b ∧ Set.Icc a b ⊆ jointGoodSet G_speeds n ∩ Set.Ico 0 1)`
and similarly for A, with `b - a > 1/(n · L_G · L_A · p)` or similar bound.

- **Pros:** the call sites already provide explicit interval witnesses via
  `lemma41_positive_measure`. The bound is provably attainable for prime `p`
  bounded away from `n` (which holds in the DI tail case).
- **Cons:** small primes still need separate handling; arguably this just moves
  the same problem.

### Recommended next step

Audit the DI/ModDI call sites to determine: when `p` is a fixed small prime
(p = 2, 3, 5, 7), under what additional structure does the joint witness exist?
This may motivate a case split on `p` rather than a uniform combinatorial proof.

---

## Call-site audit (added in same session)

**Key arithmetic at the DI call site** ([Theorem101_DI.lean:230-231](LonelyRunner/LonelyRunner/LRC/Theorem101_DI.lean)):

The DI hard case is defined by:
```
(hV_hard_lo : (n - 1) * slowSpeeds ⟨0⟩ < V)
(hV_hard_hi : V ≤ (n - 1) * slowSpeeds ⟨n - 3⟩)
```

So `V ≤ (n-1) · V_slow_max` always.

From [Lemma41_PositiveMeasure.lean:34](LonelyRunner/LonelyRunner/LRC/Lemma41_PositiveMeasure.lean):
```
lemma41_delta n vmax := 1 / (n · (n-1) · vmax)
```

So the interval witness has `2δ ≥ 2 / (n · (n-1) · V_slow_max)`.

**The interval-pigeonhole condition (Option D)** would require:
```
2δ · p > max_gap(A) = 2 / (n · q)         [for A = goodSet q n]
⟺ p > (n-1) · V_slow_max / q
⟺ p · q > (n-1) · V_slow_max
⟺ V > (n-1) · V_slow_max
```

**…but the DI hard case hypothesis says exactly `V ≤ (n-1) · V_slow_max`.** Direct contradiction.

### What this means for each remediation option

| Option | Status at DI call site |
|---|---|
| (A) Strengthen with explicit cardinality bound | **Cannot be supplied.** `|goodCellIdx_G|` is derived only from `μ(G ∩ [0,1)) > 0`; the absolute count in `[0, n·L_G)` may be much smaller than what the bound requires. |
| (B) Reformulate without fine cells (Birkhoff/mixing) | **Blocked by Mathlib 4.14.** Mixing for `T_p` on `AddCircle 1` is not formalised. |
| (C) Add `gcd(p, n · L_G · L_A) = 1` | **Necessary, not sufficient.** Counterexample `(n=3, G=[3], A=[1,5], p=2)` satisfies it. |
| (D) Use interval-witness from Lemma 4.1 | **Blocked by `hV_hard_hi`.** The DI hard-case hypothesis `V ≤ (n-1)·V_slow_max` is *exactly* the negation of what pigeonhole would need. |

**The DI/ModDI hard case hypotheses actively prevent every natural strengthening** of `joint_fine_cell_exists`.

### Architectural implication: Theorem 5.2 might be the wrong intermediate

Observe: `theorem52_nonempty_DI`'s conclusion (`∃ t₀ ∈ G_s, fract(p·t₀) ∈ goodSet q n`)
is, via Lemma 2.1, **logically equivalent** to `theorem101_DI`'s conclusion
(`∃ t₀ ∈ G_s ∩ goodSet V n`, since `circDist(q · fract(p·t)) = circDist(p·q·t) = circDist(V·t)`).

So `theorem52_nonempty_DI` adds no logical content beyond `theorem101_DI` itself.
The lemma is doing zero work in the DI case — it just repackages the conclusion.

**Recommendation (Option E, new):** Bypass Theorem 5.2 entirely in the DI/ModDI
chain. Prove `theorem101_DI` / `theorem111_ModDI` directly using:
- `H(n-1)` (or `H(n-r)`) via Lemma 4.1 for the slow-runner interval witness.
- `H(r+3)` for the A-side structure (in ModDI).
- A *different* combination step that doesn't reduce to fine cells or measure
  intersection — perhaps a direct LRC-internal compositional argument leveraging
  the specific `V = p · q` structure.

This is a larger refactor but eliminates the fundamental obstruction. The
manuscript's "Theorem 5.2 = CRT independence" framing may be inessential to the
overall LRC inductive proof — it was a convenient lemma in the prose, not a
load-bearing structural ingredient. The Lean formalisation can choose a different
decomposition that doesn't get stuck on this gap.

## Status going forward

- The 3 remaining Lean sorries are now properly understood and documented.
- `joint_fine_cell_exists` is the one that needs the architectural rework above.
- The two `theorem121_LRC` sorries are independent (intLRC gcd refactor + real-speed
  reduction) and can be addressed in parallel.

---

## Files modified this session

- `LonelyRunner/LRC/Theorem52_Weyl.lean` — docstring at line 1364 rewritten to
  document the FALSE finding. Sorry remains (lemma is still cited by
  `theorem52_nonempty_structured`).
- `LonelyRunner/THEOREM52_JOINT_FINE_CELL_FALSE.md` — this file.
- `/tmp/joint_fine_cell_harness.py`, `/tmp/joint_fine_cell_filter.py`,
  `/tmp/verify_smallest_ce.py` — harnesses used to discover and verify
  counterexamples (copied to `LonelyRunner/scripts/` if persistent record desired).

## Build status

`lake build` → 2485 jobs clean. Sorry count unchanged at 3 (the FALSE one is now
documented; the two in `Theorem121_Main.lean` are independent).
