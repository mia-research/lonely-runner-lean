## Domain
Lean 4 formalisation of a proof of the Lonely Runner Conjecture (LRC).
The source manuscript is `../../lrc_proof_v11_draft.md`.

## Mathematical dependencies (check Mathlib for each)
- `Int.fract` and `Int.fract_add_int` (fractional parts) — in `Mathlib.Algebra.Order.Floor`
- `Nat.Coprime`, `Nat.minFac` (prime arithmetic) — in `Mathlib.Data.Nat.GCD.Basic`
- `MeasureTheory.volume` (Lebesgue measure) — in `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`
- `Finset.lcm` — in `Mathlib.Data.Finset.Lattice`
- CRT-measure independence (Theorem 5.2) — NO direct Mathlib match; must be proved from primitives

## Proof structure
Strong induction on n. Four mutually exclusive cases:
- Theorem 6.1: Bounded Speed Ratio (explicit time t* = 1/(n v_1))
- Theorem 7.1: Large Speed Ratio (neighbourhood argument)
- Theorem 10.1: Divisor Induction (Weyl + coprimality)
- Theorem 11.1: Modified Divisor Induction (Fundamental Identity reduction)

## Critical dependency
**Theorem 5.2** (CRT measure lemma) in `Theorem52_Weyl.lean` is the primary blocker.
It is NOT classical Weyl equidistribution — it is a finite measure-factorisation
via the Chinese Remainder Theorem for real intervals.  Proving it requires ~200-400
lines of Lean formalizing the bijection `φ : [0, 1/(Lp)) → [0, 1/L) × [0, 1/p)`.

## File layout
- `LRC/Defs.lean` — circDist, goodSet, jointGoodSet, LRC predicate
- `LRC/Lemma21_FundamentalIdentity.lean` — {a·{b·t}} = {a·b·t}
- `LRC/Lemma41_PositiveMeasure.lean` — μ(G_s) > 0 from H(n-1)
- `LRC/Theorem52_Weyl.lean` — CRT independence lemma (**primary blocker**)
- `LRC/Theorem61_BSR.lean` — Bounded Speed Ratio (routine)
- `LRC/Theorem71_LargeSR.lean` — Large Speed Ratio (moderate)
- `LRC/Theorem101_DI.lean` — Divisor Induction (hard, depends on 5.2)
- `LRC/Theorem111_ModDI.lean` — Modified Divisor Induction (hardest section)
- `LRC/Theorem121_Main.lean` — Assembly + main theorem

## Style
- Use `sorry` stubs freely; the goal is type-correctness and structure.
- Prefer `norm_num`, `omega`, `linarith`, `simp` for arithmetic goals.
- Every sorry has a structured BLOCKER / MATHLIB_SEARCH / STATUS comment.

## Environment note
The Mathlib precompiled cache (`lakecache.blob.core.windows.net`) may not be
reachable in sandboxed environments. Run `lake exe cache get` in a network-enabled
environment, then `lake build` to type-check all files.
