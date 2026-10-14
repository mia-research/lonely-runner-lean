# Grid-anchored witness tracking — the first-order obstruction *is* Unit-Complete

2026-09-11. Script `experiments/n8/ok_gridtrack_v1.py`. Exact `Fraction`. Owner's idea:
take the AP/grid configuration, where global isolation is exact, as a base, and track where a
runner's cover moves when it is sped up or slowed toward its neighbour.

---

## 1. The base and the deformation  `[PROVED]`

At `t = a/8`, `a ∈ (ℤ/8)*`, runner `e` sits at `r/8` with `r = ea mod 8`. The AP `(1,…,7)`
sends `{1..7}` to a permutation of itself, filling all eight sites with every gap exactly
`1/8` — verified. It is a witness exactly when no `e ≡ 0 (mod 8)`, i.e. Case 1.

Put `t = a/8 + ε`. A multiple of 8, `e = 8δ`, has `8δ·a/8 = δa ∈ ℤ`, so it leaves `0` at rate
`8δ`. Every other runner leaves `r/8` at rate `e`. Hence

| `r` | slack | admissible direction |
|---|---|---|
| `2,…,6` | `1/8` each side | either, while `\|eε\| ≤ 1/8` |
| `7` | none above | `eε ≤ 0` only |
| `1` | none below | `eε ≥ 0` only |

All speeds are positive, so `ε > 0` kills every `r = 7` runner and `ε < 0` every `r = 1`. A
direction survives at grid point `a` iff `7 ∉ {ea mod 8}` or `1 ∉ {ea mod 8}`. Multiplication
by a unit permutes `{1,3,5,7}` transitively, so an odd-residue runner meets `7` for exactly one
`a` in four. Therefore:

> **If all four odd residues appear among `{e mod 8}`, every `a` places a runner on `7` and a
> runner on `1`, and no direction survives.**

## 2. That is exactly the Unit-Complete leaf  `[PROVED — 31 788/31 788]`

Over **all** 31 788 primitive 7-tuples in `[1..18]`:

> **first-order direction fails ⟺ the tuple is Unit-Complete** — 100.00%, exact, complete
> enumeration.

The project's hardest named leaf is not an assumption of the case tree: it is the precise
obstruction to perturbing off the grid. `CASE_TREE_AUDIT_v1` §2 records `|R_non| = 5` as
"**assumed** … never derived"; the *Unit-Complete* condition itself now has a derivation.

## 3. Witnesses are localised near the grid  `[VERIFIED — exhaustive, then sampled]`

For each tuple let `ρ(E)` be the exact distance from the nearest grid point `a/8` to the
closed good set `Ḡ(E) = {t : ‖e_j t‖ ≥ 1/8 ∀j}`.

- **Case 1**: `ρ = 0` for all 1332 tested — the grid point *is* the witness. (Control.)
- **Case 2, complete `[1..18]`, 20 349 tuples**: `ρ > 0` always, and
  **`max ρ = 1/10`**, at `(1,2,3,5,6,7,8)`. Grid points are spaced `1/4`, so this confines
  every witness to `80%` of the circle.

Sampled at larger boxes, `max ρ` **shrinks**: `1/10` at `[1..18]`, `1/16` at `[1..40]`,
`9/256` at `[1..120]`, `9/512` at `[1..600]`, and `13/724` on Unit-Complete-plus-multiple-of-8
adversaries. Sample sizes fall across those rows (4000 → 1500), which biases a maximum
**downward**, so the trend is suggestive and not established; the `[1..18]` row is exhaustive
and is the only one that is a bound.

**Why this matters more than the bound's size.** `project_n8_unitcomplete_theorem` records
"LRC(7) does **not** help — existence ≠ localisation". A grid-anchored distance bound is a
**localisation** statement, which is the ingredient that route lacked. That is the real content
of the idea.

## 4. The first-order window is not a certificate  `[PROVED — exhaustive]`

Over the 18 149 non-Unit-Complete Case-2 tuples in `[1..18]`, a witness lies inside the
first-order window `|ε| ≤ 1/(8·e_max)` in only **2550 (14.05%)**. So first-order admissibility
is **necessary but not sufficient**.

The reason is explicit and was predictable: a multiple of 8 needs `‖8δε‖ ≥ 1/8`, hence
`ε ≳ 1/(64δ)`, while the conservative slack allows only `ε ≤ 1/(8 e_max)`; these are compatible
only when `e_max ≤ 8δ_min`, i.e. when the smallest multiple of 8 is the largest speed. The
window is too narrow because it keeps only the *central* admissible interval for each runner
and discards the rest — each runner is in fact admissible on `3/4` of the `ε`-line. Widening it
correctly recovers the full `u(E)` computation, so the naive widening is not a shortcut.

## 5. A bug of mine, caught by the control  `[recorded]`

Control 1 initially failed 242/1332. The bad sets `{t : ‖et‖ < 1/8}` are **open**, and I merged
them with `lo ≤ prev_hi`; two open intervals that merely touch share an endpoint belonging to
neither, so merging deleted a genuine isolated witness. Strict `<` is correct, and the control
then passed 0/1332. This is the failure mode
`feedback_verify_agent_source_claims_2026_09_07` names — measure entry and exit, never assume
the breakpoint list closes.

## 6. Ledger

`[PROVED]` §1 the deformation rates and the direction rule; §2 the equivalence
first-order-fails ⟺ Unit-Complete, complete enumeration, 31 788/31 788.
`[VERIFIED — exhaustive]` §3's `max ρ = 1/10` over the complete `[1..18]` Case 2; §3's Case-1
control; §4's 14.05%, complete enumeration.
`[EMPIRICAL — sampled, downward-biased]` §3's shrinking trend at larger boxes.
`[recorded]` §5.

`n = 8` is **not proved**, and nothing here moves a grade. What is new: the Unit-Complete leaf
is derived rather than assumed, and the grid supplies an anchor for a localisation bound.
