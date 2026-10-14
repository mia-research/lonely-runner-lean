# n=8 without a case tree: one inequality, and where its extremum actually sits

2026-09-10. Step (1) of the retarget in `CASE_TREE_AUDIT_v1.md`. Scripts
`experiments/n8/ok_{umax,ufull,case2_sup,intX}_v1.py`. Exact rationals, entry evaluation,
boundary audited (0 entry/exit mismatches).

---

## 1. The reformulation  `[PROVED]`

For `x ∈ [0,1)` let `X(x) = #{r ∈ ℤ/8 : (er + ⌊ex⌋) mod 8 ∈ {1,…,6} for every e ∈ E}`,
the number of **unblocked** residues, and `u(E) = |{x : X(x) = 0}|`. Then

> `∫X > 0` ⟺ `u(E) < 1` ⟹ **a witness exists**, strictly interior.

`X` is a step function on finitely many cells, so the equivalence is exact. This needs no
case tree, no `E_non`/`E_div` split, and no residue shape.

`∫X = 0` is possible, and does not refute anything: it means every witness sits on the
boundary `‖v_i t‖ = 1/8` exactly (block index 7 with `s_e = 0`), which the strict criterion
scores as blocked. Over `[1..18]` — 31 788 tuples — `∫X = 0` occurs at exactly **three**:
`{1,2,3,4,5,6,7}`, `{1,2,3,4,5,7,12}`, `{1,4,5,6,7,11,13}`. These are the known tight
instances, and `TIGHT_INSTANCES_v1.md:51` records that **"none of the three contains a
multiple of 8"**. So every `∫X = 0` tuple lies in Case 1, closed by `t = 1/8`. Hence:

> **The whole of n=8 outside Case 1 is the single statement `u(E) < 1`.**

## 2. My step-(1) plan, as stated, is dead  `[PROVED — counterexample]`

I proposed bounding `u(E_non)` against `|⋃B_m| ≤ |E_div|/4`. Since `|E_non| = 7 − |E_div|`,
that needs `u(E_non) < 3/4, 1/2, 1/4` at `|E_div| = 1, 2, 3`. Exact maxima over primitive
`E_non` drawn from `[1..20]`:

| `k = \|E_non\|` | max `u(E_non)` | argmax | threshold | |
|---|---|---|---|---|
| 4 | `1/3 = 0.3333` | `(1,4,12,20)` | `< 1/4` | **fails** |
| 5 | `9/14 = 0.6429` | `(1,3,4,5,7)` | `< 1/2` | **fails** |
| 6 | `125/154 = 0.8117` | `(1,4,5,6,7,11)` | `< 3/4` | **fails** |

The split `u(E_non) + |⋃B_m| < 1` is lossy at **every** `|E_div|`, not just the hard leaf.
Separating the divisible runners from the rest is the error; §1 keeps them together.

## 3. The sharp target  `[EMPIRICAL — stable across five boxes]`

Maximum of `u` over **Case 2** (`E_div ≠ ∅`), by box:

| box | Case-2 tuples | max `u` | argmax |
|---|---|---|---|
| `[1..14]` | 1 715 | `1727/1820` | `(2,6,7,8,10,13,14)` |
| `[1..16]` | 8 000 | `1727/1820` | same |
| `[1..18]` | 20 349 | `1727/1820` | same |
| `[1..20]` | 45 584 | `1727/1820` | same |
| `[1..22]` | 92 730 | `1727/1820` | same |

**The maximum does not move** as the population grows 54-fold. Equivalently `∫X` attains a
minimum of `93/1820 = 0.05110`, at the same tuple, over all 45 584 Case-2 tuples in
`[1..20]`. So:

> **Case-2 Theorem (target).** For every 7-tuple of distinct positive integers with gcd 1
> and at least one multiple of 8, `∫X ≥ 93/1820 > 0` — equivalently `u ≤ 1727/1820 < 1` —
> with equality exactly on the dilation orbit of `(2,6,7,8,10,13,14)`.

One inequality. It subsumes all 27 residue shapes, both open leaves, and Lemma D.

## 4. Where the extremum sits, and why that matters  `[PROVED]`

`(2,6,7,8,10,13,14)` has residues `(2,6,7,0,2,5,6)`, so `R_non = {2,5,6,7}`,
`|R_non| = 4`, `E_div = {8}`, and the units `1, 3` are **absent**. Its shape is
**dropped-unit, `|R_non| = 4`, `|E_div| = 1`** — which is **not covered by any proved leaf**,
and is the largest of the 23 uncovered shapes.

**The hardest tuple in the entire n=8 problem lies outside the case tree.** (H′) and (NR)
are refinements of the `|R_non| = 5` slice; the true extremum is not in it.

## 5. Why n=8 has no room, quantified  `[PROVED — arithmetic]`

Under independence each runner leaves a fixed `r` unblocked with probability `1 − 2/n`, so
`∫X ≈ n(1−2/n)^{n−1}`:

    n=5: 0.7776   n=6: 0.8038   n=7: 0.9297   n=8: 1.0679   n=9: 1.3080   n=10: 1.3422

**The first-moment margin turns positive exactly at `n = 8`** (`8·(3/4)^7 = 1.0679`), having
been negative at every smaller `n`. Together with `2φ(n)/n = 1` at powers of 2, that is two
independent reasons n=8 is the extremal case — and why no general-`n` machinery will hand
it over. At the extremal tuple the true `∫X` is `0.0511`, **21× below** the heuristic: the
whole difficulty is the correlation between runners, not the count.

## 6. Grades and next

§1: **PROVED** (the bridge restated; the tight-instance fact is cited to
`TIGHT_INSTANCES_v1.md:51`, verified here by recomputation — 3 tuples, none with a multiple
of 8). §2: **PROVED — counterexample**, exact maxima. §3: **EMPIRICAL**, exhaustive over
Case 2 in `[1..22]`; the extremum's stability across five nested boxes is evidence, not
proof, and larger speeds are untested. §4: **PROVED** (residue arithmetic). §5: **PROVED**
(arithmetic) for the margins; the "why" is interpretation.

**Next:** prove `∫X ≥ 93/1820` on Case 2. The first-moment bound alone gives `1.0679` under
independence and the truth is `0.0511`, so the proof must control correlation — but note it
only has to clear **zero**, not `1/2`, which is a far weaker demand than any threshold the
case tree ever asked for.
