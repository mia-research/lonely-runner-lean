# Non-representative base speeds — architecture recovered, and the one gap

2026-09-07. The agent working this leaf was killed by a session limit before writing
its report; 14 scripts survived on disk (`experiments/n8/nonrep_*.py`). This file
recovers what they establish, with every number re-run and the two load-bearing lemmas
re-verified here. Companion to `UNITCOMPLETE_THEOREM_v1.md` (`|E_div| = 2`,
representative) and `TWIN_CASE_THEOREM_v1.md` (`|E_div| = 1`).

## The case

`n = 8`, Case 2, Unit-Complete, `|E_non| = 5`, `|E_div| = 2`, but the base speeds are
**not** representative: `e_ρ = 8q_ρ + ρ` with `q_ρ ≥ 0` not all zero, residues
`{1,3,5,7,ρ₀}`. So `E = {e_1,e_3,e_5,e_7,e_{ρ₀}} ∪ {8m₁, 8m₂}`.

The proof shape from the representative case survives: find `x` in the safe set `S` of
the five base runners and outside `B_{m₁} ∪ B_{m₂}`. What changes is that `S` must be
recomputed, since its cell boundaries sit at `j/e_ρ`, not `j/ρ`.

## 1. B-lemma — a strict sharpening of the union bound  `[PROVED]`

> `|B_{m₁} ∪ B_{m₂}| = 1/2 − |B_{m₁} ∩ B_{m₂}| ≤ 1/2 − d/(4·max(m₁,m₂))`, `d = gcd(m₁,m₂)`.

*Proof.* For `i = 0,…,d−1` the point `i/d` satisfies `m·(i/d) = (m/d)·i ∈ ℤ` for both
`m`, so `‖m·i/d‖ = 0 < 1/8`: each `i/d` lies in **both** `B`'s, together with an arc of
half-width `1/(8·max m)`. Those `d` arcs are pairwise disjoint, their spacing `1/d`
exceeding their width `1/(4·max m)` since `d ≤ max m`. ∎

*Verified here:* all 780 pairs `m₁ < m₂ ≤ 40`, **0 violations**; tight at `(1,2)` where
`|B₁ ∪ B₂| = 3/8` equals the bound; maximum over those pairs `13/28 ≈ 0.4643`.

**Consequence.** `|B_{m₁} ∪ B_{m₂}| < 1/2` **always**, so `|S| ≥ 1/2` suffices — the
representative-case step needed `|S| > 1/2`.

## 2. Reduction when the base speeds share a factor  `[PROVED]`

Let `g = gcd(E_non)`. Since `R_non ∋ 1`, some base speed is `≡ 1 (mod 8)`, hence odd, so
`g` is odd. Suppose `g ≥ 3` and `E` were a counterexample. `Ū_{E_non}` is invariant
under `t ↦ t + 1/g`, so intersecting the `g` shifts,

    S¹ = Ū_{E_non} ∪ ⋂_{j=0}^{g-1} (Ū_{E_div} + j/g).

For a divisible runner `8m`, put `d = gcd(8m,g) = gcd(m,g)`; the values `8m·j/g mod 1`
form a subgroup of order `g/d` with spacing `d/g`, each attained `d` times, and the bad
arc of length `1/4` meets at most `d(⌊g/(4d)⌋+1)` values of `j`. Summing the two
runners gives strictly fewer than `g` (checked by cases on whether each `d` exceeds
`g/4`; `gcd(g,m₁,m₂) = 1` forces at least one `d < g`, and a runner with `d = g` is
itself shift-invariant and moves to the left-hand side). So some shift is missed, the
intersection is empty, and `Ū_{E_non} = S¹` — i.e. the five speeds `E_non/g` cover at
threshold `1/8`, contradicting LRC(6), which gives `1/6 > 1/8` for five speeds. ∎

So only the **primitive** case `gcd(E_non) = 1` remains.

## 3. What the sweep shows  `[EMPIRICAL — exhaustive over the stated range]`

`nonrep_primitive_min_v1.py`, exact rational arithmetic, cells evaluated at their
**entry** point (`(e·p)//D` at the cell start), never at a midpoint:

| `ρ₀` | primitive tuples, `q_ρ ≤ 3` | `min \|S\|` | attained at | tuples with `\|S\| ≤ 1/2` |
|---|---|---|---|---|
| 2 | 1022 | `22/35 ≈ 0.6286` | `(1,3,5,7,2)` | **0** |
| 4 | 1021 | `211/390 ≈ 0.5410` | `(1,3,13,15,4)` | **0** |
| 6 | 1020 | `84294/124729 ≈ 0.6758` | `(17,11,29,23,6)` | **0** |

with the single tuple `{1,3,5,7,4}` excluded — it has `|S| = 5/14 < 1/2` and is exactly
the representative `ρ₀ = 4` case already closed by Lemma D in
`UNITCOMPLETE_THEOREM_v1.md` §5.

## 4. The gap, stated exactly

> **(H)** For every primitive base tuple (`gcd(E_non) = 1`) other than `{1,3,5,7,4}`,
> `|S| ≥ 1/2`.

Given (H), §1 finishes the leaf: `|S| ≥ 1/2 > |B_{m₁} ∪ B_{m₂}|`, and by the
integrality of §3 of `UNITCOMPLETE_THEOREM_v1.md` the surviving set contains an integer
`b`.

**Why (H) is plausible but not yet proved.** Under a uniform model for the floor state
`(t_1,t_3,t_5,t_7,t_{ρ₀}) mod 8` the covered set has measure `1152/32768 ≈ 3.5%`
(`ρ₀ = 2,6`) or `1600/32768 ≈ 4.9%` (`ρ₀ = 4`), giving `|S| ≈ 0.95`. The observed
minima are far lower (`0.54`), so the floor states are markedly non-uniform for **small**
speeds — which is where the danger is, and which is a finite region. The uniform count
is **not** a measure bound and must not be used as one without the matching
equidistribution.

**An alternative that avoids (H) entirely** is the window/gap method that closed the
twin case: choose a window `W` and a residue set `V` uncovered throughout it, and apply
the gap lemma to `A(c,J) ∪ B_m`. That route uses no measure bound at all, and the twin
case showed a measure bound can be outright false there.

## 5. Grades

B-lemma: **PROVED**, re-verified. Reduction for `gcd(E_non) ≥ 3`: **PROVED** (from
LRC(6), which this project owns). The table of §3: **EMPIRICAL**, exhaustive over
`q_ρ ≤ 3`. (H): **OPEN**.
