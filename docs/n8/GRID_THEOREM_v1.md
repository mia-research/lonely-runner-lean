# A proved theorem for grids, from the residue remainder

2026-09-13. n = 8, individual isolation, threshold 1/8. Follows the owner's observation that the
speed line has no ends — mod 8 the runners sit on a circle — and that the remainder of a speed
over multiples of n is what settles the structure.

---

## 1. Theorem  `[PROVED — arithmetic]`

Let `V` be a **grid**: its reduced residues form a complete system mod 8. Let `g` be the gcd of
all pairwise differences. Suppose **every runner has a neighbour at speed-distance exactly `g`**,
so `d_min = g` for all eight.

> Then **no runner is ever blocked**, and every runner's first isolation is exactly `1/(8g)`.

**Proof.** `g` divides every difference, so for each runner `s = d/g` is a positive integer. By
the band identity, blocked ⟺ `dist(s, 8ℤ) < 1`, and for integer `s` that is `s ≡ 0 mod 8`, i.e.
`d ≡ 0 mod 8g`, i.e. the two runners share a residue mod 8 in reduced coordinates. A grid has all
eight residues **distinct**. So nothing blocks, the bound is attained, and `t* = 1/(8g)`. ∎

Check of the implementation against the theorem: **485 of 485** constructed grids satisfying the
hypothesis (block form, dilations `k = 1,2,3,5,7`).

## 2. What it covers in one stroke

| family | `g` | previously |
|---|---|---|
| the AP `(1,…,8)` | 1 | verified |
| every dilated AP `(k,2k,…,8k)` | `k` | verified, 6 values |
| block grids `(1,…,6,15,16)`, `(1,…,5,30,31,32)`, `(1,2,11,12,21,22,31,32)` | 1 | verified, 97 cases |
| `(1,…,6,159,160)` | 1 | verified |

All of these were separate empirical results. They are **one theorem**, and the proof is four
lines.

## 3. Two corrections it forces

**"The ends sit at the band edge" is AP-specific.** I had generalised it. Over 655 random grids,
the r1–r8 pair is at the edge (`dist = 1`) in only **18**, and **blocked in 0**. The AP is the
special case where the span is exactly `7g`; general grids sit comfortably away.

**The ends are not a worry, and never were.** `d_min` for r1 is one-sided — just `v₂ − v₁` — but
the nearest speed is still a neighbour, so locality holds and the band test applies unchanged. Mod
8 there are no ends at all: in the AP, r1 and r8 differ by `7 ≡ −1`, so they are residue-neighbours
with nothing between them. That is the wrap coupling measured earlier, where displacing r1 downward
delayed r8 across six intervening runners.

## 4. Status

`[PROVED — arithmetic]` §1, for all reals (the grid hypothesis forces rationality of the ratios,
but no step assumes integrality beyond `s = d/g ∈ ℤ`, which the hypothesis supplies).
`[VERIFIED — 485 of 485]` the implementation agrees with the theorem.
`[CORRECTED]` the band-edge claim, now scoped to the AP.

**Not established.** Grids where some runner's `d_min` exceeds `g` — there `s = d/d_min` need not
be an integer and the residue argument does not apply. `(1,…,7,16)` is such a case: r8 has
`d_min = 9` while `g = 1`. The band test still decides it, but not by residues.

**n = 8 is not proved here.** This is a theorem about grids, which are the easy case; the open
first-interval claim of `ANALYTIC_STATUS_v1` is untouched.
