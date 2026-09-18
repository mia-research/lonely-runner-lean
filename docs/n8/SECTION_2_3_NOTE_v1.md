# §2.3's open item, answered for commensurable speeds

**T. Palelei.** Note v1, 2026-09-18. For folding into a manuscript version after the author's
ruling. **v10 is not edited by this note**; v10 is gate-clean and frozen at commit `c023d10`.

---

## 1. The open item, as v10 states it

> **Fitting the arrangement between the AP locations.** `[OPEN — how the fit feeds each runner's
> reading]` … *"Its about fitting them in between the spaces they can be, so for ap r1 can be 0 to
> <2, r2 can be [1] to <3, their is overlap between them."* … **How the fit decides which runners
> then need the cascade is the step still to be written down** (revision-list item 24).

## 2. The answer, for commensurable speeds

Reduce by `g`, the gcd of the differences, so the speeds are integers `w`. Then:

> **The residue partition.** At a spine instant `t = p/(n·g)` with `p` a unit mod `n`, subject `i`
> is clear of runner `j` exactly when `n ∤ (w_j − w_i)`. Hence subject `i` is lonely at **every**
> one of the `φ(n)` grid instants when its residue `w_i mod n` is **unique**, and at **none** of
> them when some other runner shares it.
>
> `[PROVED — ConstructionN.spine_all_or_nothing (Theorem 4.10); the partition form is
> ResiduePartition.lonely_at_spine_iff_residue_unique and spine_verdict_independent,
> experiments/n8/ResiduePartition_v1.lean, axiom-clean]`
> `[VERIFIED — 32,000 of 32,000 exact, experiments/n8/residue_partition_v1.py]`

**So the fit decides by residue, and the decision is binary and scale-free:**

| subject's residue mod `n` | verdict |
|---|---|
| **unique** among the eight | lonely at all `φ(n)` grid instants — **settled at the grid scale, no cascade** |
| **shared** with another runner | lonely at none of them — **must change scale** |

The verdict does not depend on which spine instant: the right-hand side of the criterion mentions
no `p`. The residues partition the pack once and for all.

**Measured shares.** Over 4,000 random integer arrangements, 32,000 subjects: **40.7%** have a
unique residue and are settled at the grid scale; **59.3%** share one and need the cascade.

**On the cases already in the manuscript:**

| arrangement | `g` | residues | settled at scale `g` | need a new scale |
|---|---|---|---|---|
| `(11,21,22,23,26,34,35,40)` | 1 | `[0,2,3,4,7,7,0,5]` | 21, 22, 23, 40 | 11, 26, 34, 35 |
| `(1,31,75,97,128,160,176,225)` | 1 | `[0,6,2,0,7,7,7,0]` | 31, 75 | the other six |
| `{2,…,7,16}` + subject | 1 | `[0,2,3,4,5,6,7,0]` | 2,3,4,5,6,7 | the pair sharing 0 |

The second line is why `(1, 31, 75, …, 225)` is a hard case: **only two of eight** are settled at
the grid scale. The third is the critical family of `NearAP.lean`, whose entire difficulty is one
sharing pair.

## 3. Why this is the right reference, and it is not the AP

Against an arithmetic progression an arrangement has **deviations**. Against the **grid of scale
`g` an integer arrangement sits exactly** — zero deviation — and all the content is in which grid
points are occupied. `WHICH_GRIDS_ISOLATE_v1` §2 is the reason: writing `u_i = π(i) + n·q_i`, the
`q` part contributes `q_i·p` whole revolutions at `t = p/(ng)` and vanishes mod 1, so **only the
residue `π` is visible**. Global isolation is `π` being a bijection; the partition above is what
`π` says when it is not.

This is the author's own reading (2026-09-18): *"maybe we are not mapping from AP ideals but from
global isolation."*

## 4. What is new here, and what is not

**Not new: the mathematics.** `FRAME_FREE_RESTATEMENT_v1` §2A, 2026-09-11, states and proves it —
*"Runner `i` is lonely at `t = a/n` ⟺ `v_i`'s residue mod `n` is unique among the `n` runners"* —
with the two-line proof and 91,528 triples checked. In Lean it is `spine_all_or_nothing`, which
§7's crosswalk already cites for Theorem 4.10.

**New: the connection.** §2.3 asks *how the fit decides which runners then need the cascade*, and
§2A answers it. The question and its answer have sat in the same repository for a week unjoined.

## 5. What remains open

1. **The incommensurable case.** There is no `g`, no reduction to integers and no residue, so this
   partition says nothing there. §2.3's item is answered for commensurable speeds **only**.
2. **What scale the sharers need.** The partition says *which* runners must change scale; it does
   not say *to what*. That is the cascade's job (§6.10's candidate scales) and is where the open
   part of Existence still sits.
3. **Grid distance does not grade the difficulty.** The minimum displacement making the residues a
   bijection is flat against `R`: 52,001 subject-instances in the hard band `S ∈ [7,8]`, mean `R`
   between 1.41 and 1.44 at every distance from 0 to 7 (`grid_distance_v1.py`). So the residue
   pattern **partitions** the pack cleanly and **does not rank** it. `[EMPIRICAL]`

## 6. Suggested placement

§2.3, after the fit paragraph, replacing the `[OPEN]` tag on the *"how the fit decides"* clause
with `[PROVED — commensurable]` and a pointer to §4.5's Theorem 4.10, keeping the `[OPEN]` for the
incommensurable case. §4.5(c)'s grid paragraph already carries the AP-plus-whole-laps statement in
v10 and is the natural cross-reference.
