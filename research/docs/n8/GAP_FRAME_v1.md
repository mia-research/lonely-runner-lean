# The gap frame — loneliness as counting on a conserved quantity

2026-09-13. n = 8, threshold 1/8. Built in the owner's objects: the eight cyclic gaps on the
track. Replaces the seven-difference ("classical") form, which was imported and is not this
framework's object.

---

## 0. The state

At any instant `t` the eight runners occupy eight positions on the circle, cutting it into eight
cyclic gaps `g_1(t), …, g_8(t) ≥ 0`. The state is the gap vector, and it carries a conservation
law:

    SUM_k g_k(t)  =  1        at every instant.        [PROVED — the circle has circumference 1]

(The one exception is a grand return, where all eight runners coincide, there is a single
position, and every gap is 0. Verified to be the only case with all gaps below threshold.)

Each runner sits at a **junction** between two consecutive gaps.

> **Runner `i` is lonely at `t` iff both gaps flanking its junction are `≥ 1/8`.**  `[PROVED]`

*Proof.* The nearest other runner is a cyclic neighbour, so `min_j ‖(v_i − v_j)t‖` is the smaller
of the two flanking gaps. ∎

**There are no end runners.** In the AP at `t = 1/8` the cyclic order is `r8 r1 r2 … r7`, so r1's
junction is flanked by the gaps to r8 and to r2. The speed line has ends; the track does not.

---

## 1. The run identity  `[PROVED]`

Let

    A(t) = { k : g_k(t) >= 1/8 }          the gaps that clear the threshold
    c(A) = number of cyclic runs of A     (c = 0 when A is all eight)

> **Theorem.**   `#lonely(t)  =  |A(t)|  −  c(A(t))`.

*Proof.* A runner is lonely iff its junction has both flanking gaps in `A`, i.e. iff it is an
adjacency inside `A` in the cyclic order. A proper subset `A` splits into `c` cyclic runs; a run
of length `L` contains `L − 1` internal adjacencies, so the total is `|A| − c`. When `A` is all
eight the cycle has no break and all eight adjacencies count, which is `|A| − 0`. ∎

**Verified: 0 violations in 180,000 instances** (6,000 random configurations × 30 instants each,
denominators 8, 16, 64, 105, 256, 1001 — exact rational arithmetic throughout).

### Corollary 1 — the deficiency bound  `[PROVED]`

Let `B = {k : g_k < 1/8}` be the deficient gaps, `b = |B|`. Every run of `A` is preceded by a
distinct element of `B`, so `c ≤ b`, giving

    #lonely(t)  >=  max(8 − 2b, 0).

`b = 0` forces all eight lonely; `b = 1` forces at least six. The bound is a **lower** bound and
is attained when the deficient gaps are pairwise non-adjacent; adjacent deficient gaps share a
blocked runner and leave more runners lonely (observed maxima: `b = 2 → 5`, `b = 3 → 4`,
`b = 4 → 3`, against the bound's `4, 2, 0`).

### Corollary 2 — the φ(8) law, from conservation  `[PROVED]`

All eight lonely `⟺ |A| = 8 ⟺ every gap ≥ 1/8`. With `Σ g_k = 1 = 8 × (1/8)`, equality is forced:
**every gap is exactly `1/8`.** So global isolation is the barycentre of the gap simplex, and
nothing else. The zero-measure fragility of the φ(8) law is this equality case.

---

## 2. What the frame makes visible

Measured spread from the barycentre, `D(t) = Σ |g_k − 1/8|`, alongside the lonely count:

| | `t` | gaps (in units of 1/8) | `D` | lonely |
|---|---|---|---|---|
| AP | 1/8 | `1 1 1 1 1 1 1 1` | 0 | **8** |
| AP | 3/16 | `.5 1 .5 1 .5 1.5 1.5 1.5` | 0.38 | 2 |
| AP | 1/4 | `0 2 0 2 0 2 0 2` | 1.00 | 0 |
| r8→9 | 1/8 | `0 1 1 1 1 1 1 2` | 0.25 | **6** |
| r8→9 | 9/64 | `1 .12 1.12 1.12 1.12 1.12 1.12 1.25` | 0.22 | 6 |
| r8→9 | 1/2 | `0 0 4 0 0 0 0 4` | 1.50 | 0 |

A single deviation never returns the state to the barycentre — `D > 0` always for `r8 → 9` — but
`D = 0.25` with **one** deficient gap still leaves six runners lonely, exactly as Corollary 1
requires. The deviation does not destroy loneliness; it costs the two runners flanking the one
gap it starves.

---

## 3. What this frame does NOT yet give

The identity is a statement about **one instant**. It converts "how many are lonely now" into
counting on the gap vector, exactly and with no measure. It says nothing yet about the
**trajectory** — whether a given runner's junction ever comes to lie inside a run of `A`.

That is the open question in this frame, and it is stated in this frame's own objects:

> **Open.** For each `i`, is there a `t` at which runner `i`'s junction is interior to a run of
> `A(t)`?

## 4. Status

| | |
|---|---|
| §0 conservation `Σ g_k = 1`; the two-gap criterion; no end runners | `[PROVED]` |
| §1 the run identity `#lonely = |A| − c` | `[PROVED]`, 180,000/180,000 |
| §1 Corollary 1, `#lonely ≥ max(8−2b, 0)` | `[PROVED]` |
| §1 Corollary 2, φ(8) law from conservation | `[PROVED]` |
| §3 the trajectory question | `[OPEN]` |

**Scope.** The identity and both corollaries use `n` only through the count of gaps and the
threshold `1/n`; they are stated for `n = 8` and are expected to carry, untested elsewhere.
Grand returns (all gaps 0, `Σ g = 0`) are the one degenerate state and satisfy the identity
trivially (`|A| = c = 0`).

**n = 8 is not proved here.**
