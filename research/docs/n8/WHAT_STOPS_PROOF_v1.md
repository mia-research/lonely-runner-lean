# What is still stopping a proof — genuine obstacles, mistranslations, and ways in

2026-09-15. After `FRAMEWORK_BOUNDARY_AUDIT_v3` and `A4_SPINE_BLOCKING_v1`. Everything is stated in the framework's objects:
readings read from the subject as slot plus deviation, spine instants, the step the speeds direct, dilation. Script
`experiments/n8/spine_runs_min_runners_v1.py` (output `.out`), exact rationals.

---

## 1. The one thing Existence asks, in these coordinates

> Along the scales the speeds direct, some scale has a spine instant with no runner's reading `r·s_j` within 1 of a multiple
> of 8.

Nothing in that statement is imported: it is Existence (Corollary 6.4 plus the band identity). What stops a proof is whatever
prevents showing it. Below, each thing that has stopped us is sorted by whether it is genuine or a mistranslation.

---

## 2. Mistranslations still in the record (to be retired)

| | where | why it is a mistranslation |
|---|---|---|
| M1 | "lap bookkeeping cannot reach the diagonal" (`TARGETS_v3` §3.2) read as an obstacle to Existence | a limit of the growth-potential method (audit B1, B8), not of the framework |
| M2 | T1: order 5 `R < 4`; T3: `R ≤ 2n − 1` | window bounds on when (audit B1, B2); stronger than Existence |
| M3 | T4 stated with residue periodicity | drift is real-valued; irrational readings behave the same (audit B3, checked exactly) |
| M4 | "the scale rule is unstated" | withdrawn: the step is proved in Lean and fixed by the speeds (audit v3) |

None of these needs more work. They need retiring from the target list.

---

## 3. Genuine obstacles — they come from the framework's own structure

### G1. One scale cannot decide — and what blocks it is closeness to an ideal at a finer lattice  `[PROVED — exact computation]`

For a single scale, the fewest runners whose in-the-way spines together include every odd spine up to `R₀`:

| `R₀` | any runners | no near-sharer deeper than `1/R₀` | no near-sharer at all (spines `3…R₀`) |
|---|---|---|---|
| 7 | 1 | 2 | 2 |
| 15 | 1 | 2 | 3 |
| 23 | 1 | 2 | 3 |
| 31 | 1 | 2 | 3 |

All far below seven. So **no argument confined to one scale can close.** The examples show why. Three runners with no
near-sharer keep every odd spine from 3 to 31 in the way, each taking one residue class of `r` mod 6:
- slot 1, `e ∈ (8/31, 2/7)`: spines 7, 13, 19, 25, 31;
- slot 1, `e ∈ (2/5, 12/29)`: spines 5, 11, …, 29;
- slot 2, `e ∈ (17/27, 19/27)`: spines 3, 9, …, 27.

These readings sit just off multiples of `8/6`. At the scale `D/6` they are **near-sharers**: the arrangement is close to an
ideal whose lattice 6 is dead. The same holds for an exact sharer, which keeps every spine in the way (lattice 1 dead).

**Meaning.** At one scale, spines are held in the way by proximity to a dead lattice at a related scale. This is the
dead-lattice structure (`WHY_IT_PREDICTS_v1` §2), met from the other side. It is not an import; it is the framework's own
ideal-and-relocation picture.

### G2. A step moves every runner by an amount fixed by invariant ratios  `[PROVED — arithmetic]`

A step set by runner `x`, which was `g ∈ (0, 2)` below `8M + 1`, adds `g·(d_y/d_x)` to every other reading `s_y`. The setter lands
exactly on `8M + 1`, clear at every spine (`A4` §4). The ratios `d_y/d_x` are fixed by the speeds and never change across scales.

**Meaning.** Whether the next scale is still held in the way depends on those fixed ratios. Near-rational ratios give drifts that
keep near-sharers near multiples of 8 at the next scale: resonance persists across steps. Every long cascade found is of this
kind (order 5: 318 chains of 25+ moves, all from near-rational ratios, `targets_long_chains_v1.out`). Resonance is genuine,
and it is the same object as G1.

### G3. The ideal's clear instants have zero margin on one side  `[PROVED — the A4 table]`

At spine `r` the runner in slot `≡ −r (mod 8)` sits exactly on the threshold in the ideal. Any positive deviation puts it in the
way (`A4` table: slot 7 at spine 1 for every `e > 0`). So "close to an ideal" does not give "lonely near the ideal's instant"
unless the deviations have the right sign. This is v7's one-sided perturbation (Part II of the development record), now exact.
It is why a near-ideal arrangement must move to another scale rather than borrow the ideal's instant.

---

## 4. How the genuine obstacles fit together

G1, G2 and G3 are one mechanism seen three ways:

- **What holds spines in the way at a scale** is closeness to a dead lattice at a related scale (G1).
- **What decides whether that persists to the next scale** is the fixed ratios through the drift `g·d_y/d_x` (G2).
- **What stops the ideal's own instant from rescuing a near-ideal arrangement** is the zero one-sided margin (G3).

So the proof has to control resonance: how close the fixed ratios are to an ideal with a dead lattice, against how far each
directed step drifts the runners.

---

## 5. Ways in

### W1. The resonance dichotomy at the subject's scale — make G1 quantitative  `[proposed; exact computation first]`

For each lattice `q`, take each runner's depth at that lattice: its distance, times `q`, from a multiple of 8.
- **Either** no runner is within `η` of a multiple of `8/q` for any `q ≤ Q`. Then G1's computation, rerun with those resonant
  pieces excluded, gives the fewest runners needed to hold every spine up to `R₀` in the way. If that exceeds seven for some
  `(Q, η, R₀)`, it is a proved single-scale lemma: a non-resonant arrangement has a clear spine by `R₀`.
- **Or** some runners are resonant at a lattice `q ≤ Q`. Then the arrangement is close to an ideal at scale `D/q`, and the
  dead-lattice criterion and first-live bound apply there.

**First action:** extend `spine_runs_min_runners_v1.py` with the resonance exclusion. It is exact and finite, since patterns
depend on the reading modulo `8q`. Find the `(Q, η, R₀)` frontier.

### W2. The transition across one step, in ratio form — make G2 quantitative  `[proposed]`

Start from each single-scale in-the-way configuration of G1 (a near-sharer plus its companions). Apply the directed step:
the setter lands on the ideal, the others drift by `g·d_y/d_x`. Compute exactly for which ratios the new scale is again held in
the way.

**Conjecture to test:** being held in the way at two consecutive scales forces the ratios within an explicit distance of a
rational with bounded denominator. Iterating, an infinite cascade forces exact rational ratios, a commensurate arrangement.

### W3. The commensurate limit through the ideal — the other half of W1 and W2  `[proposed]`

For an exactly commensurate arrangement the ideal is exact at a scale: first live lattice `≤ ⌊s_max/8⌋ + 1` (proved), and
G3's zero margin is the only thing between the ideal's instants and loneliness. The target is T4's gap bound, stated as: from
the first live lattice, the one-sided margins of G3 cannot hold every spine of the next `c` lattices in the way. This is where
the drift-interval rule (Prop 6.5) works directly, for irrational deviations too.

### What W1–W3 do not do

They do not bound when (M2). They do not count runners against spines as a density (audit B6): G1 is an exact minimum over
patterns, not a share. And they do not split rational from irrational (M3).

---

## 6. Recommended order

1. **W1**, the exact computation. It decides quickly whether a non-resonant single-scale lemma exists, and at what thresholds.
2. **W2** on the configurations W1 leaves: the two-scale transition.
3. **W3** as the target W1 and W2 reduce to.

Retire M1–M4 from the target list (`V8_REVISION_LIST_v1`).
