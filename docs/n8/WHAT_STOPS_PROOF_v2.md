# What is still stopping a proof — v2

2026-09-15. Supersedes v1. Corrections after the owner's questions:
- **G1** was about a fixed, arbitrary scale, which the framework never uses. It is not an obstacle to the framework.
- **G2** was a statement about how many steps a cascade takes. By objection ledger Part 4's test that is a false blocker.
- **G3** is about perfect isolation on both flanks, not about positive speeds.

v2 also adds the single-lattice computation for W3, and an assessment of the stable-speed (irrational) proposal. Scripts:
`experiments/n8/g1_examples_determined_v1.py`, `lattice_hold_min_runners_v1.py` (outputs `.out`).

---

## 1. What Existence asks

> The run of lap-completion zones from the bound ends: the scales the speeds direct reach one whose spine instant has no runner
> in the way.

That is Theorem 6.2(c) with Corollary 6.4, already proved in Lean (`lonely_iff_run_ends`). Nothing in v1's "continuous
dilation" description added to it: moving the instant forward multiplies every reading by the same factor, and a runner is in
the way while its reading is within 1 of a multiple of 8 — that is the lap-zone run, in reading units.

---

## 2. v1's G1–G3, re-examined

### G1 — not an obstacle to the framework  `[RECLASSIFIED]`

v1 found configurations that hold every odd spine up to 31 of **one fixed scale** in the way. Run through the determinator
(the exact cascade, `g1_examples_determined_v1.out`):
- **The no-near-sharer triple** (readings 1.27, 1.41, 2.66): with a runner at reading 1 added, it is lonely at the bound
  `t = 1/8` on the subject's own scale, 0 moves. The triple is not in the way at spine 1; v1's count left spine 1 out.
- **A near-sharer (23/3 or 25/3) plus the triple**, which does hold every odd spine 1–31 of scale 1: one move, to scale
  `23/27` (resp. `25/27`), and lonely there at `t = 27/184` (resp. `27/200`).

So G1 says only that the framework cannot stay on one scale when the speeds require another. It never does: every speed can add
a scale requirement, and the cascade follows them. For an exact AP, one scale (its gap) decides.

### G2 — a step count, not an obstacle  `[RECLASSIFIED]`

v1 said near-rational speed ratios make cascades long. That is true: order 5, 300 moves at `R = 1.38`. But the number of steps
is "how long the search takes", ledger Part 4's false-blocker test. Long cascades of this kind end early in time. What remains
genuine in G2 is only the step formula: a step set by `x`, which sat `g ∈ (0, 2)` below `8M + 1`, adds `g·(d_y/d_x)` to every other
reading. That is a tool, not an obstacle.

### G3 — perfect isolation has no slack, on both flanks  `[CORRECTED]`

It is not about positive speeds, the zero speed, or `r_1`. In the ideal at a spine instant every gap is exactly `1/8`
(Theorem 4.2), so both runners flanking the subject sit exactly on the threshold. Any deviation that moves either flank toward
the subject puts it in the way. In the A4 table, read from the subject with deviations in `[0, 1)`:
- the flank above is the slot-7 runner, in the way for any `e > 0`;
- the flank below, moved inward, reads as a near-sharer on the slot-0 side.

The wrap between the fastest and slowest runner is no special boundary: adjacency is mod 8 (Theorem 4.1). G3 is a fact about the
ideal. It rules out one shortcut, borrowing the ideal's instant for a nearby arrangement. It is not an obstacle to Existence.

---

## 3. W3 at one lattice  `[PROVED — exact computation]`

The fewest runners, none within `η` of a multiple of 8, whose in-the-way instants together include every `p/8`, `p = 1…P`
(all integers, the full lattice):

| `P` | `η = 0` | `1/16` | `1/8` | `1/4` | `1/2` |
|---|---|---|---|---|---|
| 8 | 1 | 1 | 2 | 3 | 4 |
| 16 | 1 | 2 | 4 | 4 | 4 |
| 24 | 1 | 3 | 4 | 4 | 4 |

The 4-runner witness at `P = 24`, `η = 1/2` has readings in `(0.6818, 0.6923)`, `(3.9583, 4)`, `(2.6250, 2.7083)` and
`(3.3158, 3.3182)`. These are just off `8/12`, `8/2`, `8/3` and `40/12`: **near-sharers of the finer lattices 12, 2, 3 and 12.**
Every obstruction found at one lattice is closeness to a dead finer lattice. That is the dead-lattice ladder, and it is what
T4's gap bound has to control. Four runners at one lattice is below seven, so W3 must use more than one lattice. The T4 data (gap
at most 3, rational and irrational) says the ladder is short in practice.

---

## 4. The stable-speed proposal for irrational speeds  `[ASSESSED — owner decision]`

**The proposal:** prove in Lean that if a rational truncation of `v` has a lonely instant whose margins exceed the truncation
error, then `v` is lonely. Base it on "openness of `Lonely`" plus `lonely_iff_run_ends` for rational arrangements.

**Facts:**

1. **`Lonely` is closed, not open.** It is defined with `1/n ≤ circDist` (`Iteration.lean:39`). The set of `(speeds, t)` where it
   holds is closed. What is open is strict loneliness, `>`, with a positive margin. The lemma as named is false. The true
   versions are two short statements:
   - (a) strict loneliness at `t` with margin `μ` survives any change of differences smaller than `μ/t`;
   - (b) limits of lonely instants are lonely.
2. **The margin is zero exactly at the ideal.** By G3 every ideal instant has margin 0 on both flanks. So (a) transfers nothing
   near an ideal, which is where the hard arrangements are (near-sharers, one-sided perturbations).
3. **Rational arrangements are not settled at order 8.** For rational speeds, periodicity makes the question decidable arrangement
   by arrangement, but it does not show the cascade always stops. Existence for all integer arrangements at order 8 is open in
   the framework, exactly as for irrational ones. The "`n ≤ 4` instances" are already proved for all real speeds (§8.2) and need
   no transfer. So the proposal transfers from a base that is not established.
4. **The firewall bans it.** v8.2 §6A: *"No measure, density, zero-measure argument, or stability radius."* A truncation-margin
   argument is a stability radius.
5. **The framework does not treat irrationals separately.** The reading is ratio-native: a dilation changes no reading, so decimal
   or non-decimal resolution plays no role, and every rational arrangement is an integer one after a dilation. Construction,
   Localisation, the band identity, drift intervals and the step are all proved over `ℝ`. The exact `a + b√2` run
   (`lattice_witness_irrational_v1.out`) behaved like the rational runs. Specific irrational instances are proved exactly in
   Lean (`IrrationalCascade`).

**Where a stability statement does belong:** computing and certifying specific irrational instances. There, an interval of
speeds with a strictly clear instant certifies every speed in it. That is a verification tool, not a route to Existence.

**Recommendation:** do not build the openness lemma as a route to Existence (facts 1–4). If the owner wants the computational
tool of the last paragraph, it is a separate, small item, and needs the owner's ruling against the firewall row.

---

## 5. Where that leaves the work

- **The genuine open content** is the zone run of §1, unchanged, for rational and irrational speeds alike.
- **Mistranslations retired:** M1–M4 (v1 §2), plus G1 and G2 as obstacles.
- **Native routes:**
  - **T4 / W3:** control the dead-lattice ladder (§3). The obstruction at each lattice is closeness to a dead finer lattice.
  - **W2:** use the step formula `g·(d_y/d_x)` to follow how closeness to a dead lattice changes across a directed step.
