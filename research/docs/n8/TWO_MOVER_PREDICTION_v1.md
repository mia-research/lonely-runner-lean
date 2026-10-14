# Two runners moved — what can be predicted, and what cannot

2026-09-12. n = 8, individual isolation, threshold 1/8, base AP `(1,…,8)`. Two runners displaced
together, adjacent and split. A prediction was written down first, tested, failed, diagnosed, and
repaired into an exact rule.

Data: `experiments/n8/out_pair_sweep_v1.csv` (28 pairs, 9,793 joint positions),
`experiments/n8/out_full_sweep_v1.csv` (single-mover reference).

---

## 1. First, the resolution check  `[VERIFIED — exact]`

`SERVICE_DISPARITY_v2` §1 gave fair bands from a step-0.1 sweep and cautioned that they were
"upper bounds at this resolution". **That caution was wrong in direction.** Re-run at 0.01:

| mover | band at step 0.1 | band at step 0.01 | width |
|---|---|---|---|
| r4 | 3.8 .. 4.4 (0.6) | **3.72 .. 4.42** | **0.70** |
| r5 | 4.6 .. 5.2 (0.6) | **4.58 .. 5.28** | **0.70** |

The coarse grid missed the true edges and **understated** the band. Ten of 81 positions break in
each range, all of them outside the band. The bands are real and both are 0.70 wide.

## 2. The prediction, as written before testing  `[REFUTED]`

> Displacing runner `m` disturbs `{m, the neighbour it approaches}` (`DISTURBANCE_RULE_v1`).
> Two movers whose disturbed sets are **disjoint** should therefore not interact: every runner's
> moment should equal its single-mover value, or `1/8` if neither mover reaches it.

| case | configurations | prediction holds | rate |
|---|---|---|---|
| disjoint disturbed sets | 7,192 | 2,741 | **0.381** |
| overlapping | 2,601 | 1,335 | 0.513 |

**Refuted.** Disjointness of the disturbed sets does not make the two displacements independent.

## 3. Diagnosis — the prediction had two halves, one sound and one not

**Half A** — a runner disturbed by *neither* mover keeps `t = 1/8`. Argued to be forced: if each
mover alone leaves that runner's constraints satisfied at `1/8`, both together leave both
satisfied. Measured: **41,606 of 42,092 = 0.9885**. Not forced, so the argument was incomplete.

**Half B** — a runner disturbed by *one* mover keeps its single-mover moment. Measured
**0.7322**, misses split 5,200 earlier and 3,680 later. A runner that has **lost** `1/8` must find
a later window, and where that window falls depends on the whole configuration — including the
mover that did not break its `1/8`. Half B was never sound.

**The 486 exceptions to Half A are all one thing:**

| | |
|---|---|
| moment **earlier** than 1/8 | 486 of 486 |
| runner lies strictly **between** the two movers | 486 of 486 |
| runner **adjacent to both** movers (`m−1` and `m+1`) | 486 of 486 |

Both of that runner's distance-1 neighbours have receded, so its smallest speed difference grows
and it becomes lonely *sooner*. This is the improvement mechanism from `DISTURBANCE_RULE_v1` §2 —
there available only to r1 and r8, because only they have a single distance-1 neighbour. **With
two movers, an interior runner can be improved too**, when both of its neighbours are the movers
and both move away.

## 4. The repair — one exact rule  `[VERIFIED — 42,092 of 42,092]`

A runner's first isolation cannot precede `t = 1/(8 · d_min)`, `d_min` its smallest speed
difference. That bound is forced for every runner. The question is when it is attained.

> **For a runner disturbed by neither mover, the moment is exactly `1 / (8 · d_min)`.**

| | configurations | exact | rate |
|---|---|---|---|
| disturbed by neither mover | 42,092 | 42,092 | **1.0000** |
| disturbed by at least one | 36,252 | 17,444 | 0.4812 |

This subsumes both halves of §2's prediction. An undisturbed runner that still has a distance-1
neighbour has `d_min = 1` and moment `1/8`; a sandwiched one has `d_min > 1` and is earlier. The
sandwiched sub-case alone is **600 of 600 exact**.

## 5. So: can we predict what will happen?

**For the runners neither mover disturbs — yes, exactly**, and that is most of the pack: five or
six of eight in a typical configuration. One quantity, `d_min`, determines the moment.

**For the two or three that are disturbed — no.** The bound `1/(8 · d_min)` still holds but is
attained in fewer than half of them. A disturbed runner has lost the spine instant and its next
window depends on the full configuration; nothing here predicts where it lands.

That split is the same one the whole series keeps producing: what happens *away* from the
disturbance is rigid and forced; what happens *at* it is not yet described.

## 6. Status and scope

`[VERIFIED — exact]` §1's bands; §3's 486 exceptions; §4's rule at 42,092 cases.
`[REFUTED]` §2's prediction, stated before the test.
`[PROVED — arithmetic]` the bound `t ≥ 1/(8 · d_min)`.

**Scope.** One base, the AP. Two movers only. Pair sweep at step 0.1, so `q ∈ {1,2,5,10}`; §1's
check at 0.01 covers two movers and two intervals. No three-mover test. The 0.4812 figure for
disturbed runners is a rate over this population, not a characterisation of when the bound is met.

**Not established.** What determines a disturbed runner's moment. Whether the `d_min` rule
survives three or more movers, or a non-AP base. Why the attainment rate for disturbed runners is
near one half.

**n = 8 is not proved here, and is not the target here.**
