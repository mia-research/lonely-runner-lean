# The gap sequence over a transit — where each runner finds its loneliness

2026-09-12. n = 8, individual isolation, threshold 1/8. Base AP `(1,…,8)`, r1 transited.

Artifact: `experiments/n8/ok_gap_sequence_map_v1.py`.

---

## 0. Why the gap sequence is the right object

A runner is lonely at time `t` **iff both of its adjacent gaps are ≥ 1/8**.
`[VERIFIED — 47,904 runner-instants over 499 configurations, 0 disagreements]`

All seven distance constraints collapse to two. At any instant the eight runners are a cyclic
sequence of eight gaps summing to 1, and loneliness is a local property of it. A gap is *shared*,
so closing one costs exactly the two runners bordering it — which is why displacing one runner
disturbs exactly two (`DISTURBANCE_RULE_v1` §1).

BSM returns the loneliness **intervals**, not a yes/no, so it says *where* on the track each
runner achieves its loneliness. That is what this map uses.

## 1. The transfer: space moves from in front to behind  `[PROVED — arithmetic]`

At `t = 1/8` the other seven runners are pinned (r2 at `1/4`, r3 at `3/8`, … r8 at `0`). r1 sits
in the slot between r8 and r2, and its two gaps are:

| r1 | gap **behind** (r8→r1) | gap **ahead** (r1→r2) | sum |
|---|---|---|---|
| 0.1 | 1/80 | 19/80 | **1/4** |
| 0.5 | 1/16 | 3/16 | **1/4** |
| 0.9 | 9/80 | 11/80 | **1/4** |
| **1.0** | **1/8** | **1/8** | **1/4** |
| 1.1 | 11/80 | 9/80 | **1/4** |
| 1.5 | 3/16 | 1/16 | **1/4** |
| 1.9 | 19/80 | 1/80 | **1/4** |

**Speeding a runner up steals from the gap ahead of it and gives that space to the gap behind,
one for one. The sum is fixed.** Slowing it down does the reverse. Both gaps must be `≥ 1/8` and
`1/8 + 1/8 = 1/4` exactly, so both must equal `1/8` — which forces `r1 = 1`. There is no slack
in the slot to spend.

## 2. Where each runner is lonely, through the transit  `[VERIFIED — exact]`

At the start of each runner's first loneliness window: its position, the runners flanking it at
that instant, its two gaps, and which gap is exactly `1/8` — the constraint that had been
blocking it and has just opened.

**`r1 = 1` (the AP)** — every runner lonely at `t = 1/8`, flanked by its index-neighbours, every
gap exactly `1/8`, **both** constraints binding for all eight. Nothing anywhere has slack.

**`r1 = 0.9`** (slowed)

| runner | moment | position | behind | gap behind | ahead | gap ahead | binding |
|---|---|---|---|---|---|---|---|
| r1 | 0.1136 | 0.1023 | r8 | 0.19318 | r2 | 0.12500 | r2 ahead |
| r2 | 0.1250 | 0.2500 | r1 | 0.13750 | r3 | 0.12500 | r3 ahead |
| **r8** | **0.3750** | 0.0000 | **r5** | 0.12500 | **r3** | 0.12500 | both |

**`r1 = 1.5`** (sped up)

| runner | moment | position | behind | gap behind | ahead | gap ahead | binding |
|---|---|---|---|---|---|---|---|
| **r1** | **0.2500** | 0.3750 | **r5** | 0.12500 | r2 | 0.12500 | both |
| **r2** | **0.2812** | 0.5625 | r1 | 0.14062 | **r6** | 0.12500 | r6 ahead |
| r8 | 0.1250 | 0.0000 | r7 | 0.12500 | r1 | **0.18750** | r7 behind |

r3 through r7 are identical in every one of these tables: lonely at `t = 1/8`, flanked by their
index-neighbours, both gaps `1/8`, both binding — unchanged across the whole transit.

## 3. Three things the map shows

**A delayed runner finds new flanking partners.** At the AP r1 is flanked by r8 and r2. At
`r1 = 1.5` it is lonely at `t = 0.25` flanked by **r5** and r2; at `r1 = 0.9`, r8 is lonely at
`t = 0.375` flanked by **r5 and r3**. Once the moment moves, the cyclic order has moved on with
it, and the runner's loneliness is granted by entirely different neighbours.

**The AP is the only configuration where every runner is doubly binding.** There, all eight have
both gaps at exactly `1/8`. Off the AP the disturbed runners become singly binding — one gap has
slack, one is tight. Doubly binding means no room in either direction; it is the same fact as
the zero-width windows, read off the gap sequence.

**The space r1 gives up is received by r8.** The gap ahead of r8 *is* the gap behind r1. As r1
goes `1.0 → 1.1 → 1.5 → 1.9`, r8's gap ahead goes `0.125 → 0.1375 → 0.1875 → 0.2375` — monotone,
and exactly the space taken from r2.

## 4. Status and scope

`[VERIFIED — exact]` §2's tables.
`[PROVED — arithmetic]` §1's transfer and the forced `r1 = 1`.
`[VERIFIED — 47,904 instants]` §0's two-gap criterion.

**Scope.** One base, the AP; one runner transited; six positions tabulated in §2; snapshots taken
at the start of the *first* loneliness window only. The gap sequence has not been tracked
continuously in `t` — only at those moments — so nothing here describes how gaps evolve
*between* loneliness events, or how many order changes occur along the way.

**Not established.** Whether the flanking partners of a delayed runner are predictable; whether
"doubly binding" characterises grids in general or only the AP; anything about two runners moved
at once.

**n = 8 is not proved here, and is not the target here.**
