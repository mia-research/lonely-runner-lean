# Displacing one runner pushes others' first isolation into later cycles

2026-09-12. n = 8, individual isolation, threshold 1/8. Base AP `(1,…,8)`, one runner displaced.
Tests the question: when a runner leaves the AP, do the remaining runners reach isolation not
only at different *positions* but in later *cycles*.

Data: `experiments/n8/out_full_sweep_v1.csv` (all eight sweeps, step 0.01, 12,744 runner-rows).
Cycle = one revolution of the unmoved pack, `t = 1`. At the AP every runner's first isolation is
`t = 1/8`, all eight simultaneously.

---

## 1. Answer: yes, to both  `[VERIFIED — exact]`

| first isolation falls in | runner-instances |
|---|---|
| cycle 0 — `t ∈ [0,1)` | 12,382 |
| cycle 1 | 194 |
| cycle 2 | 56 |
| cycle 3 | 28 |
| cycle 4 | 28 |
| cycle 6 | 28 |
| **cycle 12** | **28** |

**362 runner-instances wait beyond the first cycle.** The latest is `t = 12.625` — the
thirteenth cycle — for runner r1 when **r2** is displaced to `1.01`.

So displacing a single runner does not merely move the others' isolation around inside the
cycle. It can push a runner's *first* isolation more than twelve full revolutions of the pack
out.

## 2. Most of it is forced arithmetic  `[PROVED — arithmetic]`

A runner whose nearest speed-neighbour differs by `g` needs `‖g t‖ ≥ 1/8`, and since it starts
at gap 0 this cannot happen before

    t  >=  1 / (8 g)

At `g = 1/100` that is `t ≥ 12.5`, which is the thirteenth cycle. That single inequality
accounts for **336 of the 362**. Nothing is discovered there — bringing two speeds to within
`1/100` of each other means neither can separate by an eighth of a lap for twelve and a half
laps.

The table of the worst cases is entirely this effect, and it is always the displaced runner and
the neighbour it approached:

| mover | moved to | delayed runner | first isolation | gap | `1/(8g)` |
|---|---|---|---|---|---|
| r2 | 101/100 | r1 | 12.625 | 1/100 | 12.5 |
| r7 | 799/100 | r8 | 12.625 | 1/100 | 12.5 |
| r1 | 199/100 | r2 | 12.5625 | 1/100 | 12.5 |
| r3 | 201/100 | r2 | 12.5625 | 1/100 | 12.5 |

**How tight the bound is**, over the 362: exactly attained in **150**, within 5% in **112**,
and **100 land later than the bound**. So near-collision sets the scale but does not determine
the answer.

## 3. The unforced residue: same phase, next cycle  `[VERIFIED — exact]`

**26 instances are delayed past the first cycle without the arithmetic bound forcing it** —
their `1/(8g)` is under 1, so nothing compels them to miss cycle 0.

Every one of them has first isolation at exactly

    t  =  9/8

— the **same phase as the AP's first spine point, one cycle later**. They miss `1/8`, `3/8`,
`5/8` and `7/8` of cycle 0 entirely, and are picked up at `1/8` of cycle 1.

| mover | moved to | delayed runner | first isolation | its gap | `1/(8g)` |
|---|---|---|---|---|---|
| r1 | 93/50 | r2 | **9/8** | 7/50 | 0.893 |
| r1 | 187/100 | r2 | **9/8** | 13/100 | 0.962 |
| r2 | 143/50 | r3 | **9/8** | 7/50 | 0.893 |
| r3 | 213/100 | r2 | **9/8** | 13/100 | 0.962 |

Their gaps are `7/50 = 0.14` and `13/100 = 0.13` — just **above** the threshold `1/8 = 0.125`,
where the bound is 0.89 and 0.96, just short of forcing a miss. So these sit immediately outside
the near-collision regime and are delayed anyway.

This is the direct form of the question asked: the runner reaches isolation at the *same
position in the lap* it would have at the AP, but a whole cycle later.

## 4. Status and scope

`[VERIFIED — exact]` §1's cycle distribution; §3's 26 instances and their common value `9/8`.
`[PROVED — arithmetic]` §2's bound `t ≥ 1/(8g)`.

**Scope.** One base, the AP. One runner displaced at a time, step 0.01, so only denominators
dividing 100. The cycle distribution is a count over this sweep and nothing else; the smallest
gap reachable at this step is `1/100`, so the twelfth cycle is a limit of the sampling, not of
the phenomenon — a finer step would push it arbitrarily far by §2.

**Not established.** Why the unforced 26 all land on `9/8` rather than scattering; whether the
100 instances that fall later than the bound share a mechanism; whether any runner *not*
adjacent in speed to the mover is ever delayed past cycle 0.

**n = 8 is not proved here, and is not the target here.**
