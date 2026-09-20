# Isolation periods along the AP transits — r1 over [1,2), r2 over (1,3)

2026-09-12. n = 8, individual isolation, threshold 1/8. Base AP `(1,…,8)`, one runner moved,
step `1/100`, every runner's isolation **windows** recorded at every position.

Artifact: `experiments/n8/ok_ap_transit_r1_r2_v1.py`.
Data: `experiments/n8/out_ap_transit_r1_r2_v1.csv` (2,392 per-runner rows),
`experiments/n8/out_ap_transit_windows_v1.csv` (29,641 individual windows).

---

## 0. Method

**BSM on the time axis.** Boundary points and open-cell midpoints are evaluated separately.
This is load-bearing at the AP itself, where the two end runners' good sets are four **isolated
points** — a midpoint-only test reports them empty. Control: the script reproduces the AP's
`[4,8,8,6,6,8,8,4]` and a generic position's density `0.130226` against the closed form
`25/192 = 0.1302083` (`TRANSIT_DENSITY_CLOSED_FORM_v2` §2).

**Original time, not scaled.** Reducing a configuration whose moved speed has denominator `q`
stretches the period by `q`, so windows measured in the reduced configuration's own time are
not comparable across positions (`WB_window_trajectories` §0). Every window here is mapped
back: period `P = L/g` in original time, each window scaled by `P`.

**The denominator is reported, never concealed.** A uniform step of `1/100` visits only
denominators dividing 100 — `q ∈ {1,2,4,5,10,20,25,50,100}` — and those are the
small-denominator points (`TRANSIT_FRACTIONAL_v1` §1). `q` is carried in every output row. A
separate Farey-order-16 sweep of a third transit, covering **every** `q ≤ 16`, is used below as
the sampling control.

## 1. Result — each transit has one exact duration floor  `[VERIFIED — exact]`

Define the **binding duration** of a position as `min` over the eight runners of that runner's
**longest single isolation window**, in original time. It answers: at this arrangement, how long
is the most-constrained runner lonely for, at its best opportunity.

| transit | positions | non-integer | binding duration | distinct values |
|---|---|---|---|---|
| **A** — r1 over `[1,2)` | 100 | 99 | **`1/48` = 0.020833** | 1 |
| **B** — r2 over `(1,3)` | 199 | 198 | **`1/70` = 0.014286** | 1 |

One value each, at **every** non-integer position, independent of `q` and of position on the
transit. The single exception in each transit is the AP itself (`r1 = 1`, `r2 = 2`), where the
binding duration is **0**.

Sampling control: the Farey-order-16 sweep of `r8` over `(7,9)` — 158 non-integer positions
covering every denominator up to 16 — also returns a single value, `1/48`. The floor is not an
artefact of the denominators a uniform step happens to visit.

**Contrast with the other observables on the same data.** Along transit A the count runs 4 to
289 and the density 0.0613 to 0.0667; along transit B the count runs 4 to 310 and the density
0.0143 to 0.0229. Count is denominator artefact, density is generic-with-jumps, and the
binding duration is a single rational.

## 2. The mechanism — the fixed part sets the floor  `[PROVED bound, VERIFIED attainment]`

When one runner moves, every **other** runner keeps six of its seven differences. Write `A(S)`
for that runner's fixed part, `S` the six unchanged differences:

    A(S) = { t in [0,1) : ||k t|| >= 1/8 for all k in S }

`A(S)` does not move during the transit. A runner's good set is contained in its fixed part, so

> **its longest window can never exceed the longest component of `A(S)`.**

That bound is forced. What is measured is that the bound is **attained**, and attained
precisely at the runner that binds:

| transit | runner | fixed set `S` | longest `A(S)`-component | observed floor |
|---|---|---|---|---|
| **A** | r2 | `{1,2,3,4,5,6}` | `1/48` | **`1/48`** ✓ |
| | r8 | `{1,2,3,4,5,6}` | `1/48` | **`1/48`** ✓ |
| | r3, r7 | `{1,2,3,4,5}` | `1/20` | `1/20` ✓ |
| | r4 | `{1,2,3,4}` | `3/32` | `3/32` ✓ |
| | r5 | `{1,2,3}` | `1/6` | `1/8` (not attained) |
| | r6 | `{1,2,3,4}` | `3/32` | `23/288` (not attained) |
| **B** | r8 | `{1,2,3,4,5,7}` | `1/70` | **`1/70`** ✓ |
| | r1 | `{2,3,4,5,6,7}` | `1/16` | `1/16` ✓ |
| | r3 | `{1,2,3,4,5}` | `1/20` | `1/20` ✓ |
| | r4, r5 | `{1,2,3,4}` | `3/32` | `3/32` ✓ |
| | r6 | `{1,2,3,5}` | `1/15` | `1/15` ✓ |
| | r7 | `{1,2,3,4,6}` | `1/16` | `5/88` (not attained) |

The bound holds in all fourteen rows. Attainment holds in eleven, and fails only on runners with
**wide** `A`-components, which the sliding constraint has room to clip. It holds on every
**tight** runner, including both minimisers — which is why the floor is exact.

Attainment is not forced. The sliding constraint could in principle clip every copy of the
widest `A`-component; it never does. The reason it has room not to: `A` has period 1 in original
time while the configuration's period is `P ≈ q`, so one period contains `q` copies of `A` at
`q` different phases of the sliding interval, and at least one copy survives intact. This holds
already at `q = 2`.

This is `WB_window_trajectories` §2 — *"one endpoint inherited from the fixed part and never
moving"* — made quantitative: the inherited endpoints are the whole story, and the widest
inherited component is the floor.

## 3. The moving runner is never the binding one  `[VERIFIED]`

| transit | moving runner's longest-window floor | density floor | binding runner |
|---|---|---|---|
| A (r1 moves) | `25/233` = 0.1073 | 0.1136 | r2 and r8 |
| B (r2 moves) | `25/233` = 0.1073 | 0.1136 | r8 |

The runner being displaced is five to seven times better off than the runner that binds, in
both transits, at every position. The cost of a move is paid by **stationary** runners that
share residue structure with it, not by the runner that moves.

This confirms `TRANSIT_MAP_v1` §1 — *"the binding runner is r2 (or r8) throughout — never the
runner that is moving"* — through a different observable, on a different transit, at a
resolution that document did not have.

The moving runner's floor `25/233` is the same rational in both transits. Unexplained, and not
investigated.

## 4. The AP is the only collapse

At the AP the binding duration is 0 while the count is 4: the end runners hold four isolation
**instants** of zero length. Every non-integer position on both transits holds a positive
floor. So along these transits:

- **count** is minimised at the AP (4) and at the mod-8 collision (2);
- **duration** is minimised at the AP alone (0), and is otherwise constant.

A positive duration floor therefore cannot be a universal statement over all configurations —
the AP is its own counterexample. What §1 establishes is a floor on the **open** transit. This
is the measure-versus-count asymmetry standing as open item 3 in `CONCLUSIONS_2026_09_12.md`,
now with exact values on two transits.

## 5. Scope and what is not covered

- **One base** (the AP), **two transits**, **one runner moving** in each. Nothing here covers
  multi-runner displacement, non-AP grids (one grid and one AP-of-step-3 were sampled in the
  Farey run and behaved the same way — `1/48` and `1/144` — but at Q = 12 only), or non-grid
  bases.
- **Step `1/100`** visits only `q ∈ {1,2,4,5,10,20,25,50,100}`. The Farey control covers every
  `q ≤ 16` on a different transit. Neither samples large primes.
- **Attainment is observed, not proved** (§2), and it demonstrably fails on loose runners. The
  argument in §2 for why one copy of `A` survives is a mechanism sketch, not a proof; the
  `q = 1` case shows it is not universal.
- §3's `25/233` coincidence is unexamined.
- Nothing here bounds any count below, and nothing here is a floor over all configurations.

**n = 8 is not proved here, and is not the target here.** It is proved in the literature
(Rosenfeld 2025); what these measurements address is the mechanism.
