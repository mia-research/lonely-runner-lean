# Turns per lap — a scale correction to the push-out results

2026-09-13. n = 8, individual isolation, threshold 1/8. Corrects the reading (not the figures) in
`R8_INTEGER_LAW_v1`, `R7_R8_PAIR_LAW_v1`, `BLOCK_PUSHOUT_LAW_v1` and `SERVICE_DISPARITY_v2`.

**The point.** Pushing a runner out changes the **fastest** speed in the configuration, so it
changes how many laps that runner completes in a fixed window of time. Tallies counted over a
fixed `t` are therefore not comparable across these families. The comparable quantity is

    turns per lap  =  tally / (v_i · coverage)

---

## 1. The measurement  `[VERIFIED — exact]`

| configuration | tallies r1…r8 | turns per lap r1…r8 | = AP? |
|---|---|---|---|
| **AP `(1..8)`** | `1,1,1,1,1,1,1,1` | `8, 4, 8/3, 2, 8/5, 4/3, 8/7, 1` | — |
| `(1..7, 16)` | `1,…,1,` **2** | `8, 4, 8/3, 2, 8/5, 4/3, 8/7, 1` | **yes** |
| `(1..7, 160)` | `1,…,1,` **20** | `8, 4, 8/3, 2, 8/5, 4/3, 8/7, 1` | **yes** |
| `(2,4,…,16)` = AP × 2 | `1,1,1,1,1,1,1,1` | `8, 4, 8/3, 2, 8/5, 4/3, 8/7, 1` | **yes** |
| `(1..6, 15, 16)` | `1,1,1,1,1,1,1,1` | `8, 4, 8/3, 2, 8/5, 4/3,` **8/15, 1/2** | no |
| `(1..6, 159, 160)` | `1,1,1,1,1,1,1,1` | `8, 4, 8/3, 2, 8/5, 4/3,` **8/159, 1/20** | no |
| `(1..5, 30, 31, 32)` | `1,1,1,1,1,1,1,1` | `8, 4, 8/3, 2, 8/5,` **4/15, 8/31, 1/4** | no |
| `(1..5, 14, 23, 32)` spread | `1,1,1,1,1,` **3,3,4** | `8, 4, 8/3, 2, 8/5,` **12/7, 24/23,** `1` | no |

## 2. Correction A — the lone runner banks nothing per lap

`R8_INTEGER_LAW_v1` R2 says r8's tally is `k = ⌊x/8⌋`, and I wrote that as r8 "collecting `k`
turns while the pack collects one", as though it gained something.

**Per lap it gains nothing at all.** r8 takes exactly **one isolation per lap at every x**, from
8 to 160, identical to the AP. The tally `k` is precisely the number of laps it completes by
`t = 1/8`. R2 is better stated as:

> **r8 is lonely once per lap, always. `k` counts its laps, not its luck.**

The figures stand; the reading of them was wrong. In absolute time r8 genuinely does get `k`
windows to everyone else's one — that is true and is what `SERVICE_DISPARITY_v2` measured — but
it buys that with `k` times the distance travelled.

## 3. Correction B — the adjacent block is *not* "exactly like the AP"

`R7_R8_PAIR_LAW_v1` §1 and `BLOCK_PUSHOUT_LAW_v1` §2 report that at a grid point the pair and
triple families reproduce the AP exactly. That holds on **moment, coverage and tally** — all
three verified — but **not per lap, and the departure is severe.**

At `(1,2,3,4,5,6,159,160)`:

| | r7 = 159 | r8 = 160 |
|---|---|---|
| laps by coverage | 19.875 | 20 |
| tally | 1 | 1 |
| **turns per lap** | **8/159** | **1/20** |
| AP's value | 8/7 | 1 |

**r8 runs twenty laps for a single isolation** where the AP's r8 runs one lap for one. A
twenty-fold collapse, invisible in the tally because the tally is 1 in both.

So the two families are the reverse of how I framed them. The lone pushed-out runner is the one
that stays AP-like per lap; the adjacent block is the one that changes.

## 4. What survives, and the scale check

**Scale invariance holds**, as it must: `AP × 2` reproduces the AP's turns-per-lap exactly. That
is the control for this measurement, and it fires.

**The spread block is a genuine per-lap effect, not an artefact.** `(1,…,5,14,23,32)` gives r6
`12/7` against the AP's `4/3` — r6 really does better per lap, because its `d_min` is 9 rather
than 1. This is the one place where a tally difference and a per-lap difference agree.

**Nothing about moments changes.** The `d_min` rule `t* = 1/(8·d_min)` is a statement about a
time, not a count, and is untouched by all of this.

## 5. Status and scope

`[VERIFIED — exact]` §1's table.
`[CORRECTED]` the reading of `R8_INTEGER_LAW_v1` R2, and the "exactly like the AP" claims in
`R7_R8_PAIR_LAW_v1` §1 and `BLOCK_PUSHOUT_LAW_v1` §2 — figures unchanged, framing withdrawn.
`[control]` scale invariance on `AP × 2`.

**Scope.** Eight configurations. Turns-per-lap computed at the coverage time only, not swept.

**Not established.** Whether turns-per-lap has its own closed form; whether the AP profile
`8, 4, 8/3, 2, 8/5, 4/3, 8/7, 1` — which is `8/i` by index — holds for every grid whose runners
keep `d_min = 1`, or only for the families tested.

**n = 8 is not proved here, and is not the target here.**
