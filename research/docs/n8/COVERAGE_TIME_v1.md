# Coverage time — run until every runner has had its isolation

2026-09-12. n = 8, individual isolation, threshold 1/8. Replaces the cycle-based frame used in
`GRAND_RETURN_v1`, `FULL_SWEEP_v1` and `TRANSIT_PERIODS_v1`.

---

## 1. Why the cycle cannot be the frame

All runners start together at 0. One revolution of the **slowest** runner is the shortest a
grand return could possibly be — every runner must complete at least one lap for all of them to
be back at 0 at once.

But that bound is attained only in special cases, and a grand return need not exist at all.

**The grand return takes exactly `v_min / gcd(v_i)` revolutions of the slowest runner.**
`[VERIFIED — independent search, 599 speed sets, 0 violations]`

It is never fewer than one — the slowest runner must complete a whole number of laps to be back
at 0, and it started there. It is exactly one precisely when `v_min` divides every `v_i`.

| speeds | `v_min` | grand return `T` | revolutions of the slowest |
|---|---|---|---|
| `1,2,3,4,5,6,7,8` (AP) | 1 | 1 | **1** |
| `2,4,6,…,16` (AP × 2) | 2 | 1/2 | **1** |
| `1,2,3,4,5,6,7,16` (a grid) | 1 | 1 | **1** |
| `2,3` | 2 | 1 | 2 |
| `2,3,4,5,6,7,8,9` | 2 | 1 | 2 |
| `3,5,7,11,13,17,19,23` | 3 | 1 | 3 |
| `6,10,15` | 6 | 1 | 6 |
| `1.1, 2,…,8` | 11/10 | 10 | **11** |

Verification note: the first check of this was run with a broken cross-checker, which reported
39 spurious disagreements. Re-run as an independent search — the slowest runner must lap a whole
number of times, so test `T = m/v_min` for increasing `m` — it agrees with the formula on all
599 sets, finds no grand return earlier than one slowest-revolution, and no violation of the
divisibility criterion.

And for **incommensurable** speeds there is no `T` at all: the runners never all return to 0
together, so there is no cycle to normalise by or to enumerate over.

So the cycle is a property of special configurations, not a frame for the problem. The frame
that works for any speeds is the operational one: **run until each runner's isolation is
found.**

## 1a. Two corrections to how §1 was stated

**A grand return is guaranteed for integer speeds.** Integer speeds are always commensurable, so
`T = 1/gcd(v_i)` always exists. The earlier phrasing ("exists only when all speeds are
commensurable") is true but invites the wrong reading: the condition is not a restriction on
integer configurations, only on real ones.

**The grand return is the shortest period of the ABSOLUTE pattern, not of the isolation
pattern.** Isolation depends only on relative positions, and those can repeat sooner:

| speeds | grand return `1/gcd(speeds)` | isolation period `1/gcd(differences)` |
|---|---|---|
| `3, 5` | 1 | **1/2** |
| `1,…,8` (AP) | 1 | 1 |
| `1.1, 2,…,8` | 10 | 10 |

For `(3,5)` at `t = 1/2` both runners sit at `1/2` — the same relative configuration as at
`t = 0`, so the isolation pattern has already repeated while the absolute one has not. The two
coincided in every configuration in these sweeps, which is why nothing reported is affected, but
`1/gcd(differences)` is the correct period for isolation and it is the one the scripts use.

## 1b. Irrational speeds: no grand return, and coverage exceeds one revolution
`[VERIFIED — floating point, precision caveat below]`

With incommensurable speeds there is no grand return at all, isolation still occurs, and the
search simply runs until every runner has been covered. Coverage is then **not** bounded by one
revolution of the slowest runner:

| speeds | coverage, in revolutions of the slowest | last covered |
|---|---|---|
| `1,…,8` (AP, control) | **0.12500** | all eight |
| `1, √2, √3, √5, √6, √7, √10, √11` | **1.97214** | r8 |
| `1 + 1/(10π), 2,…,8` | 0.64903 | r1 |
| `1 + 10⁻⁴√2, 2,…,8` | 0.62511 | r1 |
| `1, π, e, 3√2, 5.1234…, 6.7182…, 7.3890…, 9.8696…` | 0.31584 | r2 |
| `1,…,7, 8 + 10⁻³√2` | 0.37500 | r8… r1 |

The control reproduces the exact value `1/8` on the AP, so the float engine agrees with the
exact one where both apply.

**The AP's coverage is fragile.** Its `1/8` is achieved at a zero-width instant, so *any*
displacement destroys it: both small irrational nudges above land at ≈ `5/8`, a factor of five
worse, and the size of the nudge (`10⁻⁴` against `3×10⁻²`) barely matters. Observed on two
configurations only — the larger rational displacements `r1 = 1.1` and `1.5` give `0.498` and
`0.422`, not `5/8`, so this is a small-`ε` observation and not a general one.

**Precision caveat.** §1b is floating point. Near-degenerate constraints could be misclassified;
the tolerance is `10⁻¹²` on the threshold test. The rational rows elsewhere in this file are
exact.

## 2. Coverage time  `[VERIFIED — exact]`

**Coverage time** = the first `t` by which *every* runner has been individually isolated at
least once. Reported in revolutions of the slowest runner, `t · v_min`, which is scale-free.

| configuration | coverage `t` | in slowest-revolutions | last runner covered |
|---|---|---|---|
| **AP `1..8`** | **1/8** | **0.1250** | **all eight at once** |
| grid `1..7,16` | 1/8 | 0.1250 | seven at once |
| `r8 = 9` | 9/64 | 0.1406 | r1 |
| `r1 = 1.5` | 9/32 | 0.4219 | r2 |
| `r1 = 1.1` | 125/276 | **0.4982** | **r1 (the mover)** |
| primes `3,5,7,11,13,17,19,23` | 3/32 | 0.2812 | r7 |
| random `2,5,9,14,20,27,35,44` | 17/264 | 0.1288 | r1 |
| random `1,4,6,11,17,23,30,41` | 9/136 | **0.0662** | r3 |

Three things.

**The AP covers all eight runners at a single instant.** `t = 1/8` — the first spine point,
1:30 on the clock — is simultaneously the first isolation of every runner. Nothing is staggered.
That is the rigidity, measured on this observable.

**Displacing a runner roughly quadruples the coverage time**, `0.125 → 0.498` at `r1 = 1.1`, and
the **mover is the last to be covered**.

**The AP is not the fastest.** Both random sets cover sooner than the AP — `0.0662` and
`0.1288` — so early coverage is not what the AP is extremal for. What it is extremal for is
covering everyone *at once*.

## 3. A correction to `GRAND_RETURN_v1` §4

That file says the displaced runner is "the safest runner in the configuration", on the evidence
that its longest window is about five times the stationary runners' (`25/233` against `1/48`).

**On coverage time it is the worst.** At `r1 = 1.1` the mover is the last runner covered, at
`0.4982` slowest-revolutions. Both measurements are correct and they are about different things:
the mover waits longest for its first isolation, and then gets the longest ones. "Safest" was an
unqualified word on a single observable and should not have been written.

## 4. What this makes the target

LRC(8) is exactly the statement that **coverage time is finite for every configuration**. The
count floor and the duration floor are properties of one period; coverage time is the quantity
the conjecture is about, and it is defined without a period — so it survives irrational speeds,
where count-per-period is undefined. That is the asymmetry standing as open item 3 in
`CONCLUSIONS_2026_09_12.md`, and coverage time does not have it.

No bound is proposed here. Eight configurations is not a sample.

## 5. Status and scope

`[VERIFIED — 599 sets, independent search]` §1's revolution count `v_min/gcd(v_i)` and the
divisibility criterion.
`[VERIFIED — exact]` §2's eight rows.
`[CORRECTED]` §3.

**Scope.** Eight configurations, all with rational speeds, all but two derived from the AP.
Coverage time has not been swept across any transit, related to the duration or count results,
or tested on irrational speeds — where it is defined but not computable by the exact method used
here.

**n = 8 is not proved here, and is not the target here.**
