# The transit frame — what the n = 8 mapping is for, and what to measure

2026-09-12. n = 8, individual isolation. Written to fix the frame of the mapping series, and
to review the series against it. No claim here is promoted; §4 adds one measurement.

---

## 1. The frame

**n = 8 is already known to hold.** Rosenfeld 2025 (his `k = 7`) settles it by a 27-prime
search. What is absent is not a verification — it is a **mechanism**. The target of this work
is to understand *why* every runner reaches individual isolation, not to establish again that
it does.

**The grid is the one place the mechanism is known in closed form.** A grid — `n` speeds whose
reduced residues form a complete system mod `n`, `n` being the number of runners — is globally
isolated at exactly `φ(n)` instants `t = p/(ng)`, `gcd(p,n) = 1`. Every runner is lonely, at
the same instants, for a reason that is written down. The AP is the grid with all deviations
zero.

**The programme is the transit.** Move from the grid to another arrangement and watch what
happens to **individual** isolation along the way. Global isolation is not the quantity: it
dies at the first deviation, and that is expected and uninformative. Individual isolation never
dies. So there is nothing to explain about loss, and everything to explain about **change** —
where the isolation goes, what appears in its place, and what carries the property once the
`φ(n)` reason is gone.

Whether the map becomes a proof is downstream. The understanding is the target.

### 1a. What this frame excludes

The old small-`n` machinery does not answer n = 8, which is why this frame exists. Treat the
following as a signal of drift back, not as progress:

- **Grid distance `k` as an explanatory variable.** `MECHANISM_REVIEW_v1` §1 already killed it
  as a predictor (see §3 below) and then kept it as the organising frame.
- Modulus criteria, covering and union bounds, denominator routes, prime filtering.
- **Floor-hunting.** That the count never reaches 0 is the known part. Searches that re-verify
  it locate extremal structure; they do not address the mechanism.

## 2. What to measure: BSM, and duration

**BSM is the method of preference, and it is not only a better predicate.** The Boundary Set
Method evaluates boundary points and open cells **separately**, because a single constraint's
bad set is the *open* interval between its boundaries. A midpoint-only test loses every
isolated witness where the gap equals `1/n` exactly — which is precisely the AP's own witnesses.

A run of this error is on the record in this session: an open-cell-only implementation reported
the AP's two end runners at count **0** instead of 4, because their entire good set is four
isolated points. The corrected run reproduces `[4,8,8,6,6,8,8,4]` and the reserve profile
`0,4,4,2,2,4,4,0`.

**BSM returns intervals, so it gives isolation duration, not just existence.** Duration is the
observable the transit frame needs, and §4 shows why.

## 3. Review of the transit series against this frame

Reading order of the series: `TRANSIT_MAP_v1` (the origin — vary one runner's speed toward its
neighbour and map every runner's isolation) → `TRANSIT_MAP_FULL_v1/v2` → `RECOVERY_LAW_v1/v2` →
`TRANSIT_FRACTIONAL_v1` → `WN_offap_displacement_map` → `MECHANISM_REVIEW_v1` →
`WB_window_trajectories` → `TRANSIT_DENSITY_CLOSED_FORM_v1/v2`.

### 3a. `MECHANISM_REVIEW_v1` M3 is stale, and its scope is inflated

`MECHANISM_REVIEW_v1.md:43` heads the item **"A move takes the spine, not the reserve"** and
`:46` concludes **"The reserve is conserved on average; only the spine is transferred."**

The evidence at `:44` is "3,657 runners that **kept** the spine across a move". Runners that
**lost** the spine are excluded from the statistic — and those are exactly the runners whose
reserve decides whether anyone reaches the floor. The headline covers all runners; the
population covers only the safe ones.

The finding on the excluded population points the other way. `CONCLUSIONS_2026_09_12.md` §4
(commit `5357a97`) now records it: for spine-losers reserve is **created**, and a zero-reserve
runner lands on 2 rather than 0 because of that compensation, not because of prior reserve.
Independently reproduced here — 2,284 spine-losing runners over 1,142 single moves off 1,304
grids in `[1..20]`: reserve up 1,607, same 477, down 200; the twelve with reserve 0 beforehand
landed at counts 4, 6, 8, 12.

**M3 should be re-scoped to spine-keepers and its headline withdrawn.** As written it states
the opposite of the mechanism, on the population that matters.

### 3b. `MECHANISM_REVIEW_v1` contradicts itself on `k`

§1 kills grid distance as a predictor — over 3,000 random single moves, `Δk = −1/0/+1` give
count-down rates 29.6% / 30.4% / 29.5%, indistinguishable — under the heading
**"'Grid distance predicts what a move does.' False, and it was a standing candidate
mechanism."**

M5 (`:60`) and §3 then use `k` to bracket the result: **"The danger band is `k = 1..4`"**, with
"both flanks safe". Killed as a predictor in §1, retained as the frame in §3. This is the
clearest instance of §1a's drift in the series.

### 3c. The later documents grade the transit work against the floor

`TRANSIT_DENSITY_CLOSED_FORM_v2` §4 is careful work — a scoped null with a firing control,
stating object, class of observable, power and scope. But its criterion is whether density
**localises the count floor**, and the title is "and why it does not reach the n = 8 object".
Under §1 the floor is not the object and the count is not the target. A `[PROVED | Weyl]`
closed form for the transit density (`25/192` at the endpoint, `853/6720` and `941/6720`
interior, with the exact factorisation `(3/4)·|G_fixed|` for non-moved runners) is a mechanism
result about the transit. It is filed as a failure to reach something it was not aimed at.

The §4 null stands exactly as scoped — density's argmin-rank carries no information about where
the count floor sits. That is a statement about floor localisation, not about the usefulness of
duration.

### 3d. Two documents appear to contradict each other and do not

`TRANSIT_MAP_v1` §1: across a transit "the minimum is flat: mean 0.0653, min 0.0613, max
0.0667, spread 0.0054".

`TRANSIT_FRACTIONAL_v1` §3: "**The transit is not a smooth curve.** Adjacent positions differ by
an order of magnitude — `5/48` gives 137 while `1/8` gives 21."

Both are correct. The first measures **duration**, the second **count**. `TRANSIT_FRACTIONAL_v1`
retracts "the transit shape implied by `TRANSIT_MAP_FULL_v2` §1 and `MMIN_RETRACTION_v1` §4"
but does not name `TRANSIT_MAP_v1`, and the reconciliation is not stated anywhere in the series
until `TRANSIT_DENSITY_CLOSED_FORM_v2` §3 — where it arrives as part of a retraction rather
than as a finding. §4 below states it directly.

### 3e. What the series has that is mechanism, and should be built on

- **`WB_window_trajectories` §2–§3.** A window is the intersection of a fixed `A`-component with
  a sliding bad interval: **one endpoint inherited from the fixed part and never moving, the
  other sliding until it clamps at the `A`-boundary**, after which a new window nucleates in a
  different component. And §3's account of the AP: at the AP the bad intervals close `A`'s
  components down to single points, so any perturbation reopens them. This is the transit
  mechanism at the level of individual windows, and it explains the measure jump rather than
  recording it.
- **The spine/reserve exchange**, in its corrected form (§3a): losing the spine creates reserve
  on a finer 2-power lattice.
- **`TRANSIT_DENSITY_CLOSED_FORM_v2` §2's closed form**, read as a transit result.

## 4. Duration is the comparable observable; count is not  `[VERIFIED — exact, one transit]`

Artifact: `experiments/n8/ok_transit_duration_v1.py`. Base AP `(1,…,8)`, runner 8 transits
`8 → 9` in steps of `1/24`, 25 positions, exact `Fraction`, counts and measures taken on the
reduced integer configuration, BSM throughout.

| `r8` | denominator | min count | min duration |
|---|---|---|---|
| `8` (the AP) | 1 | 4 | **0** |
| `193/24` | 24 | 71 | 0.065625 |
| `65/8` | 8 | 25 | 0.065625 |
| `25/3` | 3 | 12 | 0.067172 |
| `17/2` | 2 | 10 | 0.064583 |
| `26/3` | 3 | 14 | 0.062862 |
| `211/24` | 24 | 85 | 0.065625 |
| `9` | 1 | 2 | 0.028571 |

Over the 23 interior positions: **min count ranges 10 to 85, a factor of 8.5; min duration
ranges 0.0629 to 0.0672, a spread of 7%.** The count tracks the denominator of the moved speed
and nothing else — `193/24` and `17/2` give counts 71 and 10 at the identical duration
`0.065625`.

> **Along a transit the duration is flat and the count is denominator artefact.** Counts at
> different positions of a transit are not comparable; durations are.

The two endpoints are the events. At the AP the duration is 0 — the tiling collapse of
`WB_window_trajectories` §3. At `r8 = 9`, where r1 and r8 collide mod 8, duration drops to
0.0286, below every interior value.

The popcorn structure survives in duration but with small amplitude: small-denominator interior
points dip (0.0629 at `26/3`, 0.0646 at `17/2`) against the generic `0.065625`. Same phenomenon
as the count, four orders of magnitude smaller in relative terms.

**Scope.** One base, one runner, one transit, 25 positions at resolution `1/24`. Not tested on
non-AP bases, other runners, multi-runner transits, or finer resolution — the resolution point
of `TRANSIT_FRACTIONAL_v1` §1 applies to this table too, and `1/24` samples denominators
dividing 24 only.

## 5. Status

`[FRAME]` §1, §2 — direction and conventions, not claims.
`[VERIFIED — exact, one transit]` §4, scope as stated.
`[REVIEW]` §3a–§3d: defect claims, each quoting its sentence with file and line.
`[UNCHANGED]` Everything in `CONCLUSIONS_2026_09_12.md` §2's proved list.

**n = 8 is not proved here, and is not the target here.** It is proved in the literature; the
mechanism is what is missing.
