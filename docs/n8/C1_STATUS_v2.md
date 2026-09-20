# C1 — where it stands

2026-09-15, revising `C1_STATUS_v1`. **C1 is not proved.**

C1: every runner's isolation space empties at some instant. Normalised, with `d_j` the seven
differences at the subject, `d_min` the least of them and `s_j = d_j/d_min` the reading:

> find `u ∈ [1/8, 7/8]` with `‖s_j u‖ ≥ 1/8` for all seven.

`s_1 = 1`, which is what fixes the window to `[1/8, 7/8]` — one lap of the nearest runner.

---

## 0. What this file is, and an attribution correction

`C1_STATUS_v1` §1 puts the settled share at **31.4%** and §4 says of mixed readings that "nothing
is closed here beyond the ratio condition and the near-collision trigger of window-widening".

**Both were already superseded by the owner's own later files, before this session began.**

- `SKETCH_v6` §7b, "Reach": the four instants `u = p/8` name a location and a time for **about 72%
  of runners**, with 25.3% / 27.6% / 29.7% naming none of the four across three spans. §7b also
  gives the mechanism — the four points stand or fall together exactly when the reading is
  integral, so a *mixed* reading is precisely where they come apart and `p = 3` becomes a genuinely
  different test from `p = 1`.
- `C1_MIXED_CONSTRUCTION_v1` §2: **97.5% settled** at span 600, stated there explicitly against
  v1's 31.4%, with the open population defined as *mixed reading and `d_max > 7·d_min`* — the same
  set this file calls the residual.

Earlier in this session I re-measured the spine against mixed readings, got 77.6%, and reported it
as a correction nobody had made. It had been made, in §7b, and the residual had been delimited in
`C1_MIXED_CONSTRUCTION_v1` §2. **That framing is withdrawn.** The re-measurement is an independent
confirmation of §7b at five spans on 12,000 instances, and nothing more.

What follows in §1–§3 is what this session adds on top of those files. §4 is a v1 correction that
does stand.

## 1. The ratio condition is not a separate route  `[PROVED]`

**Claim.** If `d_max ≤ 7·d_min` then `u = 1/8` clears the subject.

*Proof.* The hypothesis is exactly `s_j ∈ [1, 7]` for every `j`. The nearest multiples of 8 to such
an `s` are 0 and 8, at distances `s ≥ 1` and `8 − s ≥ 1`. So `dist(s, 8ℤ) ≥ 1`, hence
`‖s · 1/8‖ = dist(s, 8ℤ)/8 ≥ 1/8`. Every `s_j` is clear at `u = 1/8`. ∎

The bound is sharp at both ends: `‖s/8‖ = 1/8` exactly at `s = 1` and at `s = 7`, so the ratio
condition cannot be loosened by any amount. A sweep of `[1,7]` at step `1/10000` returns `1/8` as
the worst value, and 400,000 random seven-term readings in `[1,7]` give no exception.

**Corollary.** If all four spine points are shut then `d_max > 7·d_min`. Measured first — 3,396 of
3,396 instances with all four shut had `d_max > 7·d_min`, no exceptions — then proved.

**Why it matters.** `C1_STATUS_v1` §1 lists the ratio condition (29.8%) and the spine as separate
rows and adds them. They are not independent: the ratio condition is a *subset* of the spine's
reach. `C1_MIXED_CONSTRUCTION_v1` §2 already treats the two as disjoint routes in its "On
everything" table (68.1% + 29.3%); the two numbers are still correct as stated there, because that
table's first row is the move construction rather than the spine, but the ratio-condition row is
reachable by the spine alone and the relationship was not recorded.

## 2. When a single runner shuts the whole spine  `[PROVED]`

**Claim.** A single `s` shuts all four spine points iff `dist(s, 8ℤ) < 1/7`.

*Proof.* `s` shuts `u = p/8` iff `‖s p/8‖ < 1/8` iff `dist(sp, 8ℤ) < 1`. Write `s = 8k + e` with
`|e| = dist(s, 8ℤ) ≤ 4`; then `dist(sp, 8ℤ) = dist(ep, 8ℤ)`. If `|e| < 1/7` then `|ep| < 1` for
every `p ≤ 7`, so all four are shut. Conversely, `p = 1` shut gives `|e| < 1`, so `7e ∈ (−7, 7)` and
`dist(7e, 8ℤ) = |7e|`; `p = 7` shut then forces `|7e| < 1`. ∎

Verified 1,396 of 1,396, no falsifiers in either direction.

**Relation to what is already recorded.** `C1_MIXED_CONSTRUCTION_v1` §4 observes that the move
construction's failures carry "a runner at distance **exactly 0** from a multiple of 8 —
`s_j ≡ 0 (mod 8)`". This claim is the spine's version of the same neighbourhood, with the exact
radius: not distance 0, but distance below `1/7`, and for the spine rather than for the move. It is
also the band the endpoint-killing calculation produced independently, at density `1/28`.

**Where it sits.** Of the instances with all four spine points shut, the *minimum* number of
readings that shut them is 1 in **56.0%** of cases, 2 in 9.0%, 3 in 20.9%, 4 in 14.0% (12,800
runner-instances, four spans). This claim characterises the 56.0% row exactly.

*(An earlier count in this session gave 41.1 / 10.0 / 23.4 / 25.5. That was **greedy** — for each
spine point it took the first reading that shut it — and so over-stated the number needed.
Withdrawn; the figures above are true minima.)*

The other three rows are now finite rather than open-ended: see `SPINE_PATTERNS_v1`, which shows a
single reading's shut-set is one of ten subsets of `{1,3,5,7}` and that there are exactly **eleven**
minimal ways for a collection of readings to shut all four, never using more than four readings.

## 3. The lonely count is never 7  `[PROVED]`

In `GAP_FRAME_v1`'s convention — eight cyclic gaps `g_1…g_8 ≥ 0`, one per runner, zeros permitted —
let `A = {k : g_k ≥ 1/8}`. If `|A| = 8` the eight gaps are each `≥ 1/8` and sum to 1, so each is
exactly `1/8` and all eight are lonely. If `|A| ≤ 7` then `A` is a proper subset, so `c(A) ≥ 1`, and
the run identity gives `#lonely = |A| − c(A) ≤ 6`.

> **The count lies in `{0,…,6} ∪ {8}`. It is never 7,** and it is 8 only at the barycentre of the
> gap simplex, which is `GAP_FRAME_v1` Corollary 2.

Exhaustive over all 12,870 eight-subsets of `[1,16]`: sizes `{0,1,2,3,4,5,6,8}` occur, 7 does not.
This is a corollary of the run identity, and it sharpens Corollary 1 — the bound
`#lonely ≥ max(8 − 2b, 0)` has no companion value at 7 for the count to take.

**A retraction.** Earlier this session I reported that the run identity "over-predicted at 685 of
46,204 instants" and proposed `GAP_FRAME_v1` carry a qualifier restricting it to lonely
*positions*. **Withdrawn.** The mismatch was in my check, which built `k` gaps from `k` distinct
positions; `GAP_FRAME_v1` §0 says eight gaps with zeros permitted. Re-run in the file's own
convention the identity has **0 violations in the same 46,204 instants**. Two runners at one point
have a zero gap between them and so both already fail the two-gap criterion. `GAP_FRAME_v1` is
correct as written and needs no change.

## 4. The first-window demand is not where the difficulty lives

C1 as stated asks for `u` in the **first** window. LRC asks only that the runner be lonely at *some*
time, which in these objects is `u ∈ [k + 1/8, k + 7/8]` for *some* lap `k` of the nearest runner.
C1 is therefore stronger than needed, and the relaxation to "some `k`" is free.

For integral readings the two are identical — the reading is 1-periodic and `s_1 = 1` confines
every isolation instant to the first window mod 1 (`Construction8.localisation_free`). v1 §4 says
that off integrality the localisation is "a genuine extra demand", and as a statement about logical
strength that is correct.

**It is not where the difficulty lives.** Over 12,000 runner-instances at five spans, mixed and
integral, the first clearance was in lap 0 in **every** case; no instance needed `k > 0`. A second
run on an independent seed, posed differently — clear in the first window, against clear anywhere
in a full period — agrees on all 12,800 of its instances, with no runner clear somewhere but not in
the first window. Adopting the relaxation is right on principle and costs nothing, but it does not
open the residual.

## 5. The spine and window-widening are complementary  `[VERIFIED — exact]`

On `SKETCH_v6` §7d's own worked case, speeds `(1, 1+δ, 3, 4, 5, 6, 7, 8)` with `δ = √2/100`,
at 400 digits:

| | §7d's treatment | spine points alive |
|---|---|---|
| **r1** | the window-widening lemma reaches it — `h = 1`, `m = δ`, fifty-three full periods inside the window | **none** |
| **r2** | "the case the lemma does **not** reach … the general shape rather than an exception" | **`p = 3` and `p = 7`** |

`p = 3` clears r2 with margin `+0.0495`; `p = 7` clears it at exactly `1/8`, which is the nearest
runner `s_1 = 1` sitting on the threshold — a boundary point admitted by the closed comparison, not
a rounding artefact. Stable at 100 and 400 digits. r1's four margins are `−0.0920`, `−0.0920`,
`−0.0959`, `−0.0221`, none near the threshold.

Nothing in §7d is false: the lemma does not reach r2, and having a commensurable sub-pack is the
special circumstance *for the lemma*. What this adds is that the lemma is not the only instrument,
and on this example the two are exactly complementary — each reaches the runner the other misses.
§7d reads as though r2 is unreached outright, and it is not.

## 6. Status

`[PROVED]` §1's claim and corollary; §2's `1/7` characterisation; §3's never-7. Plus the pieces
named in v1 §5, unchanged.

`[VERIFIED]` §4's lap-0 result (12,000 instances, five spans, plus 12,800 on a second seed);
§5's complementarity, exact at 400 digits; §3's exhaustive 12,870.

**`[WITHDRAWN]`** the run-identity qualifier (§3); the framing of the spine's mixed-reading reach as
a new correction (§0) — it is `SKETCH_v6` §7b's result, re-measured.

**`[OPEN]` C1.** The residual is a mixed reading with `d_max > 7·d_min` in which the spine is shut —
the population `C1_MIXED_CONSTRUCTION_v1` §2 already delimits, where the move construction runs at
97.0–97.4% and the remaining **2.5%** is unsettled. That file's §3 states the gap precisely and it
is unchanged by anything here: the construction's feasibility is *checked per case, not
characterised*, so it is a construction with a measured hit rate rather than a lemma. §2 above
characterises one row of the shut set exactly; the two-, three- and four-runner rows are not
characterised.

**n = 8 is not proved.** What closes a case is a *named* instant. The residual is settled only by
searching, and no search produces a formula, however many instances it clears.

---

Artifact: `experiments/n8/spine_reach_v1.py` — pre-registers four quantities with falsifiers, all
four empty. Note its Q1 duplicates `SKETCH_v6` §7b and is a confirmation, not a new measurement.
