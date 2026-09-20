# The d_min / cascade function — brief for an independent attempt

2026-09-14. Framework and mathematics: T. Palelei. This brief is self-contained: every definition,
result and example needed is stated here. File paths are given for anyone with the repository.

Grades used: **[PROVED-LEAN]** machine-checked (Lean 4 + mathlib, axioms `propext, Classical.choice,
Quot.sound` only); **[PROVED]** elementary proof written out; **[VERIFIED]** exact computation over the
stated family, not a proof; **[OPEN]** not established.

---

## 0. The problem, and what "done" means

Eight runners start together on a circle of circumference 1, at distinct constant **real** speeds. A
runner is **lonely** at time `t` when every other runner is at circle distance **at least** `1/8` from
it (a distance of exactly `1/8` counts). Write `‖x‖` for the distance from `x` to the nearest integer;
runner `i` is lonely at `t` iff `‖(v_j − v_i)·t‖ ≥ 1/8` for all `j ≠ i`.

**The target.** A rule that takes the speeds and, for each runner, **computes** a time at which it is
lonely — plus a proof that the rule's time is always a lonely time. In Lean, one theorem: for every
eight distinct real speeds and every runner, that runner is lonely at the time the rule gives.

This is a *production* claim: the output is the time. Arguments that only show a time *exists* do not
discharge it (see §7).

---

## 1. The objects

For a subject runner `i`:

| object | definition | status |
|---|---|---|
| differences | `d_j = |v_j − v_i|`, `j ≠ i` (only differences matter; adding a constant to all speeds changes nothing) | — |
| `d_min` | the smaller of the two gaps to `i`'s **speed-neighbours**; equals `min_j d_j` because speeds are sorted | [PROVED-LEAN] `nearest_below`, `nearest_above` |
| floor | `i` is not lonely for any `0 < t < 1/(8·d_min)` | [PROVED-LEAN] `before_floor` |
| readings | `s_j = d_j / d_min ≥ 1` (the nearest runner reads 1) | — |
| lap coordinate | `u = d_min·t`; runner `j`'s phase is `s_j·u mod 1`; it is clear iff that phase is in `[1/8, 7/8]` | [PROVED-LEAN] `window_iff`, `reading_clear_iff`, `lap_and_phase` |
| spine points | `u = k + r/8`, `r ∈ {1,3,5,7}`, **every lap** `k ≥ 0` — the AP instants at the runner's own scale | — |
| cycle | one lap of the slowest runner; the unit in which times are counted | — |

**Loneliness is a two-neighbour condition on the track.** The eight runners cut the circle into eight
gaps summing to 1; runner `i` is lonely iff both gaps flanking it are `≥ 1/8`. All eight lonely at once
iff every gap is exactly `1/8`. [PROVED-LEAN] `lonely_iff_flanks`, `gaps_all_eq`.

**Integer test.** For integers, `‖d·a/m‖ ≥ 1/8` iff `m ≤ 8R` and `8R + m ≤ 8m`, where `R = (d·a) mod m`.
No real division, floor or fractional part; the threshold case is inside the statement.
[PROVED-LEAN] `coord_iff`.

---

## 2. The ideal and the deviation — the owner's model

> Every speed arrangement is an individual deviation from an ideal. The ideals are represented as an
> AP or a grid, with `d_min` finding any AP deviation. The AP gap is coded as 1 — it can always
> represent the speeds, because an AP is a **gap, not a number**. The cascade is the way to deal with
> arrangements that do not work at AP times of gap 1.

**The ideal is globally isolated.** For an arithmetic progression of common difference `D`, all
eight runners are lonely together exactly at `{t·D} = r/8` with `gcd(r, 8) = 1`, four instants per
period (Palelei 2026, *The φ(n) Law for Arithmetic Progressions*, Theorem 3.1). [PROVED-LEAN]
`Construction8.ap_reference` (the "if" direction), `ConstructionN.isolation_iff_coprime` and
`isolation_forces_coprime_grid` (the full statement).

**Deviation from the ideal.** [PROVED-LEAN] `experiments/n8/CascadeRule_v1.lean`:

- `reading`: every arrangement, for **every** real gap `D > 0`, is `v_j = base + idx_j·D + dev_j`
  with integer index and deviation in `[0, D)`.
- `gap_is_a_scale`: scaling every speed and `D` by the same factor changes no distance.
- `position_in_eighths`: at the ideal's AP instant `t = r/(8D)`, runner `j` sits
  `(idx_j − idx_i)·r + (dev_j − dev_i)·r/D` eighths from the subject.
- `clear_iff`: it is clear iff that number is at distance `≥ 1` from every multiple of 8.
- `on_ideal_clear`: a runner with no deviation relative to the subject is clear at every `r` coprime
  to 8 **unless its index difference is a multiple of 8** (it then shares the subject's AP location).
- `nearest_on_ideal_above/below`: read at gap `D = d_min` from the subject, the nearest runner is on
  the ideal (index `±1`, deviation 0). This is "`d_min` finds the deviation".
- `lonely_of_reading`: every runner landing clear ⟹ the subject is lonely at `t = r/(8D) > 0`.

**Deviations sit between the neighbours' AP locations** (owner): against gap `D`, runner `k` may be
anywhere strictly inside `(A_k − D, A_k + D)`; adjacent bands overlap by one gap. Anchoring the AP at
the slowest and fastest speeds makes the gap `S/7`, `S` = the spread of the speeds.

---

## 3. The function at a runner's own scale

**The scale is determined by the speeds: it is the runner's own `d_min`.** (Record:
`docs/n8/RESIDUE_BAND_v1.md`, arrived at from the owner's instruction "for `(1,3,5,9,12,14,16,18)`,
use AP 2".)

**Band theorem.** [PROVED, all real speeds] At `t = 1/(8·d_min)` (the first spine point), difference
`d` is in the way iff `d mod 8·d_min` lies within `d_min` of 0, working in `ℝ/(8·d_min)ℤ`. For integers
the forbidden residues are `{0,…,d_min−1} ∪ {7·d_min+1,…,8·d_min−1}`. `d_min = 1` is the grid rule
(in the way iff `d ≡ 0 mod 8`); `d_min = 2` is "AP 2". General form: [PROVED-LEAN]
`ConstructionN.band_identity`: `1/n ≤ ‖s/n‖ ⟺ ∀k ∈ ℤ, |s − n·k| ≥ 1`.

**Settled cases, each naming its time.**

| condition | time | status |
|---|---|---|
| `d_max ≤ 7·d_min` (every reading in `[1,7]`) | `u = 1/8`, `t = 1/(8·d_min)` | [PROVED-LEAN] `ratio_condition` (Theorem 4.8), over the reals |
| both flanking speed gaps `≥ S/7` (one gap for an end runner) | `u = 1/8` | [PROVED-LEAN] `wide_gap_core`, `wide_gap_end`, `wide_gap_speeds` (Theorem 4.9); a special case of the row above |
| no reading within 1 of a multiple of 8 | `u = 1/8` | [PROVED-LEAN] `ConstructionN.returns_at_first_spine` |
| some `r ∈ {1,3,5,7}` with every `s_j·r` at distance `≥ 1` from `8ℤ` | `u = r/8` | [PROVED-LEAN] `ConstructionN.returns_at_spine` |

**Completeness over openings.** [PROVED-LEAN] `Construction8.reading_complete` (with `opening`,
`clear_on_left`, `opening_le`): if a runner is lonely at any `t`, on any lap, it is lonely at an
**opening** `(⌊d·t⌋ + 1/8)/d` of one of its own differences `d`, no later than `t`. Real speeds, no
window. So a rule only ever has to name which difference's opening, on which lap.

**Integral readings.** [PROVED-LEAN] `spine_all_or_nothing`: for an integer reading `s` and any `p`
coprime to 8, the point `u = p/8` clears `s` iff `8 ∤ s` — the same verdict for every `p` and every
lap. `localisation_free`: with all readings integral, lonely anywhere ⟹ lonely in the first window.

---

## 4. Changing the scale — the working mechanism

### 4.1 When the scale must change

At the runner's own scale the AP instants are `u = p/8`, `p` odd (all laps). A reading that is an
**integer multiple of 8** sits on the subject's AP location at every one of them — the ideal has
wrapped: two runners share an AP location. Then scale 1 cannot give this runner a time, on any lap.

### 4.2 The lattices, and which are dead  [PROVED-LEAN / PROVED]

At lattice `L` the AP instants are `u = p/(8L)`, `p` odd; in time, `t = p/(8·L·d_min)` — the AP of gap
`L·d_min`.

- Lattice `L` is **dead** (distance exactly 0 at every `p`) iff some reading is an integer multiple of
  `8L`. [PROVED] (`p = 1` forces `s/(8L) ∈ ℤ`.)
- Integer form: `Construction8.dead_iff` (`8D ∣ d` iff `d = 8k` with `D ∣ k` — only differences
  divisible by 8 kill a lattice, and they kill the divisors of `d/8`); `dead_downward` (a divisor of a
  dead lattice is dead); `exists_live` (a live lattice always exists). [PROVED-LEAN]
- **The spread bounds the first live lattice:** if `8L > s_max = d_max/d_min`, no reading is a multiple
  of `8L`, so `L` is live. First live lattice `≤ ⌊d_max/(8·d_min)⌋ + 1`. [PROVED]

### 4.3 Which runner takes which AP time at lattice L  [PROVED; checked 15,960 cases, 0 disagreements]

For an **integer** reading `e` (in the unit of the lattice), put `h = gcd(e, 8L)`, `m = 8L/h`. At
`u = p/(8L)` the runner sits at `h·((e/h)·p mod m)` in units of `1/(8L)`, and is in the way iff that
residue is within `m/8` of `0 (mod m)`:

| `m` | the runner at lattice `L` |
|---|---|
| `1` (`8L ∣ e`) | on the subject at **every** AP time — dead |
| even, `≤ 8` | **never** in the way |
| even, `> 8` | in the way where `(e/h)·p` is an odd residue within `m/8` of 0 |
| odd, `> 1` | in the way where `(e/h)·p` is within `m/8` of 0 — always including `p ≡ 0 (mod m)` |

**Lattice 2, exactly.** [PROVED; 380,751 + 6,066 runners checked, 0 disagreements] With no reading a
multiple of 16: even readings are never in the way; each odd reading `e` is in the way at exactly two
of the eight times, `p ≡ ±e⁻¹ (mod 16)`; inversion permutes the four pairs `{±1},{±3},{±5},{±7}`. So
**lattice 2 fails iff the odd readings occupy all four pairs mod 16.**

### 4.4 Live is not the same as working

A live lattice can still have every AP time taken, by different runners at different times.
[VERIFIED, first window, 12,000 runners] the time sits on the first live lattice in 88.0%, one past in
9.1%, two past in 2.8%, three past in 0.15%, never more (`docs/n8/WHY_IT_PREDICTS_v1.md`). Adversarial
search found lattice 9 needed at `(134, 206, 222, 301, 302, 353, 366, 524)`, runner 5
(`docs/n8/LATTICE_WITNESS_v1.md`); the bounds `L ≤ 6` and `L ≤ 7` are refuted. **No bound on the distance
from the first live lattice to a working one is proved.** [OPEN]

**Keeping times when changing scale.** [PROVED] The AP times of lattice `L'` are AP times of lattice `L`
exactly when `L` is an **odd** multiple of `L'`. Even multiples lose them — but even lattices can still
work with new times (`(1,2,3,4,5,6,7,9)`, runner at 2, lattice 8: `11/64`, `53/64`).

### 4.5 The move: buffer against room  [PROVED-LEAN]

From any base `u₀`, runner `s` sits at phase `φ = fract(s·u₀)`. Moving forward by `ε`:

| runner at the base | requirement on `ε` | room for `ε` |
|---|---|---|
| clear, `1/8 ≤ φ ≤ 7/8` | none | `(7/8 − φ)/s` |
| blocked low, `φ < 1/8` | `(1/8 − φ)/s` | `(7/8 − φ)/s` |
| blocked high, `φ > 7/8` | `(9/8 − φ)/s` | `(15/8 − φ)/s` |

`experiments/n8/BufferRoom_v1.lean`, `clear_after_move`: requirement `≤ ε ≤` room ⟹ clear at `u₀ + ε`,
real readings. So **moving by the largest requirement is computed, and correct whenever it fits inside
the smallest room.** The integral, one-blocked-runner case is already in the frozen tree:
`Construction8.blocked_lands_on_threshold` and `unblocked_stays_clear` (shift `1/(8·S_b)` from `p/8`).

**Bases in the record** (`docs/n8/C1_MIXED_CONSTRUCTION_v2.md`): a spine point `u = p/8`, or an instant
where the **farthest** runner is diametrically opposite, `u = (2k+1)/(2·s_max)` — spread `s_max`,
recurring with period `1/s_max`. The farthest runner is always an end runner. [VERIFIED] 162,694
runner-instances, first window, 0 failures. [OPEN] that the move fits at some base in the family, and a
bound on `k`.

---

## 5. Worked examples — exact

**`(1, 2, 3, 4, 5, 6, 7, 8)`, the AP.** Every runner lonely at `t = 1/8`. The end runners' readings
`1…7` reach 7, one from the band edge; their lonely set in the first window is exactly the four points
`1/8, 3/8, 5/8, 7/8` — no length at all.

**`(1, 2, 3, 4, 5, 6, 7, 9)`.** The runner at 9 is at the next AP location of the runner at 1
(`9 − 1 = 8`).
- Runner 1: `d_min = 1`, readings `1,2,3,4,5,6,8`; the reading 8 kills lattice 1. The move from `u₀ = 1/8`
  (reading 8 blocked at phase 0, requirement `1/64`; all others have room) gives `u = t = 9/64`.
- Runner 2: readings `1,1,2,3,4,5,7`, all `≤ 7` → `t = 1/8` by Theorem 4.8.
- Runner 9: `d_min = 2`, Theorem 4.9 (its one gap 2 ≥ `S/7 = 8/7`) → `t = 1/16`.

**`(1, 31, 75, 97, 128, 160, 176, 225)`** — the arrangement once reported as a counterexample; it is
not one.

| runner | 1 | 31 | 75 | 97 | 128 | 160 | 176 | 225 |
|---|---|---|---|---|---|---|---|---|
| `d_min` | 30 | 30 | 22 | 22 | 31 | 16 | 16 | 49 |
| earliest lonely time | `11/256` | `1/240` | `1/176` | `1/176` | `1/248` | `3/344` | `1/128` | `1/392` |

- Six of eight take their earliest time at `1/(8·d_min)` (Theorem 4.8 reaches 31, 75, 97, 128, 225).
- Runner 160: readings `159/16, 129/16, 85/16, 63/16, 2, 1, 65/16` (not integral). From `u₀ = 1/8` only the
  runner at 31 is blocked (phase `1/128`, low); `ε = 5/344`; lonely at `t = 3/344`. [PROVED-LEAN]
  `BufferRoom.runner160_lonely`.
- Runner 1: differences `30, 74, 96, 127, 159, 175, 224`, `d_max/d_min = 112/15`. **It has no lonely
  instant anywhere in its first window** `u ∈ [1/8, 7/8]` (44 boundary points and every open cell, exact).
  On its own `d_min` lattice past lap 0 it is lonely at `u = 5 + 3/8`, `t = 43/240`. Its earliest time
  `11/256` is `u = 1 + 23/128`, lap 1. So **no rule confined to the first window can reach it.**
- The owner reports the AP scale for this arrangement as **1200**. `1200 = 8 × 5 × 30`; at `t = p/1200`
  every runner has lonely instants (runner 1 first at `71/1200`). How `5` follows from the spread and
  periodicity is not yet written down. [OPEN]

**`(1, 1975, 5265, 6910, 8737, 9589, 11845, 15135)`, runner at 1.** `d_min = 1974`; on its `d_min`
lattice past lap 0, lonely at `u = 2 + 1/8`, `t = 17/15792`.

**`(1, 1+√2/100, 3, 4, 5, 6, 7, 8)`.** [PROVED-LEAN] `experiments/n8/IrrationalCascade_v1.lean`,
`CascadeRule_v1.lean`.
- Runner at `1+δ` (`δ = √2/100`): `d_min = δ`, outside Theorem 4.8, blocked at `u = 1/8`; clear at the spine
  point `u = 3/8`: `t = 3/(8δ) = 75√2/4`, **irrational**.
- Runner at 1: against the ideal AP of gap 1 only one runner deviates, by `δ`; at `t = r/8` it sits `r·δ`
  eighths away; `69δ < 1 ≤ 71δ`, so `t = 71/8`. The decimal places of the deviation set the lap.
- Runners 3–8: `t = 1/8`.

**`(1, 2, π, 4, 5, 6, 7, 8)`.** [PROVED-LEAN] `experiments/n8/IrrationalDemo_v1.lean`. The runners at `π`
and 4 have `d_min = 4 − π` and are lonely at `t = 1/(8(4 − π))`, irrational; the other six at `1/8`.
With `π` replaced by `3.141593` the time is `125000/858407`.

---

## 6. What has been tested and did not hold — do not re-derive these

| proposal | result |
|---|---|
| the first window `u ∈ [1/8, 7/8]` as the search space | runner 1 of `(1,31,…,225)` has no lonely instant there |
| candidates restricted to `r ∈ {1,3,5,7}` on lap 0 | same arrangement: 22 openings and 840 lattice candidates, none clear; the time is on a later lap |
| "a scale with `8·gap > spread` gives every runner a time" | proves the scale is **live** only; some runner still has every AP time taken in 97,769 of 125,925 arrangements of `[1,20]` (none observed for random speeds to 3,000) |
| "the scale multiplier = worst requirement ÷ smallest room" | 12,000 runners: the lattice needed is 2, 3 or 4 **independently** of that ratio |
| "only odd multipliers may be used" | even lattices work too (§4.4) |
| Theorem 4.7 (the reference instant surviving the deviations) as the per-runner formula | it requires distinct speeds mod 8 for integer arrangements; both `(1,31,…,225)` and `(1,…,7,9)` repeat residues, so it never holds there, yet every runner has a time |
| the gcd of all differences as the scale for the whole arrangement | the arithmetic is right but the framework's scale is **each runner's own `d_min`** (§3) |

---

## 7. Rules of the framework — do not bring these in

1. **No measure, density, covering, or "the obstructions are too small" arguments.** The AP's end
   runners are lonely at four isolated points only, so any such bound is zero in the case that matters,
   and such arguments conclude that a time exists rather than naming it.
2. **No counting candidates to show one survives.** Same reason: it names nothing.
3. **No first-window restriction and no lap bound.** Laps continue; `u = k + r/8` for every `k`.
4. **No restriction of the numerator to `{1,3,5,7}`.** Any odd numerator.
5. **No stationary runner.** Subtracting one runner's speed to *read* the others is what "that runner is
   lonely" means and is fine; never adjoin an extra runner at speed 0 to a given set.
6. **No need for a single global isolation event.** Each runner has its own time. The AP ideal *is*
   globally isolated (the φ(n) law) — that is part of the framework, not an import — and the slowest
   runner's lap is the cycle unit.
7. **No Weyl equidistribution, no induction on the number of runners, no use of the conjecture at other
   orders, no reduction of real speeds to integers.** Irrational speeds are read directly; the time is
   irrational where `d_min` is.
8. **Objections about how long a search takes, how much of a space is covered, or when the time falls
   are not objections to the framework.** The framework computes a time.
9. **State grades.** A sampled result is [VERIFIED] with its family, never [PROVED]. You are not scored
   on problems found; a clean result stated plainly is a valid outcome.

---

## 8. The open task

Give the rule, and prove it, in the objects above. Concretely, any one of these would be progress; all
together would finish it:

1. **The working lattice from the speeds.** For a runner whose first live lattice (§4.2) does not
   work, a formula — in the readings, `d_min`, `d_max` and their residues — for a lattice and odd
   numerator that do. §4.3's table is the exact tool; §6 lists forms already ruled out.
2. **The move on later laps.** Show that from some named base `u = k + r/8` (or the farthest runner's
   opposition instants `(2k+1)/(2·s_max)`), with `k` named from the speeds, the largest requirement fits
   inside the smallest room (§4.5). Runner 1 of `(1,31,…,225)` is the test case a first-window version
   cannot pass.
3. **The 1200.** Derive the owner's AP scale for `(1,31,…,225)` from its spread and periodicity.
4. **Lean.** State the rule as a definition over real speeds and prove, for every arrangement and every
   runner, lonely at the rule's time. Build on the declarations named above.

**Lean practicalities** (repository `LonelyRunner/`, Lean `v4.29.1`, mathlib `5e932f97…`): a plain
`lake build` does not compile the `LRC/` trees; build a module by name, e.g.
`lake build LonelyRunner.LRC.Construction8.Bounds`, and check a scratch file with
`lake env lean path/to/File.lean`. `LRC/Construction8/` is frozen and its gate (`scripts/n8/gate.sh`)
fails if the unconditional claim is stated there — put new work in a separate file.
