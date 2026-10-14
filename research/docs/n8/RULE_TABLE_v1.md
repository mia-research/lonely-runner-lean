# The rule table for door 4: what is derived, what is fitted, and why fitting does not converge

2026-09-18. Artefacts: `experiments/n8/rule_table_v1/`. Continues `DOOR4_v1` §13, which ruled the
density route an import and set the native task: **exhibit a rule naming a lonely `(e, k)`, with its
conditions shown exhaustive.**

---

## 1. Rules derived from the framework  `[these stand]`

**R0 — the first opening admits only the nearest flank.** `[PROVED]`
`Flanks.inWay_at_first_opening_of_lt`, `eq_min_of_lonely_first_opening`. Flank `b`'s opening `k = 0`
is `1/(n·b)`, where a runner at `m < b` reads `m/(n·b) < 1/n` and is in the way. So the `k = 0` layer
is **exhaustively** the single flank `b = min ds`.

**R0′ — the opening lower bound.** At flank `b`, opening `k`, the nearest runner reads
`m(nk+1)/(nb)`; if `m(nk+1) < b` that is below `1/n` and `m` is in the way. So

    lonely at (b, k)  ⟹  b ≤ m·(n·k + 1),   i.e.   k ≥ ⌈(b/m − 1)/n⌉

Verified with **0 violations over 1,252,558 openings**. It subsumes R0 at `k = 0`. It is a correct
pruning rule but a weak one — it removes 2.7% of openings.

**R1 — the nearest flank, with an exact condition at `m = 1`.** Take `b = min ds`. When `m = 1` the
flank has only `k = 0`, and the condition there is **exactly** *no difference divisible by 8*:
agreement **20,000/20,000**. This settles all three tight configurations, whose locators sit at
`±1 (mod 8)` (`DOOR4_v1` §9a).

R1 covers 0.552 at `k = 0` and 0.82 allowing `k < m`.

## 2. Rules fitted to the data  `[these do not stand]`

Continuing the table by choosing a fallback flank fails, and the failure is measurable.

| step | coverage on `[1,14]` | uncovered |
|---|---|---|
| R1 (nearest flank) | 0.769 | 792 |
| R1 ∨ "largest flank" | 0.9843 | **54** |
| R1 ∨ largest ∨ "largest odd not divisible by 8" | 0.9848 | 52 |

The 54 uncovered are highly structured — **every one contains both 7 and 8**, and every one contains
a multiple of 8. But no single fallback clears them: flank 7 serves 49 of 54, "second largest" serves
46, "largest not divisible by 8" serves 2.

**And the residue grows with the range.** The same three rules leave **52** sets uncovered on
`[1,14]` and **107** on `[1,17]`. The *fraction* improves (0.9848 → 0.9945) while the *count* rises.
Adding rules one at a time is not converging on anything; it is fitting a list to a sample.

## 3. The distinction that matters

A framework rule is **derived** — it comes from the construction and carries a condition the
construction supplies. R0, R0′ and R1's `m = 1` condition are of that kind: each has a one-line
reason and an exact statement.

"Take the largest flank", "take the largest odd flank not divisible by 8" are **fitted** — chosen
because they scored well on a sample, with no reason behind them and exceptions that multiply. They
are not rules in `FRAMEWORK_CONJECTURE_v1` §3's sense, and a table built from them would not have its
conditions *shown* exhaustive, only *observed* so on a range.

**This reinforces `DOOR4_v1` §6** rather than working around it. §6 showed no single designated flank
works; §2 here shows no short list of them works either. Whatever names the flank must be
**parameterised by the set** — computed from `ds` — rather than selected from a fixed menu.

## 4. Seventh sampler failure

Random sampling reported that "largest flank" clears **100%** of R1's failures — 7,374 of 7,374.
Exhaustive search over `[1,14]` finds **54** it does not clear. The sampler again missed the
structured hard cases, which here are exactly the sets containing both 7 and 8.

The standing rule stands: on this problem, exhaustive enumeration over a bounded range is the only
search that has ever found the binding cases. Every coverage figure above is exhaustive.

---

## 5. Combinations of flanks — the owner's question, and it changes the picture

**The question.** If no single flank rule works and no short list of them works, is it the right
*combination* of flanks that is required?

**A mechanism I tried first, and it failed.** Making a runner the flank *neutralises* it — at its own
openings it sits exactly on the band edge and never blocks — so the flank to choose should be the
runner that otherwise blocks most. It has a reason, and it is worse than the fitted rule:

| rule | `[1,14]` | `[1,17]` |
|---|---|---|
| nearest (R1) | 0.7692 | 0.5697 |
| worst blocker, globally | 0.7773 | 0.7493 |
| worst blocker at the nearest flank | 0.8962 | 0.9504 |
| largest (fitted) | 0.9630 | 0.9859 |

Having a reason did not make it right. `[REFUTED]`

### 5a. No pair suffices; a triple does  `[VERIFIED — exhaustive]`

Testing every pair and triple of flank **ranks** (0 = smallest … 6 = largest):

| | `[1,14]` | `[1,17]` |
|---|---|---|
| best single rank (6, the largest) | 0.9630 | 0.9859 |
| best pair, `(4,6)` | 0.9977 | 0.9993 |
| **pairs covering every set** | **none** | **none** |
| **triple `(4,5,6)` — the three largest** | **1.0000** | **1.0000** |
| triple `(2,4,6)` | 1.0000 | 1.0000 |
| triple `(3,5,6)` | 0.9997 | 0.9999 |

Not every triple works — `(3,5,6)` fails. But `(4,5,6)` holds across **widening exhaustive ranges**:

| range | primitive sets | failures of `(4,5,6)` |
|---|---|---|
| `[1,17]` | 19,440 | **0** |
| `[1,20]` | 77,400 | **0** |
| `[1,22]` | 170,213 | **0** |
| spread-biased sample | 40,000 | **0** |

≈307,000 sets, zero failures — and all three tight configurations are covered. **This behaves
unlike the fitted single-flank rules**, whose uncovered count *grew* with the range (54 → 107).

### 5b. The binding case is unique

Distribution of the number of working flanks per set:

| working flanks | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|
| `[1,20]` | **1** | 40 | 657 | 4,500 | 15,305 | 28,314 | 28,583 |

Across 77,400 sets there is **exactly one** with a single working flank — `(2,3,4,5,6,7,16)`, the same
set in both ranges — and its unique flank is the **largest**, rank 6. No set anywhere has its only
working flank below rank 4, which is precisely what the triple `(4,5,6)` needs.

### 5c. Status, stated exactly

**The owner's reframing is right**: combinations succeed where single flanks and short lists fail, and
the jump is from "no pair ever suffices" to "this triple never fails".

**But it is `[EMPIRICAL]`, not derived.** The triple was found by searching all 21 pairs and 35
triples, so its origin is fitting — and `(2,4,6)` works equally well, which undercuts any story about
the three largest specifically. What is missing is a *reason* three flanks suffice and two never do.
Until that exists this is a candidate rule with an exhaustive range behind it, not a rule with its
conditions shown exhaustive.

**What would settle it**: an argument that the set of working flanks can never be confined to ranks
`0–3`. The data says it is confined to a single flank exactly once in 77,400 sets, and that flank is
the largest.

---

## 6. The Three-Largest-Flanks rule  `[CONJECTURE — stable across five exhaustive ranges]`

> **Conjecture (TLF).** For every finite `ds ⊂ ℤ_{>0}` with `|ds| = 7` and `gcd(ds) = 1`, at least one
> of the **three largest** differences serves as a flank with a lonely opening.
>
> With `Flanks.target_flank_agrees` this gives `ExistenceAt8` — door 4 — over whole numbers.

### 6a. Evidence, and a retraction

**I said `(2,4,6)` works equally well, undercutting any story about the three largest. That is
wrong** — it was true only on the narrow range I had tested.

| range | primitive sets | `(4,5,6)` fails | `(2,4,6)` fails | triples covering all |
|---|---|---|---|---|
| `[1,17]` | 19,440 | 0 | 0 | **2** |
| `[1,20]` | 77,400 | 0 | 1 | **1** |
| `[1,22]` | 170,213 | 0 | — | — |
| `[1,24]` | **345,304** | **0** | **2** | **1** |
| spread-biased sample | 40,000 | 0 | — | — |

The winner count falls 2 → 1 and stays there. **`(4,5,6)` is the unique fixed triple that survives**,
and it survives every widening. Over 500,000 sets, zero failures.

### 6b. Why this is unlike everything else tried

Every other rule in this file degraded as the range grew — the fitted single-flank list left 54
uncovered on `[1,14]` and **107** on `[1,17]`; no pair ever reached 1.0 at any range. TLF does the
opposite: its hard case is a **single set that does not multiply**.

| working flanks per set | 1 | 2 | 3 | ≥4 |
|---|---|---|---|---|
| `[1,20]`, 77,400 sets | **1** | 40 | 657 | 76,702 |

The one set with a unique working flank is `(2,3,4,5,6,7,16)` — **the same set at `[1,17]`, `[1,20]`
and `[1,24]`** — and its flank is the largest. **No set at any range has its only working flank below
rank 4.**

### 6c. The owner's proposed reason, and what it still needs

The suggestion: an isolation is affected by **three** different speeds, and since no two runners share
a speed there is a birthday-style forcing that keeps the working flanks from collapsing onto the low
ranks.

That is the right *shape* of reason — it would explain the `3` and it would explain why distinctness
matters — and the data is consistent with it: the number of working flanks is 6 at the median and
collapses to 1 exactly once in 345,304 sets.

**What it is not yet is a derivation.** To become one it needs: (i) a precise statement of which three
speeds an isolation is "affected by", in the framework's objects; (ii) an argument that those three
cannot all sit at ranks `0–3`. Until (i) is pinned down I cannot check (ii), and the rule stays
`[CONJECTURE]`.

**But the status has changed.** This is no longer a fitted rule with a growing residue. It is a single
named conjecture, with a unique known extremal set, stable across five exhaustive ranges — and a
candidate reason for its constant. That is the first thing in this file worth trying to prove rather
than measure.

---

## 7. (i) made precise, and the mechanism it exposes

**The owner's statement.** The three speeds an isolation is affected by are **the subject and its two
neighbours** on the circle at the isolation instant.

In the subject's frame this is exact and elementary: the subject sits at `0`, and loneliness is
precisely *both neighbours at distance `≥ 1/8`* — every other runner is further round, so no other
constraint is active. At a flank opening the **flank is one of the two neighbours**, sitting at
exactly `1/8`. So a working flank is a runner that can occupy one neighbour slot while the other
neighbour stays clear.

### 7a. What the neighbours actually are  `[VERIFIED — 226,519 lonely openings, exhaustive on [1,17]]`

| rank (0 = smallest … 6 = largest) | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|---|
| **flank** at a lonely opening | 14,562 | 13,897 | 23,272 | 31,549 | 39,285 | 45,436 | **58,518** |
| **other neighbour** | **45,386** | 37,781 | 33,272 | 31,311 | 28,059 | 27,653 | 23,057 |

**The two distributions run in opposite directions.** The flank is usually **large**; the other
neighbour is usually **small**. The single most common configuration is `flank rank 6, neighbour
rank 0` (14,720 openings) — the largest difference and the smallest.

So the three speeds of an isolation are, typically: **the subject, the largest difference, and the
smallest.** That is the owner's statement, made concrete.

### 7b. The mechanism this gives, and it connects to a proved rule

Why should the flank be large and the neighbour small? Because of R0′, which is **already proved**:

    lonely at (b, k)  ⟹  b ≤ m·(n·k + 1)

A *small* runner sits near the subject unless it has had time to travel — at flank `b`, opening `k`,
the nearest runner reads `m(nk+1)/(nb)`, and below `k = ⌈(b/m − 1)/n⌉` it is inside the forbidden arc.
**The small runners are the binding constraint, and clearing them costs openings.** A flank of size
`b` supplies `b` openings, of which roughly `b(1 − 1/(n·m))` survive R0′.

**Hence the three largest flanks: they are the ones that supply enough openings for the small runners
to have cleared.** That is a mechanism in the framework's own objects — readings, openings, the
nearest runner — and it is why `(4,5,6)` and not `(2,4,6)` survives.

### 7c. Where (ii) now stands

The statement to prove is unchanged and now has a direction of attack:

> No `ds` has all of its working flanks at ranks `0–3`.

Confirmed exhaustively: **0 of 19,440** sets on `[1,17]`, and 0 across every range tested. The
distribution of the *lowest* working rank shows how rare the hard cases are:

| lowest working rank | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|---|
| sets | 11,074 | 3,703 | 3,359 | 1,094 | 196 | 13 | **1** |

Only 210 sets of 19,440 need a flank of rank `≥ 4` at all, and exactly one needs rank 6 —
`(2,3,4,5,6,7,16)`, the same extremal set at every range.

**What is still missing.** R0′ says small runners cost openings; it does not yet say that the three
largest flanks supply *enough*. Turning §7b into a proof means bounding, for the three largest `b`,
the number of openings surviving R0′ from below by more than the other runners can block — and the
union bound is vacuous there (`6 × 1/4 = 1.5`), so it needs the band arithmetic of `DOOR4_v1` §1, not
a count. That is the concrete next step, and it is the first one in this file with both a proved
ingredient and a named target.

---

## 8. Fast and slow blockers are different objects, and the AP names the instant

Two owner observations, tested.

### 8a. "Faster runners get in and out of the way faster"  `[VERIFIED]`

Exact in the flank picture: stepping `k` by one moves runner `a` by `a mod b`. A slow runner steps a
little and blocks **long runs of consecutive openings**; a fast runner steps far and blocks
**scattered singles**. Measured at `b = max ds`, 2,400 (runner, flank) pairs:

| `a/b` | # blocked runs | mean run length | blocked fraction |
|---|---|---|---|
| 0.00–0.10 | **9** | **4.88** | 0.249 |
| 0.20–0.35 | 42 | 1.00 | 0.250 |
| 0.50–0.70 | 45 | 1.00 | 0.249 |

**Same quarter blocked by every runner; completely different shape.** This is the first fact that
distinguishes the six blockers from one another — and it is exactly what every counting argument
throws away when it writes `6 × 1/4 = 1.5`. One or two slow runners carve the openings into a few
long windows; four or five fast ones sprinkle holes inside them.

**A heuristic of mine off it, refuted.** I predicted the lonely openings would sit near the middle of
the slow runner's clear stretches. They do not: position within the stretch has quartiles
**0.20 / 0.50 / 0.80** — uniform. (A figure in the first run said 59% lie in "the longest" stretch;
that was an artefact of ranking by *length* with many runs tied. The honest number is **13.2%**, which
is chance.)

### 8b. The AP names the instant  `[VERIFIED]`

For an arithmetic progression the positions at time `t` are themselves an AP on the circle with
generator `d·t`: **clustering is the generator at 0, isolation is the generator at 1/8** — two
extremes of one parameter. The cascade's bound `t₀ = 1/(8m)` *is* that isolation point, which is why
`k = 0` at the nearest flank settles the AP exactly (`ap_defect = 0 → k = 0`).

**Departing from the AP does not shift `k` — it kills the flank.** Correlation of `ap_defect` with the
first working `k` is `−0.164`, and the median `k` is 0 in every band; but the nearest flank's failure
rate climbs **0.036 → 0.344** across the defect range. The drift is in *which runner nominates*, which
is the TLF direction: `ap_defect` correlates `+0.32` with the lowest working rank and `−0.36` with the
number of working flanks. Modest — the medians do not move, it is a tail effect.

**And at the AP itself the nomination has an exact arithmetic description.** For `{1,…,7}` the working
flanks are ranks `0, 2, 4, 6` — precisely the **odd** differences `1, 3, 5, 7`; every even difference
fails as a flank. That is a *named* rule at the extremal configuration rather than a count.

| set | `ap_defect` | working ranks |
|---|---|---|
| `{1,2,3,4,5,6,7}` | 0.0000 | `[0,2,4,6]` — the odd differences |
| `{1,2,3,4,5,7,12}` | 0.2194 | `[0,2,4,5]` |
| `{1,4,5,6,7,11,13}` | 0.1959 | `[0,2,4,5,6]` |
| `{2,3,4,5,6,7,16}` | 0.2644 | `[6]` — the unique one-flank set |

Note the defect does **not** single out the extremal set: `(2,3,4,5,6,7,16)` sits at 0.264, inside the
ordinary range. So AP-defect measures how *thin* the options get, not *which* set is hardest.

### 8c. Where this leaves the naming gap

Two of the three pieces a producer needs are now in hand and native:

- **which runner nominates** — the three largest (TLF, conjecture), and at an AP exactly the odd
  differences (verified);
- **which laps are dead** — R0′, proved.

Missing still: **which lap**, away from the AP. But the shape of the remaining question has changed.
It is no longer "how many openings survive six interchangeable quarter-blockers" — a count that is
vacuous at `1.5`. It is: *inside the few long windows the slow runners leave, avoid the scattered
holes the fast ones punch.* That is an argument about two kinds of obstruction, which is the sort the
framework admits.

---

## 9. Reasoning the fast/slow split all the way through — it does not complete a door

Asked whether §8's split could close one of the doors. It cannot, and the reason explains why `7/4`
has been so robust.

### 9a. Three routes, one number

**Duration.** Runner `d` is in the way when `circDist(d·t) < 1/n`, so each blocking interval has
length exactly `1/(4d)` and `d` blocks a fraction `1/4` of any span. Every cascade interval
`[tⱼ, tⱼ₊₁)` lies inside one blocker's blocking interval, so the intervals partition the span among
seven runners, each absorbing at most a quarter:

    span ≤ 7 · span/4        vacuous at 7/4.

**Move size.** `move` goes to the *latest* exit among blockers, so each move is at most
`1/(4·d_setter) ≤ 1/(4m)`, giving `t_N − t₀ ≤ N/(4m)`.

**Settings count.** After a move the setter has exited, so it must re-enter before setting again —
each setting consumes a distinct blocking interval of that runner (this is
`nextOpening_le_move`'s corollary, verified: laps strictly increase between activities). Hence
`#settings by d ≤ d·span + 1` and `N ≤ (Σd)·span + 7`. With the move-size bound:

    N · (1 − Σd/(4m)) ≤ 7,   and  Σd ≥ 7m,  so the coefficient is ≤ 1 − 7/4 < 0.

Vacuous at `7/4` again, from a third direction.

### 9b. Why `7/4` is invariant under this split

**The blocking fraction is `1/4` for every runner, independent of speed** — measured 0.249–0.250
across every speed band (§8a). The fast/slow asymmetry changes the **granularity** of the blocked set
(9 runs of mean length 4.88 versus 45 of length 1.00) and not its **measure**.

So every duration, counting or measure argument is blind to the split *by construction*: each sees
only `7 × 1/4`. This is why the same constant has appeared in the union bound, the potential `Ψ`, the
move count, Prop 6.11, the Long-Return circle (`7/3` after the depth factor) and now three more
routes. It is one fact wearing different clothes.

### 9c. What the split is actually good for

It is not useless — it is simply not a measure statement. To use it one needs a claim about how the
blocked sets **intersect**, not how large they are: the slow runners' blocks are few and long, so a
single slow runner's blocked set is nearly an interval, while the fast runners' are nearly
equidistributed. A statement of the form *"a nearly-equidistributed set of density 1/4 cannot cover
the complement of a few intervals"* would do it — and that is a cancellation statement, which is the
density machinery again.

**So the split relocates the difficulty rather than removing it**: from "six interchangeable
quarter-blockers" to "one or two interval-blockers plus four or five equidistributed ones". The
second description is strictly more informative and still not sufficient.

**Recorded so it is not re-derived.** Any future route that ends in a comparison of *total blocked
measure* against *total span* will produce `7/4` and be vacuous, whatever the framing. The only
routes with a chance are those that use where the blocked sets sit relative to **each other**.

---

## 10. The AP's four isolation events, and what they explain

**The owner's statement.** The AP gives four global isolation events — two patterns and their
inversions — and the framework needs only **one**.

### 10a. Exact, and it explains §8b  `[VERIFIED]`

For `{1,…,7}`, every flank's lonely openings:

| flank | parity | lonely opening | instant |
|---|---|---|---|
| 1 | odd | `k = 0` | **1/8** |
| 2 | even | none | — |
| 3 | odd | `k = 1` | **3/8** |
| 4 | even | none | — |
| 5 | odd | `k = 3` | **5/8** |
| 6 | even | none | — |
| 7 | odd | `k = 6` | **7/8** |

**The four isolation events are exactly the four odd flanks' openings**, and the set
`{1/8, 3/8, 5/8, 7/8}` is closed under `t ↦ 1 − t`: `1/8 ↔ 7/8` pairs flanks 1 and 7, `3/8 ↔ 5/8`
pairs flanks 3 and 5. Two patterns and their inversions, as stated.

**This explains §8b**, which recorded that the working flanks of the AP are the odd differences
without knowing why. They are the hosts of the four events, one each.

### 10b. The symmetry is general; the four-fold *opening* structure is not

Over 9,763 lonely openings from general `ds`:

| | |
|---|---|
| mirror `1 − t` fails to be lonely | **0** — `lonely_neg`, as it must be |
| mirror `1 − t` is itself a flank opening | **962 (9.9%)** |

So loneliness is always symmetric, but the **opening** structure is not: away from the AP the mirror
of a lonely opening is lonely and lands *between* openings. The neat four-event picture is an AP
phenomenon. (An earlier run of mine reported "0/400 closed" for general `ds`; that tested closure of
the *opening* set, which is the wrong object for the symmetry claim. The instant-level statement is
the one above, and it never fails.)

### 10c. The inversion worth recording

*"We only need to find one"* is exactly `ExistenceAt8`'s `∃ s`. And at the AP one is **named
exactly**: `t = 1/8`, at flank `b = 1`, `k = 0`, under the condition *no difference divisible by 8*.

So the configurations where LRC is **tightest** — the three extremal sets, margin of a single opening
— are precisely the ones where the naming rule is **simplest and exact**. The naming difficulty is not
at the extremes; it is in the ordinary middle, where nothing distinguished picks out the instant.

That is the opposite of what the density measurements suggested (§§11–12 of `DOOR4_v1`, where the
worst error sat at `Σ ds ≈ 50`, in the middle) — and it is the same answer read from the native side.
Both say: **the hard cases for naming are the generic ones, not the extremal ones.**

---

## 11. Named instants: the flank does not have to be in `ds`

Asked whether the AP structure lets us **bound the flanks**. It does, and it exposed a freedom the
whole search had been giving away.

### 11a. The flank-hosting rule, derived  `[PROVED reasoning, VERIFIED 236/236]`

`t = j/8` is an opening of flank `b` iff `8k + 1 = jb` for some `k ≥ 0`, which forces `jb ≡ 1 (mod 8)`.
Every odd residue is self-inverse mod 8, so for odd `j`:

    t = j/8 is an opening of flank b   ⟺   b ≡ j (mod 8)

That is why flanks `1, 3, 5, 7` host `1/8, 3/8, 5/8, 7/8`, one each — §10a's observation, now derived
rather than observed.

### 11b. The freedom that had been thrown away

`ExistenceAt8` asks for a lonely **instant**, not a lonely flank opening — and
`clear_at_int_flank_iff_emod` places **no membership hypothesis on the flank**. So an instant may be
named as `(k + 1/n)/c` for *any* whole `c`, in or out of `ds`.

    Flanks.lonely_at_named_instant      `[PROVED]`
    Flanks.exists_lonely_of_named_instant `[PROVED]`

Naming an instant is therefore: **choose a pair `(c, k)`, check one residue condition per
difference.** All axiom-clean, build 2443 jobs.

### 11c. The `c = 1` case is a theorem on its own

`circDist(a/n) ≥ 1/n` unless `n ∣ a`. So:

> **If no difference is divisible by `n`, then `1/n` is lonely.**
> `Flanks.lonely_at_inv_of_not_dvd`, `exists_lonely_of_not_dvd` — `[PROVED]`, axiom-clean.

It does **not** require `1 ∈ ds`. Measured coverage at `n = 8`: **0.4201** of primitive 7-sets,
against `(7/8)^7 = 0.3927`, and **0 failures in 79,336** checks.

This is an *exhibition* in `FRAMEWORK_CONJECTURE_v1` §3's sense — the instant is written down — and it
is the first one in this file.

### 11d. How far `k = 0` with free `c` reaches

`t = 1/(8c)` is lonely iff `a mod 8c ∈ [c, 7c]` for every `a`:

| | coverage |
|---|---|
| `c = 1` | 0.4201 |
| `c ≤ 2` | 0.5264 |
| `c ≤ 10` | 0.9090 |
| any `c ≤ 4000` | **0.9420** |

Median smallest `c` is **2**, 90th percentile 10, largest found 43. Exhaustively on `[1,14]` the
largest smallest-`c` is **2**.

**But 5.8% have no `c` at all** — including `(2,3,4,5,6,7,16)`, the unique one-flank set of §6b. The
limitation is the numerator: this fixes `u = 1`, while the general instant is `u/(8c)` with
`u ≡ 1 (mod 8)`, i.e. `k > 0`.

### 11e. Where the rule table now stands

| rule | instant | condition | coverage | status |
|---|---|---|---|---|
| R-A | `1/8` | no difference divisible by 8 | 0.420 | **`[PROVED]`** |
| R-B | `1/(8c)` | `a mod 8c ∈ [c, 7c]` for all `a` | 0.942 | **`[PROVED]`** (same theorem, `k = 0`) |
| R-C | `(k+1/8)/c` | the residue condition at `k > 0` | — | `[PROVED]` as a criterion; **no rule names `(c, k)`** |

Two named instants are now proved and cover 94%. The gap is unchanged in kind but much narrower in
scope: **what names `(c, k)` for the remaining 5.8%** — the sets carrying a difference divisible by 8
in a configuration no single `c` clears.

---

## 12. What names `(c, k)` for the remaining 5.8%

### 12a. Why `k = 0` has a ceiling  `[derived]`

At `k = 0` the condition is `a mod 8c ∈ [c, 7c]`. For any `a < c` this reads `a ≥ c`, so

    k = 0 requires  c ≤ min ds.

That is the whole reason the `k = 0` layer stalls: for `(2,3,4,5,6,7,16)` the minimum is 2, so only
`c ∈ {1,2}` are available, and `16 ≡ 0 (mod 16)` and `16 ≡ 0 (mod 8)` kill both. At `k > 0` the
ceiling lifts, because `a(8k+1)` is no longer smaller than the modulus.

### 12b. Small `(c, k)` always worked  `[VERIFIED — no failure anywhere]`

For 40 sets with no `c` at `k = 0`: smallest `c` had median **5**, max **10**; its `k` median **2**,
max **5**; **none failed**. `c ∈ ds` in only 7 of 40 — the free-flank freedom of §11b is doing the
work, not a member of `ds`.

`(2,3,4,5,6,7,16)`, the unique one-flank set, is named by **`(c, k) = (8, 7)`**, i.e. `t = 57/64`.

Across everything tested — exhaustive `[1,14]`, `[1,17]`, `[1,20]`, `[1,22]` (267,000 sets) and
30,000 random sets to 600 — **a naming pair was found for every set, with `c ≤ 13`.**

### 12c. The divisibility structure, and a confirmation

| # differences divisible by 8 | median `c` | max `c` |
|---|---|---|
| **0** | **1** | **1** |
| 1 | 3 | 11 |
| 2 | 4 | 12 |
| 3 | 4 | 11 |
| 4 | 5 | 10 |

The first row **is** `lonely_at_inv_of_not_dvd`, recovered from the data: no difference divisible by
8 ⟹ `c = 1` ⟹ `t = 1/8`. Beyond that the count of multiples of 8 does **not** drive the size of `c`.

### 12d. The obstruction: `c` is not bounded by anything I can prove  `[STOP]`

The smallest naming `c` **grows with search effort**:

| search | max smallest-`c` |
|---|---|
| exhaustive `[1,14]` | 9 |
| exhaustive `[1,17]`, `[1,20]`, `[1,22]` | **13** (same set each time) |
| hill-climb, 120 restarts | 15 |
| hill-climb, 400 restarts | **17** |

So *"try all `(c, k)` with `c ≤ C`"* is **not** an established rule: I have no `C`. The naming pair
always exists in practice and I cannot bound where to look for it.

**What a bound would buy, stated exactly.** If `c ≤ C` always sufficed, the condition would depend on
each `a` only through `a mod 8c` for `c ≤ C`, hence through `a mod 8·lcm(1..C)` — a **finite** check
over residue patterns. `ExistenceAt8` over whole numbers would reduce to a finite computation. That
is what the missing bound is worth, and why it is the right thing to attack next.

**Where this leaves the door-4 line.** Two named instants are proved and cover 94% (§11e). The
remaining 5.8% always have a named instant and it is always small in practice — but the search for it
is unbounded by anything proved, which is the same shape of gap as `lonely_iff_bounded_search`'s
per-set finiteness with no uniform bound. The gap has moved from *"which opening"* to *"how far to
look"*, and got much smaller — `c ≤ 17` observed, against `Σ ds` before — without closing.
