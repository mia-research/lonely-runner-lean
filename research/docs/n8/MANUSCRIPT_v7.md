# A Bounding Framework for Eight Lonely Runners

**T. Palelei.** Draft v7, 2026-09-14.

---

## Abstract

Eight runners start together on a circle of circumference 1 and run at distinct constant
speeds. The Lonely Runner Conjecture at `n = 8` asserts that each of them is, at some
instant, at distance at least `1/8` from every other. The case was settled by computer
verification (Rosenfeld 2025), and the computational line has since reached `n = 13`
(Sungkawichai and Trakulthongchai 2026). **No analytic proof is known at `n = 8`.**

**Every result asserted as proved is formally verified** — 85 theorems in Lean 4, no
`sorry`, no `native_decide`, every declaration depending on `propext`, `Classical.choice`
and `Quot.sound` alone. §8 maps every numbered statement to its Lean declaration, so the
extent of the verification can be checked rather than taken, and a done-check script
refuses to pass if the open claim of §7.4 is ever stated.

We present a local framework for the problem and a formal verification of it. The
framework is not specific to `n = 8`: 79 of the 85 verified statements are at general `n`
or involve no runner count, and the six that are not have explicit general forms, themselves
formalised (§9). The framework replaces global analysis with a per-runner construction in
three objects — the cyclic **gaps** on the track, each runner's nearest speed difference
`d_min`, and the **laps** the others complete relative to it — and evaluates isolation on an
exact integer grid rather than by any continuous argument. Six of the construction's seven
parts are proved here and machine-checked in Lean 4. One ingredient inside them — the `φ(n)`
count of isolation instants for an arithmetic progression, part 2(b) — is cited to prior work
rather than re-derived, and is the framework's only external dependency (§5); it is proved
analytically in its source and is the one ingredient not machine-checked here.

The seventh part is the claim that the construction's procedure always returns, and it
is not proved. We state it as a **finite integer statement about one runner's seven speed
differences** — no interval, no measure, no reference configuration — record what is verified
of it, and do not state it in Lean. We also prove that several natural routes to it cannot work, including any
argument bounding how little of the evaluation window the obstructions amount to.

**This paper does not prove LRC(8).** It supplies verified local infrastructure, isolates
the remaining gap, and closes several approaches to it.

---

## 1. Introduction, and the Boundary Set Method

### 1.1 The shift

The classical treatments of the Lonely Runner Conjecture work globally and continuously.
The framework here does neither. It fixes one runner, forms that runner's own scale from
its two speed-neighbours, and reads every other runner's position off an exact rational
lap count inside one bounded window. Nothing is sampled, approximated, or estimated in
aggregate.

Two consequences follow immediately and both matter.

**Every quantity is exact.** Positions, lap counts and phases are rationals computed from
the speeds, so an isolation instant is *named*, not shown to exist.

**The evaluation is local.** Each runner is treated independently; the construction is
performed identically and separately for each of the eight, and no runner is held
stationary at any point.

### 1.2 The Boundary Set Method

Isolation is decided on the boundary set: the finite, named set of instants at which some
runner sits exactly on the threshold, together with the ends of the window. Between
consecutive boundary points nothing changes, so the decision on an open cell is settled by
its two ends.

**Open cells and boundary points are evaluated separately, and touching zones are never
merged.** This is not a matter of care; it is load-bearing. An in-the-way zone is the set
where the circle distance is strictly below `1/8`, so it is an **open** interval and its
endpoints are clear. In the arithmetic progression `(1, …, 8)`, the first runner's
**reading** — the set of instants at which every other runner is simultaneously clear of it
— inside its window is exactly the four points `1/8, 3/8, 5/8, 7/8` and nothing else. Any
implementation that closes those brackets, or that samples cell interiors, reports the
AP's end runners as never isolated — and compiles, and looks correct.

### 1.3 The window, and a deliberate over-strong target

Write `m = d_min(i)` for the subject's nearest speed difference and `u = m·t` for the lap
coordinate. The nearest runner is clear of the threshold exactly on `u ∈ [1/8, 7/8]`, one
full lap relative to it. The construction confines its evaluation to that first window.

This is **stronger than the conjecture requires.** LRC(8) asks only that a runner be lonely
at some time, which in this coordinate is `u ∈ [k + 1/8, k + 7/8]` for *some* lap `k`. The
first-window form is kept deliberately, because it buys a closed expression for the time —
`t* = u*/d_min`, with `d_min` read from two speeds — where the relaxed form would leave the
lap `k` unsupplied. We record it as a choice, not as the target.

---

## 2. Foundations: the local scale and the integer plane

### 2.1 The autonomous scale

Let the speeds be distinct and sorted, `v_1 < … < v_8`. For a subject `i`, put
`D = { d_j = |v_j − v_i| : j ≠ i }` and `d_min = min D`.

Because the speeds are ordered on a line, the minimum is attained at a **speed-neighbour**,
and this is exact rather than approximate. There is no wrapping on the speed line: for the
extremal runners the minimum is one-sided, so `d_min(r_1) = v_2 − v_1`, and `|v_8 − v_1|`
is the *largest* difference, never a candidate for the smallest. Cyclic adjacency, used
throughout §4, is a property of the **track**, not of the speed ordering, and the two must
not be conflated.

The readings are `s_j = d_j / d_min`, so `s_j ≥ 1` for every `j`, with equality possible —
in the AP the second runner's readings are `1, 1, 2, 3, 4, 5, 6`, two of them equal to 1.

**Seven differences, one of which realises `d_min`, leave exactly six readings to
evaluate.** The second speed-neighbour is not free: `d_min` comes from the *nearer* of the
two, and the other is read like every other runner. Omitting it changes the answer — at
`V = (4, 12, 29, 37, 101, 121, 176, 196)`, runner `r_4` has `d_min = 8` and a second
neighbour at difference 64, so `s = 8` sits exactly on its lap line at `u = 1/8` while all
five non-neighbours are clear. Reading five returns `1/8`; the moment is `9/64`. The two
readings differ in 3,276 of 48,000 runner-instances.

### 2.2 The `(a, m)` coordinates

Isolation moments are evaluated as coprime integer pairs. For the rational time `t = a/m`
and a relative speed `d`:

> **Proposition 2.1.** `‖d·a/m‖ ≥ 1/n` **iff** `m ≤ n·R` and `n·R + m ≤ n·m`, where
> `R = (d·a) mod m`.

Both conditions are on `ℕ`. There is no real division, no floor, and no fractional part in
the statement, so the threshold case — a gap equal to exactly `1/n` — is **in the
statement** rather than left to an argument about interiors. This is the form in which the
boundary discipline of §1.2 becomes automatic. *(Independently checked against a direct
test on 121,722 triples, zero mismatches.)*

---

## 3. Local restrictions: the clear-interval bound

Fix a subject and a reading `s`. The instants at which that runner is in the way are the
open intervals

    ( (8k − 1)/(8s),  (8k + 1)/(8s) ),    k = 1, 2, …

one per lap of the reading.

> **Proposition 3.1.** Each in-the-way zone has width `1/(4s)`, and consecutive zones are
> separated by a clear interval of width `3/(4s)`.

The zones are open and their endpoints are clear, as §1.2 requires; closing them would put
`u = 1/8` in the way for `s = 7`, and the AP's spine would vanish.

> **Corollary 3.2 (contiguous reach).** A single reading covers contiguously at most
> `1/(4s)`. It cannot bridge its own clear interval.

> **Proposition 3.3 (single-reading exclusion).** Let `σ` be the smallest reading other
> than the baseline `s_1 = 1`. No single reading **other than the baseline** can close a
> clear interval of `σ` on its own: any such reading has `s′ ≥ σ`, while a solo closure
> would need `1/(4s′) ≥ 3/(4σ)`, that is `s′ ≤ σ/3`.

Excluding the baseline is necessary, not a technicality. With `σ = 8` — realised by the
subject at speed 1 of `(0, 1, 9, …)`, whose readings are `{1, 8, …}` — the clear interval
`[57/64, 63/64]` of `σ` lies entirely inside the baseline's zone `(7/8, 9/8)`.

It costs nothing, because **the baseline has no zone inside the evaluation window at all**:
the zones of `s = 1` are `((8k−1)/8, (8k+1)/8)`, which meet `[1/8, 7/8]` in neither
direction. That is exactly how §1.3 defines the window. The counterexample therefore sits
outside the region where the proposition is used, and the restriction is the statement
catching up with that. *(The formal statement `no_solo_closure` already carries the
hypothesis `σ ≤ s′`; the gap was in the prose.)*

Every closure of a clear interval of the slowest reading therefore requires at least two
readings acting together. This is a structural constraint obtained from the geometry of
the combs alone, with no appeal to how much of the window anything amounts to.

---

## 4. Global structure: gap conservation and the reference permutation

### 4.1 Loneliness is a two-neighbour condition

At any instant the eight runners cut the circle into eight cyclic gaps summing to 1.

> **Theorem 4.1.** Runner `i` is lonely **iff** both gaps flanking its junction are `≥ 1/8`.

Seven constraints collapse to two. The statement holds at every index, including the
first and the last: adjacency is adjacency **mod `n`**, so the first runner's gap *before*
it and the last runner's gap *after* it are the same wrap gap, and there are no end
runners. Both directions are proved, and the converse needs only the two flanking pairs —
not the attainment of any minimum.

### 4.2 Conservation and the regular `n`-gon

> **Theorem 4.2.** All eight runners are lonely **iff** every gap is exactly `1/8`.

Eight numbers each at least `1/8` and summing to 1 are all equal. Global isolation is the
uniform 8-grid and nothing else.

> **Theorem 4.3.** `n` positions in `[0,1)`, pairwise at circle distance at least `1/n`,
> are in sorted order an arithmetic progression of step `1/n`.

This is 4.2 reached from a *pairwise* hypothesis rather than assumed in gap form, and it
is what the converse of §4.4 turns on.

> **Corollary 4.4.** The number of simultaneously lonely runners lies in `{0,…,6} ∪ {8}`.
> It is never 7.

If every gap clears, all eight are lonely; otherwise the clearing gaps form a proper subset
and the count is at most 6. *(Exhaustive over all 12,870 eight-subsets of `[1,16]`.)*

### 4.3 The reference instant

Write `V = A + e` against an arithmetic progression `A_k = v₀ + k·d`, and fix
`t = r/(nd)` with `gcd(r, n) = 1`.

> **Theorem 4.5.** The AP part places the `n` runners on the `n` distinct `n`-ths, one
> each, every pair at distance at least `1/n` — **for every runner simultaneously.**

The map `k ↦ kr (mod n)` is a bijection precisely when `gcd(r, n) = 1`. That simultaneity
is why the reference gives global isolation, and why no runner need be held still.

> **Theorem 4.6.** The deviation displaces runner `k` by exactly `e_k·r/d` eighths.

### 4.4 When the reference survives

> **Theorem 4.7.** With `v₀` chosen so that `e₀ = 0`, the instant survives **iff** every
> displacement is a whole number of eighths and `k ↦ kr + e_k r/d (mod n)` is a bijection.

The normalisation `e₀ = 0` is doing mathematical work, not bookkeeping. It pins one
position at 0; since all positions are non-negative that one is the sorted minimum, so the
regular `n`-gon of 4.3 sits at 0 and every position is a whole number of `1/n`s — which is
what forces each displacement to be integral. Without it the `n`-gon could sit anywhere
and the displacements would be whole only up to a common real shift.

### 4.5 Cases the framework settles outright

> **Theorem 4.8 (the ratio condition).** If `d_max ≤ 7·d_min` then `u = 1/8` isolates the
> subject.

The hypothesis is `s_j ∈ [1,7]` for every `j`, and every such `s` is at distance at least 1
from `8ℤ`. The bound is sharp at both ends: `‖s/8‖ = 1/8` exactly at `s = 1` and at `s = 7`.

> **Theorem 4.9 (the wide-gap lemma).** If two **adjacent** speed gaps are each at or above
> the average `S/7`, where `S` is the spread, then the runner between them satisfies 4.8.
> The extremal runners need only one such gap, since their farthest difference is the whole
> spread.

Contraposed: if 4.8 reaches no runner at all, then no two above-average gaps are adjacent
and none is at either end, so they occupy pairwise non-adjacent positions inside `{2,…,6}`
and there are at most three. *(Exhaustive over all 24,310 eight-subsets of `{0,…,16}`.)*

---

## 5. The external debt

The framework has **exactly one** dependency outside itself, and it is the author's own
prior work.

> Part 2(b) — that for an arithmetic progression the instants of global isolation are
> exactly `{δt} = r/n` with `gcd(r,n) = 1`, and that there are `φ(n)` of them per period —
> is Palelei (2026), Theorem 3.1(a)–(b).

That source proves Theorem 3.1 analytically and carries no formal development, so 2(b) is
the one ingredient of the construction that is cited rather than machine-checked. **None of
the numbered results of §§2–4 depends on it**, which is why the formal development covers
them without it. Where it does enter is as the fact that the arithmetic progression's
reading is the four isolated points `1/8, 3/8, 5/8, 7/8`: that is `φ(8) = 4` instantiated,
and it drives the boundary discipline of §1.2 and the negative result of §6.1.

Nothing else is cited. In particular the framework does not use Weyl equidistribution, does
not use the conjecture at any other order, and does not use Proposition 4.1 of the `φ(n)`
paper, which is a proof sketch in its source. Every other statement in §§1–4 and §7 is
proved here.

---

## 6. Negative results: routes that cannot close this

These are stated as contributions. Each is a route that looks natural and does not work,
with the reason.

### 6.1 Bounding how little the obstructions amount to cannot work

The natural first attempt is to show the in-the-way sets are collectively too small to
fill the window. This cannot succeed **at any strength**, and not because the bound is
merely loose.

> In the arithmetic progression, the subject's own reading inside the window is the four
> isolated points `1/8, 3/8, 5/8, 7/8`. The quantity such an argument would bound below is
> **zero** in the case that matters.

Any proof must therefore be pointwise: it must name an instant.

### 6.2 The relay and stretch-ratio refutation

A second attempt models a blockade as a chain of overlapping in-the-way zones spanning the
window, and bounds the ratio such a chain can span. Four facts defeat it, and each is
exact.

1. Blocking `u = 7/8` does **not** require a reading below `9/7`. The condition is
   `|7s − 8k| < 1`, so `s = 11/5` blocks it on its *second* lap: `‖(11/5)(7/8)‖ = 3/40`.
2. The overlap bound `9/7` holds for **first** zones only. In general lap `k` of `s` meets
   lap `k′` of `s′` when `s/s′ < (8k+1)/(8k′−1)`, giving `17/7` and `25/7` at later laps.
3. A relay is built from **zones, not runners**. A reading `s` has about `3s/4` zones in
   the window; seven readings supply 24, and an observed chain ran 11 hops with readings
   recurring. `N` runners do not give `N − 1` hops.
4. A single reading can block **both** ends alone: `s = 8` gives `8·(1/8) = 1` and
   `8·(7/8) = 7`. The ends do not force two readings, so there is no ratio to accumulate.

### 6.3 The `s = 8` fragmentation, and why the count fails

A reading of `s = 8` does fragment the window into 7 in-the-way zones and 6 clear gaps of
`3/32` each, and does block both ends. The fragmentation is real. The inference that five
remaining readings cannot fill six gaps is not: it assumes one reading per gap, and both
halves fail — readings **collaborate** on a single gap, and one reading has many zones and
so **serves several gaps**. A search over 300,000 draws of five readings closed **three of
the six**, which is neither none nor all.

The conclusion survives with margin; the counting argument for it does not.

**And the count cannot be repaired by bounding how many gaps one reading reaches.**  Let `σ`
be the smallest reading other than the baseline.  Its clear intervals are
`C_k = ((8k+1)/(8σ), (8k+7)/(8σ))`.  Take the single reading `s = 2σ`; its lap-`(2k+1)` zone is
`((16k+7)/(16σ), (16k+9)/(16σ))`, whose centre `(2k+1)/(2σ)` is exactly the centre of `C_k` and
whose width `1/(8σ)` is a sixth of `C_k`'s.  So

> `B_{2k+1} ⊂ C_k` for **every** `k`.  `[PROVED]`

One reading can therefore participate in closing **every** clear interval of `σ`, not merely
several.  Any argument of the form "there are only five other readings and too many gaps" is
dead at the outset, and §3.3's "at least two collaborators per gap" cannot be combined with a
participation count to rescue it.

---

## 7. Soundness, and what remains

### 7.1 The procedure, in integers

Fix a runner. Let `D` be its seven differences and `m = d_min`. Every candidate instant is
a rational `t` whose clearing test is Proposition 2.1 at `n = 8`. There are **two families**,
and §7.4 records that neither is redundant.

> **The reading's own openings.** For each `d ∈ D` and each `a ≡ 1 (mod 8)` with
> `d ≤ a·m ≤ 7d`, test whether `d ≤ (a·e mod 8d) ≤ 7d` for every `e ∈ D`. Return
> `t = a/(8d)` for any `(d, a)` that passes.
>
> **The lattice cascade.** For each step `D` — the gcd's lattice, then the runner's own
> `d_min`, then larger steps — and each `p ∈ {1,3,5,7}`, test whether
> `D ≤ (e·p mod 8D) ≤ 7D` for every `e ∈ D`. Return `t = p/(8D)` for any `(D, p)` that
> passes.

Every condition is an integer comparison. In the first family the condition `d ≤ am ≤ 7d`
is exactly `t ∈ [1/(8m), 7/(8m)]`, one lap of the nearest runner. **The second family is not
confined to that window**, and that is the point of it.

*Two of the seven conditions in the first family are free.* For `e = d`, `a ≡ 1 (mod 8)`
gives `a·d mod 8d = d` exactly. For `e = m`, the window condition already puts `am` in
`[d, 7d]`. When `d ≠ m` these are distinct and **five** conditions remain; when `d = m` they
are the same difference, the window forces `a = 1`, and **six** remain. The `d = m` candidate
is `t = 1/(8m)`, which is `u = 1/8`.

*The cascade's ceiling is forced, not chosen.* For the difference `m` itself the test reads
`D ≤ (m·p mod 8D) ≤ 7D`, and for `D ≤ 7m` the residue is `mp`, so `D ≤ mp ≤ 7m`. **No step
above `7·d_min` can clear**, whatever ceiling is nominated.

### 7.2 The candidates are exactly the openings  `[PROVED]`

> **Proposition 7.1.** If the subject is lonely at any instant of its window, then it is
> lonely at one of the candidates of §7.1.

*Proof.* By §1.2 an in-the-way zone is open, so the clear set inside the closed window is the
window minus finitely many open intervals, and is therefore closed. Every nonempty closed
subset of a closed interval has a least element, and every connected component of the clear
set has one. That least element is either the window's left end or the right endpoint of some
zone, since to its immediate left the point is covered. The right endpoint of the lap-`k` zone
of the difference `d` is `(8k+1)/(8d)`; the window's left end is `1/(8m)`, which is the `k = 0`
right endpoint of the difference `m`. Both are candidates. ∎

**The two cases are one.** The window's left end is not a separate case — it is the opening of
the nearest runner's own zone. So the moment, whenever the procedure returns, is always an
**opening** `(8k+1)/(8d)` for one of the runner's own differences.

*(Independently checked: 4,800 of 4,800 returned instants are of that form; and across
`n = 5…11`, no returned instant is ever a closing.)*

**This is a statement about which instants can work, not about which comes first.** The
procedure is not asked to produce the earliest moment, and §7.4 does not claim one.

### 7.3 Soundness  `[PROVED]`

> **Theorem 7.2.** If the procedure returns `(d, a)`, then the subject is lonely at
> `t = a/(8d) > 0`.

By Proposition 2.1 each clearing condition is `‖e·t‖ ≥ 1/8`; by §2.1 that covers every other
runner; by Theorem 4.1 the subject is lonely. Since the runner and the arrangement were
arbitrary, **the claim of §7.4 implies LRC(8)**.

### 7.4 Termination  `[CLAIMED]`

> **Claim.** For every arrangement and every runner, **one of the two families of §7.1
> clears**: either some `(d, a)` with `d ∈ D`, `a ≡ 1 (mod 8)`, `d ≤ a·m ≤ 7d`, or some
> `(D, p)` with `p ∈ {1,3,5,7}` and `D ≤ 7·d_min`.

**It is not proved, and it is not stated in the formal development.** It is a finite integer
statement about seven numbers, per runner. No interval, no measure, no reference
configuration, and no ordering in time.

#### Neither family alone suffices, and both witnesses are exact

This is why the Claim is stated over the pair rather than over either one.

> **The openings alone are not enough.** `V = (1, 1975, 5265, 6910, 8737, 9589, 11845,
> 15135)`, the runner at speed `1`, `m = 1974`. All 23 admissible `(d, a)` fail. The cascade
> clears it at `D = 8`, `p = 3`, `t = 3/64`. `[VERIFIED — exact]`
>
> **The cascade alone is not enough.** `V = (11, 21, 22, 23, 26, 34, 35, 40)`, the runner at
> speed `35`, whose differences include `1`. By the ceiling above, `D ≤ 7`, and no step in
> that range clears. The opening `(d, a) = (9, 25)` clears it. `[VERIFIED — exact]`

The second witness is the general shape rather than an accident: **a runner with a difference
equal to `d_min` small relative to its others has almost no cascade to run**, since the
ceiling `7·d_min` collapses. The two families cover opposite regimes — the cascade reaches
instants outside the first window, and the openings reach numerators the cascade's four
residues cannot express.

#### What failure would require

Suppose a runner has neither. Then for every opening, some `e ∈ D` throws its residue into
`[0, d)` or `(7d, 8d)`, which in both cases is `|a·e − 8q·d| < d`; dividing by `a` and using
`a ≥ d/m` gives

    | e − (8q/a)·d | < m.

**Every blocking event forces another of the seven differences to lie within less than one
`d_min` of a specific rational multiple of `d`** — and the seven would have to satisfy such a
relation for every admissible `(d, a)` at once, while also failing all `7·d_min` lattices.

#### Cases in which it is proved, from §§2–4 alone

| case | condition | reach |
|---|---|---|
| the `r = 1` candidate | no reading within `1` of a multiple of `8` | ≈ 47–58% of runners |
| **the four candidates `u = r/8`, `r ∈ {1,3,5,7}`** | the same with `r` in place of `1` | **≈ 71–76%** |
| Thm 4.8, the ratio condition | `d_max ≤ 7·d_min` | ≈ 28–33% |
| the residue test | `d_min` divides every difference, none `≡ 0 (mod 8d_min)` | ≈ 3–34% |
| every grid, and every dilate of one | a special case of the row above | ≈ 0.4–15% |

**These are nested, and the nesting is arithmetic, not incidental.** `d_max ≤ 7·d_min` puts
every reading in `[1,7]`, hence at distance `≥ 1` from `8ℤ`, hence clear at `r = 1`. The
residue test is the same band condition with integral readings, and every grid satisfies it.
So rows 3, 4 and 5 are contained in row 1, and row 1 is the `r = 1` case of row 2. Measured,
rows 3–5 contribute nothing to the union beyond row 2.

They are kept because each is a cheap sufficient condition a reader can check without
evaluating the band — not because they add coverage.

**The four-candidate row is the reading's own structure.** §1.2 and §6.1 both record that the
arithmetic progression's reading inside the window is exactly `1/8, 3/8, 5/8, 7/8`. Testing
all four is the procedure matching that structure; testing only `1/8` was an understatement of
it.

#### Evidence where it is not proved

`[VERIFIED]` Over 4,800 runner-instances from random integer 8-sets with speeds to 1,500,
**the two families together clear every runner**, while the cascade alone reaches
`0.981–0.999` and the openings alone miss the first witness above. Also 21,600
runner-instances across seven populations, including adversarial ones, all returning; and exhaustively every integer arrangement with `0 = v_1 < … < v_8 ≤ 40` and gcd 1
— 18,564,316 arrangements, 148,514,528 runner-instances, zero failures, in exact rational
arithmetic.

**That sweep is in the pinned frame `v_1 = 0`**, which is Rosenfeld's formulation rather than
this framework's; the two agree by the standard reduction, but §1.1's "no runner is held
stationary" does not describe the enumeration. A sweep over eight distinct **positive** speeds
with gcd 1, no pinning, returns for every runner at `n = 5, 6, 7, 8, 9, 10` over 4,025,986
runner-instances — decided by the boundary set, not sampled.

The returned locations sit early in the window: median `u = 1/8`, 90th percentile `0.173`,
99th percentile `0.25`, maximum `245/304 ≈ 0.806`, against a window ending at `0.875`.

**This remains verification over bounded families, not a proof.** Nothing above `v_8 = 40` is
covered, and no bound is offered on how far the search extends.

The obligation is **per runner**, not per configuration: a runner outside the settled cases
needs its moment whether or not some other runner in the same arrangement is inside them.

---

## 7A. The firewall

The framework's bans are part of it. They are recorded here so that a reader can tell them
from omissions, and so that an implementation can be checked against them.

| | |
|---|---|
| **No stationary frame** | No runner is pinned to zero. Translation invariance is stated once, in §1.1 |
| **No first-instant demand** | The procedure returns *an* isolation instant. It is never asked which comes first (§7.2) |
| **No global clock** | The procedure yields up to eight different times for the eight runners. No single global isolation event is needed |
| **No measure or density** | Exact arithmetic and combinatorial geometry only. No measure, density, zero-measure argument, or stability radius |
| **No covering or emptiness language** | The construction forms no complement and no set to be empty |
| **Boundary discipline is mandatory** | Open cells and boundary points evaluated separately; touching zones never merged (§1.2) |

Two of these were violated in earlier drafts of this paper: the first-instant demand entered
§7.1 and §7.2, and the pinned frame entered §7.4's evidence. Both are recorded above rather
than quietly repaired.

---

## 8. Formal verification

`LonelyRunner/LRC/Construction8/`, Lean 4 with mathlib, eleven modules.

| | |
|---|---|
| theorems | **85** |
| `sorry` | **0** |
| `native_decide`, `unsafe`, `admit` | **0** |
| axioms, every declaration | `[propext, Classical.choice, Quot.sound]` |

**Which numbered results are machine-checked.**  A referee should be able to check this
rather than take it, so the map is given in full.

| result | Lean declaration | |
|---|---|---|
| Prop 2.1, the `(a,m)` condition | `coord_iff` | ✓ |
| §2.1, locality of `d_min` and the floor | `nearest_below`, `nearest_above`, `before_floor` | ✓ |
| Prop 3.1, zone and clear widths | `blocked_width`, `clear_width` | ✓ |
| Cor 3.2 / Prop 3.3, contiguous reach and exclusion | `no_solo_closure`, `solo_closure_forces_smaller` | ✓ |
| Thm 4.1, the two-gap criterion | `lonely_iff_flanks`, `_first`, `_last` | ✓ |
| Thm 4.2, all lonely ⟺ every gap `1/8` | `gaps_all_eq` | ✓ |
| Thm 4.3, the regular `n`-gon | `grid_of_pairwise` | ✓ |
| Cor 4.4, never 7 | `lonely_ne_pred` | ✓ (also exhaustive to `[1,16]`) |
| Thm 4.5, the reference permutation | `ap_reference` | ✓ |
| Thm 4.6, displacement in eighths | `displacement` | ✓ |
| Thm 4.7, survival, both directions | `survives_of`; `int_of_pairwise_sep`, `not_dvd_of_sep` | ✓ |
| Thm 4.8, the ratio condition | `ratio_condition` | ✓ (sharp at `s = 1, 7`) |
| Thm 4.9, the wide-gap lemma | `wide_gap_core`, `wide_gap_end`, `wide_gap_speeds` | ✓ (core and geometric form) |
| §1.2/§7.1, the window and the reading | `window_iff`, `reading_clear_iff`, `lap_and_phase` | ✓ |
| Prop 7.1, the candidates are the openings | proved in §7.2; machine-checked as `exists_clear_candidate`, outside this artefact (§9) | ✓ **not in the digest** |
| Thm 7.2, soundness | assembled from the above; not stated as one declaration | **partial** |

Parts 1, 2(a), 3, 4, 5, 6(a), 6(b) and 6(c) are formalised. Part 2(b) is cited (§5). **Part
7 is not stated**, deliberately: the done-check `scripts/n8/gate.sh` **fails** if it is.
That gate also builds every module explicitly — the default build target does not enter the
directory — inventories `sorry`, scans for the hygiene keywords, and checks axioms on
twenty-three headline declarations. Its failure modes were each tested before it was trusted.

---

## 9. Generalisation

The framework is not specific to `n = 8`, and the formal development records how far that
goes rather than leaving it to assertion.

**Of the 85 theorems, 59 are stated at general `n`** and a further 20 involve no runner
count at all, being statements about reals — the contiguous-reach bound, the circle-distance
identities, the index-free wide-gap core. **Six** carry `n = 8` in the statement, all of
them the stretch geometry of §3: the two zone widths, the two ratio bounds, and the two
halves of the single-reading exclusion.

Those six have explicit general forms. With threshold `1/n`, a reading `s` is in the way
when `|u − k/s| < 1/(ns)`, and the rest follows:

| | at general `n` | at `n = 8` |
|---|---|---|
| in-the-way zone width | `2/(ns)` | `1/(4s)` |
| clear interval width | `(n−2)/(ns)` | `3/(4s)` |
| first-zone overlap (Prop 3.1 ff.) | `s/s′ < (n+1)/(n−1)` | `9/7` |
| descent through consecutive integers | `2s > n + 1` | `2s > 9`, breaking at `s = 4` |
| single-reading exclusion (Prop 3.3) | `s′ ≤ 2σ/(n−2)` | `s′ ≤ σ/3` |

Each general form is itself formalised, in a separate development that is not the artefact
of this paper, together with a theorem instantiating it at `n = 8` and recovering the
`Construction8` statement with its constants — so the reduction is checked rather than
asserted. The paper's artefact is unchanged by that work.

**Proposition 7.1 is machine-checked there too**, as `exists_clear_candidate`: given finitely
many open zones and a point of the closed window outside all of them, the window's left end or
some zone's right endpoint is also outside all of them. The proof is finite — the witness is
the largest right endpoint already passed — and uses no topology. §6.3's `2σ` containment is
checked there as well, and needs `3 < n`: at `n = 3` the two ends coincide.

**One hypothesis appears only at general `n`.** The single-reading exclusion asserts
`2/(ns′) < (n−2)/(nσ)`, which requires `n > 4`: at `n = 4` the two sides coincide and the
exclusion says nothing. It is therefore a fact about `n ≥ 5`, and at `n = 8` the hypothesis
is discharged by arithmetic, which is why the `n = 8` statement carries no trace of it. The
remaining five forms hold for every `n ≥ 1`.

**The local restrictions tighten as `n` grows.** The overlap bound `(n+1)/(n−1)` decreases
towards 1 — `9/7` at `n = 8`, `13/11` at `n = 12`, `17/15` at `n = 16` — so two readings
must be closer in ratio for their zones to meet at all. The single-reading exclusion
`2σ/(n−2)` tightens likewise. Whatever obstruction the framework's local bounds present, it
is not weaker at larger `n`.

**What does not carry over.** The coverage figures of §7.4 are measurements at `n = 8` and
say nothing about other orders. Part 2(b) is stated at general `n` in its source and so
transfers without change. And the claim of §7.4, read at general `n`, is the Lonely Runner
Conjecture itself — settled by computation for `n ≤ 13` (§ References) and open beyond.

**This section claims transferability of the infrastructure, not of any result about the
conjecture.** Nothing here closes a case at any order, including `n = 8`.

---

## 10. Statement of what is and is not established

**Established and machine-checked.**  Every numbered result of §§2–4: Proposition 2.1; the
locality of `d_min` and the floor; Propositions 3.1–3.3; Theorems 4.1, 4.2, 4.3, 4.5, 4.6,
4.7, 4.8, 4.9 and Corollary 4.4; the window and the reading.  The table in §8 gives the
declaration for each.

**Established.**  The soundness of the procedure (7.2), assembled from the formalised parts
rather than stated as one declaration.  The negative results of §6, which are proved here
and carry explicit counterexamples rather than formal statements.

**Not established.** The claim of §7.4, and therefore LRC(8). No bound is offered on how
far the procedure's search extends, and none of §§2–4 produces a moment for a runner in the
open case.

**n = 8 is not proved by this paper.**

---

## 11. Data and code availability

**The formal development.** Lean 4, toolchain `leanprover/lean4:v4.29.1`, against mathlib
at revision `5e932f97dd25535344f80f9dd8da3aab83df0fe6` (tag `v4.29.1`) and batteries at
`756e3321fd3b02a85ffda19fef789916223e578c`. The eleven modules of the artefact are
`LonelyRunner/LRC/Construction8/`: `Parts`, `LemmaPass`, `Coords`, `Reference`, `Gaps`,
`Sorted`, `Grid`, `Integrality`, `Flank`, `Window`, `Bounds`. Their SHA-256 digests, sorted
by filename, hash to

    578022e0296ce565ec601655747d1e5cdc614a9efa2cced6540162e698f43b9d

reproducible as `shasum -a 256 *.lean | sort -k2 | shasum -a 256` in that directory.

**The done-check.** `scripts/n8/gate.sh`. It purges build artefacts whose contents have been
evicted by file-system sync, builds each of the eleven modules by explicit target, inventories
`sorry`, scans for `native_decide`, `unsafe` and `admit`, runs `#print axioms` on 23 headline
declarations, and fails if the open claim of §7.4 is stated in Lean at all — with `sorry` or
otherwise. A plain `lake build` is **not** a check on this development: the default target does
not import `LRC/`, so it succeeds without compiling any of the above.

**The exhaustive record of §7.4.** The `v_8 ≤ 40` sweep is a single JSON record,
SHA-256 `18f8f88a0f92e08cd2110c61e75b92189baba80506cc73aa098cc86385525a7c`, produced by
`exhaustive_exact.py`, SHA-256
`1589b78f939564718204a338b380283b5e0181162e4d2903205e57232be84bc3`. It carries the counts
quoted in §7.4 — 18,564,316 arrangements, 148,514,528 runner-instances, zero failures — the
quantiles, and the extremal arrangement, and was computed in exact rational arithmetic. Its
`u_max_runner: 7` is a 0-based index and denotes the eighth runner. It presently sits in a
separate working tree from the Lean development; both will be deposited together, and the
digests above identify the deposited copies.

**The seven-population run of §7.4** (21,600 runner-instances) is tabulated by population in
the working record; its generator is in the experiments tree of the same repository and is not
individually hashed here.

**The generalisations of §9** are formalised in `LonelyRunner/LRC/ConstructionN/`, which is not
part of this paper's artefact and is not covered by the digest above. It carries its own
done-check, `scripts/nN/gate.sh`, which likewise refuses to pass if the open claim is stated.

---

## References

**Barajas, J. and Serra, O. (2008).** *The lonely runner with seven runners.* Electronic
Journal of Combinatorics **15**, R48. — settles `n = 7`, the largest case with a proof
that is not computer-assisted.

**Rosenfeld, M. (2025).** *The lonely runner conjecture holds for eight runners.*
arXiv:2509.14111, submitted 17 September 2025, revised 16 October 2025. — settles `n = 8`
by computer verification, combined with bounds on a minimal counterexample. This is the
case treated here. Rosenfeld states the conjecture with a stationary runner and `n − 1`
non-zero speeds; the framework below holds no runner still, and the two formulations agree
by the standard reduction.

**Sungkawichai, T. and Trakulthongchai, T. (2026).** *Eleven, twelve, and thirteen lonely
runners.* arXiv:2604.23906, submitted 26 April 2026, revised 1 September 2026. — extends
the computational line to `k ∈ {10, 11, 12}`, so the conjecture is known for `n ≤ 13`.
Builds on the method of Rosenfeld and the second author, which had reached `k ≤ 9`.

**Palelei, T. (2026).** *The φ(n) Law for Arithmetic Progressions in the Lonely Runner
Conjecture: Algebraic Structure and Computational Fragility.* Working paper, version 1.0,
4 January 2026. Zenodo, DOI **10.5281/zenodo.18158886**. — Theorem 3.1(a)–(b) supplies the
instants of perfect isolation for an arithmetic progression and their count; **the sole
external dependency of this paper**, cited at §5. Proved there analytically; that work
carries no formal development.
