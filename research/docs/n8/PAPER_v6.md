# A Bounding Framework for Eight Lonely Runners

**T. Palelei.** Draft v6, 2026-09-22. Submission draft, extracted from `MANUSCRIPT_v20.md`, which
remains the manuscript of record and holds the development history, the verification apparatus and
the record of routes closed.

**Correction in v6 — attribution of the `φ(n)` law.** The `φ(n)` law for arithmetic progressions is
not a result of this paper. It is the author's existing preprint — *The φ(n) law for arithmetic
progressions in the lonely runner conjecture: algebraic structure and computational fragility*,
Zenodo, `10.5281/zenodo.18158886`, dated 2026-01-06 — and it is the precursor to this framework, not
a consequence of it. Draft v5 stated it as new work in the abstract, in the introduction and in §3.1,
and cited the preprint nowhere. Corrected in four places, and the preprint added to the references:

* the **abstract** no longer says "we show" of the law, and names it as recalled rather than
  established;
* the **introduction** attributes it and calls it the precursor;
* **§3.1** states Theorem 3.4 as *Palelei 2026, Theorem 3.1*, and marks the proof as restated for
  self-containedness with no part claimed as new;
* **§3.2** now opens by attributing the zero-radius fragility to *Palelei 2026, Proposition 4.1*, so
  that Theorems 3.5–3.6 read as the sharpening they are rather than as new territory.

A fourth borrowing was found in the same pass and was not part of the complaint: **§4's boundary set
method is also the preprint's** (§2.2, Lemmas 2.1–2.2), and was named there without attribution. Now
cited.

Corrections carried from v5 — the repair of Theorem 3.4's proof, three symbol collisions, and the
terminology and cross-reference fixes — are recorded in `PAPER_v5.md` and are not restated here.

**A process note, carried forward.** The v4 file on disk was edited in place during that review
rather than being superseded, so the draft delivered under the name v4 is not recoverable.

---

## Abstract

Let `n` runners with distinct real speeds move on a circle of unit circumference. The Lonely Runner
Conjecture asserts that each is, at some instant, at distance at least `1/n` from every other. All `n`
runners are lonely simultaneously exactly when they occupy the vertices of a regular `n`-gon, and for
speeds in arithmetic progression this occurs at exactly `φ(n)` instants in each period — the `φ(n)`
law of Palelei (2026), which is the precursor to the present work and is recalled here rather than
established. Taking it as the starting point, we give for an arbitrary arrangement a necessary and
sufficient condition for such a global instant to persist under perturbation of the speeds,
sharpening that paper's zero-radius fragility to an exact criterion. We then develop a deterministic
procedure, the cascade, and prove that it halts precisely when a given runner is lonely — at an
instant `(j + 1/n)/e` determined by an integer `j` and one of that runner's own disparities `e`. The pair `(j, e)` is a certificate, verified in `n − 1` modular reductions. We give eight
arithmetic conditions on a runner's set of disparities, each of which produces such a pair and
so establishes the conjecture for every arrangement satisfying it, and we classify what they
presently reach by a single integer parameter. Two structural facts emerge: at order five the
cascade length is unbounded while the halting instant stays within a fixed factor of the earliest
possible one, and the same count `φ(n)` that governs the global instants governs the disparities a condition may use. All results are formalised in Lean 4.

---

## 1. Introduction

Let `v₁, …, vₙ` be distinct real speeds, each runner moving on a circle of unit circumference at its
own speed, and let `‖x‖` denote the distance from `x` to the nearest integer. Runner `i` is **lonely**
at time `t` if `‖(vⱼ − vᵢ)t‖ ≥ 1/n` for every `j ≠ i`. The Lonely Runner Conjecture, due to Wills and
independently to Cusick, asserts that every runner is lonely at some instant. It is settled for
`n ≤ 7` by arguments particular to each order.

The difficulty is that the conjecture is an existence statement over an unbounded continuum of
times, with `n − 1` conditions that must hold at once, and no evident reason why the times at which
each condition holds should ever intersect. The approach here is to begin where the intersection is
forced rather than accidental.

**Simultaneous isolation is rigid.** At any instant the `n` runners cut the circle into `n` gaps
summing to 1, so all of them are lonely at once only if every gap is exactly `1/n`: the runners must
stand at the vertices of a regular `n`-gon, with no freedom (Theorem 3.2). This is a strong
condition, and for speeds in arithmetic progression it is met, at instants one can write down: this
is the `φ(n)` law of Palelei (2026), recalled here as Theorem 3.4. That law is the precursor to
everything below, and its count `φ(n)` is the first appearance of a number that recurs throughout
the paper.

**Perturbation destroys simultaneity, and the conjecture is what remains.** Writing an arbitrary
arrangement as a progression plus deviations, we give a criterion (Theorem 3.6) deciding exactly
when a global instant persists, sharpening to an exact condition the zero-radius fragility that
Palelei (2026) established for the progression itself. A global instant rarely does persist: it
requires commensurable speeds and an alignment condition, and an irrational deviation destroys it
outright. When it fails there is no
longer one instant serving every runner, and each needs an instant of its own. That every runner
still has one is precisely the conjecture — so the conjecture is what the simultaneous picture
degenerates into, not a separate question. A fragment is already a theorem: the number of
simultaneously lonely runners is never exactly `n − 1` (Corollary 3.3), so simultaneity is lost all
at once rather than runner by runner.

**Locating the individual instants.** The rest of the paper does this. Fix a runner, work in its own disparities and its own time scale, and run a deterministic procedure: start at the earliest
instant the runner could be lonely, and whenever some other runner lies within `1/n`, move to the
latest instant at which one of those reaches distance exactly `1/n`. The runners currently
obstructing determine the step, so nothing is searched or ranked. We call this the **cascade**.

> **Theorem A.** For every injective `v : Fin 8 → ℝ` and every runner `k`, the following are
> equivalent: `k` is lonely at some positive instant; the cascade halts; the cascade's instants are
> bounded above; some disparity `e` has an opening `(j + 1/8)/e` at which `k` is lonely; and
> each runner obstructs `k` at only finitely many steps.

The equivalence has both directions and no hypothesis beyond injectivity, and its proof is uniform
in the order. It identifies the conjecture with a statement about a pair of integers: when the
cascade halts it halts at `(j + 1/n)/e`, and that pair `(j, e)` can be checked in `n − 1` modular
reductions without reference to the procedure that produced it (§6).

Eight explicit conditions on the disparity set then produce such a pair directly. They are
elementary — the widest asks only that the largest difference be at most `n − 1` times the least,
and the simplest asks that no difference be divisible by some `q ≤ n`, naming the instant `1/q`.
Each establishes the conjecture for every arrangement meeting it. §12 classifies what they reach by
the number of differences divisible by `n`, and isolates the one region where none of them names a
flank.

**Arrangement of the paper.** §3 treats simultaneous isolation, recalls the `φ(n)` law of Palelei
(2026) and gives the perturbation criterion. §4 sets out the boundary discipline the construction depends on. §5 fixes the runner's
scale, §6 reduces arbitrary lonely instants to the pairs `(j, e)`, and §7 defines the cascade and
traces it in full on one arrangement. §8 proves Theorem A. §9 gives the order-five length result,
§10 the eight conditions, §11 the totient behind them, and §12 the classification and what remains
open. §13 treats general `n` and §14 the formal verification.

## 2. Notation

| symbol | meaning | introduced |
|---|---|---|
| `n` | the number of runners; `n = 8` unless stated | §1 |
| `v : Fin n → ℝ` | an **arrangement**: injective speeds | §1 |
| `k` | the **subject**, the runner whose loneliness is at issue | §1 |
| `‖x‖` | circle distance from `x` to the nearest integer, `min(frac x, 1 − frac x)` | §3 |
| `A`, `e` | the progression part and the deviations of an arrangement, `v = A + e` | §3.2 |
| `a` | the index of a global instant `a/(n d)`, coprime to `n` | §3.1 |
| `d` | a **difference**: `\|vᵢ − v_k\|` for some `i ≠ k` | §3 |
| `ds` | the subject's set of disparities; `\|ds\| ≤ n − 1` | §3 |
| `m`, `d_min` | the least disparity | §5 |
| `d_max` | the greatest disparity | §5 |
| `t` | time | §3 |
| `u` | the local time coordinate `d_min · t` | §5 |
| `e` | a **flank**: a disparity used as the denominator of a candidate instant | §6 |
| `j` | the **opening index** of a flank | §6 |
| `(j + 1/n)/e` | the `j`-th **opening** of the flank `e` | §6 |
| `t₀` | **the bound** `1/(n·d_min)`, the earliest instant that can be lonely | §5 |
| `R` | the ratio of the halting instant to the bound | §9 |
| `L` | the lap counter in the band condition of R2 | §10 |
| `M`, `c` | the number of disparities divisible by `n`, and the number of disparities | §12 |
| `φ` | Euler's totient | §11 |
| `M` | the number of disparities divisible by `n` | §12 |

A reading is a quantity `d · t`; a **band** is the set of readings at circle distance at least
`1/n` from the integers, namely `[1/n, 1 − 1/n]` modulo 1.

## 3. Global isolation and the `φ(n)` law

Fix a subject `k`. Runner `i` sits at circle distance `‖(vᵢ − v_k)t‖` from the subject at time `t`.

> **Definition.** The subject is **lonely at `t`** when `‖d·t‖ ≥ 1/n` for every difference `d`. The
> condition is closed: a runner at distance exactly `1/n` leaves the subject alone.

At any instant the `n` runners cut the circle into `n` cyclic gaps summing to 1.

> **Theorem 3.1.** Runner `i` is lonely if and only if both gaps flanking it are at least `1/n`.

The converse needs only the two flanking pairs, and not the attainment of any minimum. Two
consequences fix the shape of the problem.

> **Theorem 3.2.** All `n` runners are simultaneously lonely if and only if every gap is exactly
> `1/n` — the regular `n`-gon.

> **Corollary 3.3.** The number of simultaneously lonely runners lies in `{0, …, n−2} ∪ {n}`. It is
> never exactly `n − 1`.

Theorem 3.2 says global isolation is a rigid configuration: the `n` runners must stand at the
vertices of a regular `n`-gon, with no freedom at all. Corollary 3.3 is a conservation statement —
the gaps sum to 1, so isolation cannot be removed from one runner while the others keep theirs
simultaneously.

### 3.1 The `φ(n)` law

For speeds in arithmetic progression the global instants can be written down exactly. This is the
`φ(n)` law of Palelei (2026, Theorem 3.1), the precursor to this framework; it is stated here, with
its proof, so that the paper is self-contained, and no part of it is claimed as new.

> **Theorem 3.4** (the `φ(n)` law; Palelei 2026, Theorem 3.1)**.** Let the speeds be
> `v₀, v₀ + d, …, v₀ + (n−1)d`. All `n` runners are simultaneously lonely precisely at the instants
>
> ```
>     t = a/(n d),      a ≥ 1,      gcd(a, n) = 1,
> ```
>
> and at no others. There are `φ(n)` such instants in each period. At `n = 8` there are four, at
> `t d = 1/8, 3/8, 5/8, 7/8`.

*Proof* (Palelei 2026; restated). Work relative to runner `0`. At time `t` runner `i` stands at
`(vᵢ − v₀)t = i d t` on the circle, so writing `u = d t` the `n` relative positions are `{ i u mod 1 : 0 ≤ i < n }`. By
Theorem 3.2 all `n` runners are lonely exactly when these are the `n` vertices of a regular
`n`-gon, that is when

```
    { i u mod 1 : 0 ≤ i < n }  =  { 0, 1/n, 2/n, …, (n−1)/n }.
```

Suppose they are. Runner `1` stands at `u`, which is then a vertex, so `u = a/n` for some integer
`a ≥ 1`. The positions are `{ i a/n mod 1 }`, and as `i` runs over `ℤ/n` the image of `i ↦ i a` is
the subgroup generated by `gcd(a, n)`, of size `n / gcd(a, n)`. That is all of `ℤ/n` exactly when
`gcd(a, n) = 1`. Conversely, if `gcd(a, n) = 1` then `i ↦ i a` is a bijection of `ℤ/n` and the
positions are precisely the `n` vertices. Hence the global instants are `u = a/n` with
`gcd(a, n) = 1`, that is `t = a/(n d)`, and there are `φ(n)` of them per period. ∎

The count is the framework's first invariant, and it recurs: §11 shows that the same `φ(n)` counts
the disparities a certificate rule may use as a flank. The global instants are exactly the
units of `ℤ/n`, and so are the usable flanks.

Two further consequences are worth recording. The lonely set here is finite in each period, hence of
measure zero, so at this configuration there is no positive-measure set of lonely instants for an
averaging argument to act on. And by Theorem 3.2 this is the extremal configuration, the one any
general argument must cover; the framework accordingly works in exact arithmetic and lap geometry
throughout.

### 3.2 Perturbation: when a global instant survives

Palelei (2026, Proposition 4.1) shows that the configuration of Theorem 3.4 has zero stability
radius: exact grid formation cuts out a measure-zero set, so arbitrarily small perturbations destroy
it. What follows sharpens that statement from a measure-theoretic one to an exact criterion, naming
which perturbations survive and which do not.

Let the speeds be arbitrary. Write them against a progression, `v = A + e`, with
`A_k = v₀ + k d` and deviations `e_k`, normalising `e₀ = 0`.

> **Theorem 3.5.** At `t = a/(n d)` with `gcd(a, n) = 1`, the progression part places the `n` runners
> one to each `n`-th, simultaneously; the deviation displaces runner `k` from its vertex by exactly
> `e_k · a / d` of an `n`-th.

> **Theorem 3.6.** The global instant survives the deviation if and only if every displacement is a
> whole number of `n`-ths and `k ↦ k a + e_k a / d (mod n)` is a bijection of `ℤ/n`.

So global isolation is fragile in a precise way. It requires the displacements to be integral, which
forces the speeds to be commensurable, and it requires the resulting permutation of the vertices to
remain a permutation. An irrational deviation destroys it outright; a rational one destroys it as
soon as two runners are sent to the same vertex.

**Where the isolation goes.** When the global instant fails, what has been lost is the
simultaneity: no single instant now serves every runner, and each must be given one of its own. That
every runner still has one is the Lonely Runner Conjecture itself.

Corollary 3.3 is the fragment of that picture which is a theorem: isolation cannot be removed from
one runner while the rest keep theirs together. So simultaneity goes all at once, which is why
Theorem 3.6 reads as an all-or-nothing condition. Locating the individual instants is what the rest
of this paper does.

---

## 4. The boundary discipline

The loneliness condition is closed, so the set of times at which a given runner obstructs is a union
of **open** intervals,

```
    ( (N − 1/n)/d , (N + 1/n)/d ),     N ∈ ℤ,
```

one about each of that runner's relative laps. We call these its **in-the-way zones**; the endpoints
belong to the complement. Two consequences carry through everything that follows.

**Endpoints are clear.** At `t = (N + 1/n)/d` the runner `d` stands at distance exactly `1/n`. Every
candidate instant this paper constructs is such an endpoint, for some runner and some lap — that is
what makes the certificate of §6 a pair of integers rather than a real number.

**A cell is decided by an interior point.** Partition the positive axis by all the zone endpoints of
all the differences. Within one cell every runner's status is constant, so any interior point
decides it. The endpoints bounding a cell may both be clear while the cell's interior is not: the
two bounding zones can belong to different runners and overlap across the cell between them.
Deciding a cell therefore requires an interior point.

This is the **boundary set method** of Palelei (2026, §2.2), whose Lemmas 2.1–2.2 establish that a
runner's status can change only at these endpoints, so that the cells are exactly the intervals on
which every status is constant: evaluate open cells and boundary points separately, never merge
touching zones, and decide a cell by an interior point. The worked example of §7.1 shows it
operating — two runners sit exactly on the boundary at the first step and are clear, and one of them
becomes the next obstruction.

---

## 5. The local scale

Normalise by the nearest runner. Writing `u = d_min · t`, each disparity `d` has a **ratio**
`s = d / d_min ≥ 1`, and the reading of `d` at time `t` is `s · u`.

> **Theorem 5.1 (the earliest possible lonely instant).** If the subject is lonely at `t > 0` then
> `t ≥ 1/(n·d_min)`; equivalently `u ≥ 1/n`.

We write `t₀ = 1/(n·d_min)` and call it **the bound**: below it the nearest runner has not yet left
the subject, so nothing earlier can be lonely. It is where the procedure of §7 begins.

> **Theorem 5.2 (the ratio condition).** If `d_max ≤ (n−1)·d_min` then the subject is lonely at
> `u = 1/n`, that is at `t = 1/(n·d_min)`.

Immediately: at that instant every reading `s` lies in `[1, n−1]`, hence at distance at least 1
from `n·ℤ`. The constant `n − 1` is one below the first multiple of `n`, and is not special to
eight. Theorem 5.2 is the first and widest single rule, and it settles a subject outright whenever
the spread of its disparities is within a factor of `n − 1`.

---

## 6. Flanks and openings

> **Definition.** For a disparity `e` and an integer `j ≥ 0`, the `j`-th **opening** of the flank
> `e` is the instant `(j + 1/n)/e`.

At such an instant the runner `e` sits at distance exactly `1/n` — on the boundary, hence clear —
and the content of the condition is carried by the other disparities. The following says the family
loses nothing.

> **Theorem 6.1.** The subject is lonely at some positive instant if and only if some flank has a
> lonely opening.

The forward direction is the substantive one: from any lonely `t`, the opening `(⌊e·t⌋ + 1/n)/e` of
a suitable disparity `e` is lonely and no later than `t`. So a search for lonely instants may be
confined to this countable family without loss.

For whole-number disparities the family is finite and the condition is arithmetic.

> **Theorem 6.2.** Let the disparities be positive integers and `e` one of them. The opening `j` of
> the flank `e` is lonely if and only if
>
> ```
>     d · (n j + 1)  mod  n e   ∈   [ e , (n−1) e ]        for every disparity d.
> ```
>
> The condition is periodic in `j` with period `e` — replacing `j` by `j + e` adds `n e` to the
> numerator — so the search `0 ≤ j < e` decides the question. No real number survives in the
> criterion.

(`e` is a period; it need not be the least one, and nothing below requires that it be.)

Written on the floor rather than the residue, the same condition reads

```
    ⌊ d · a / e ⌋  mod  n   ∈   {1, …, n−2},    or  = n−1 with e | d·a,
```

where `a = n j + 1`. So `⌊d·a/e⌋` is the Beatty sequence of slope `d/e`, and an opening index is a
point at which `|ds| − 1` Beatty sequences simultaneously avoid two residues modulo `n`. The flank
itself is free, since `d = e` gives `⌊a⌋ = a ≡ 1 (mod n)`.

Two remarks. Every opening index `a = n j + 1` is coprime to `n`; the framework never exhibits a
witness outside the unit group of `ℤ/n`. And the clause `= n−1 with e | d·a` is the closed endpoint
of the band and is not optional: dropping it makes disparity sets appear to have no working
opening when in fact they do.

---

## 7. The procedure, and a worked example

> **Definition.** A runner at disparity `d` is **in the way** at `t` when `‖d·t‖ < 1/n`. Its **next
> opening** after `t` is the least `(N + 1/n)/d` at or after `t`. The **move** sends `t` to the
> largest next opening among the runners in the way at `t`, and fixes `t` if none is. The
> **cascade** is the sequence of moves from the bound `1/(n·d_min)`.

Three facts make this well defined and free of search. A runner in the way at `t` stays in the way
until its own next opening; the next opening is strictly later than `t`; and each move lands on the
opening of one runner in the way. There is no candidate list: the runners in the way at `t` fix the
move.

It is a recursion on the scale. At `1/(nD)` a runner of reading `s = d/D` is in the way exactly
when `|s − nN| < 1` for some `N`, and its next opening is the first point of the progression of gap
`d/(nN+1)`. So

```
    D₀ = d_min,    D_{j+1} = D_j · min{ s/(nN+1) : |s − nN| < 1 },    instant = 1/(n·D_final),
```

stopping when no reading lies within 1 of a multiple of `n`. Every factor is below 1, so the scales
decrease.

### 7.1 A complete example

Take the arrangement `1, 2, 3, 4, 5, 6, 8, 9` and the subject at speed `1`, whose disparities are

```
    ds = { 1, 2, 3, 4, 5, 7, 8 },      d_min = 1,      earliest possible instant t₀ = 1/8.
```

Adding a constant to every speed changes no disparity, so the choice of which runner to place where
is a convenience and never a hypothesis; the construction is carried out separately for each
subject, in that subject's own differences.

**Step 0, `t = 1/8`.** The readings `d·t` are

| `d` | 1 | 2 | 3 | 4 | 5 | 7 | 8 |
|---|---|---|---|---|---|---|---|
| `d·t` | 1/8 | 1/4 | 3/8 | 1/2 | 5/8 | 7/8 | 1 |
| `‖d·t‖` | 1/8 | 1/4 | 3/8 | 1/2 | 3/8 | 1/8 | **0** |

Runner 8 is at distance 0 — it has completed exactly one relative lap and sits on the subject. It
is the only runner in the way. Its next opening is `(1 + 1/8)/8 = 9/64`, and the move goes there.

Note what runners 1 and 7 are doing: both sit at distance exactly `1/8`, on the boundary. They are
clear. This is the closed condition of §3 doing visible work — had the inequality been strict, this
instant would have three obstructions rather than one.

**Step 1, `t = 9/64`.** The readings are now

| `d` | 1 | 2 | 3 | 4 | 5 | 7 | 8 |
|---|---|---|---|---|---|---|---|
| `‖d·t‖` | 9/64 | 9/32 | 27/64 | 7/16 | 19/64 | **1/64** | 1/8 |

Runner 8 has been cleared — it now reads `9/8`, distance `1/8`, on the boundary. But runner 7,
which sat exactly on the boundary at step 0, now reads `63/64`: it has been carried to within
`1/64` of completing its lap, and is in the way. Its next opening is `(1 + 1/8)/7 = 9/56`, and the move goes there.

**Step 2, `t = 9/56`.** The readings are

| `d` | 1 | 2 | 3 | 4 | 5 | 7 | 8 |
|---|---|---|---|---|---|---|---|
| `‖d·t‖` | 9/56 | 9/28 | 27/56 | 5/14 | 11/56 | **1/8** | 2/7 |

Every distance is at least `1/8`. No runner is in the way, the move fixes `t`, and the subject is
lonely at `t = 9/56`.

**Reading off the certificate.** The halting instant is `9/56 = (1 + 1/8)/7`, which is the opening
`j = 1` of the flank `e = 7`. So the certificate is the pair `(e, j) = (7, 1)`, and runner 7 sits at
exactly one eighth — as Theorem 8.1(d), proved in §8, says it must.

The cascade took two moves. Nothing in the certificate records that; the pair `(7, 1)` is what is
exhibited, and it can be checked in seven modular reductions without reference to the procedure
that found it. This is the distinction §9 makes precise.

**And the rules of §10 reach this set by another route entirely.** Its largest disparity exceeds
seven times its least, so R1 does not apply; one disparity is divisible by 8, so R3 does not. But no
disparity is divisible by 6, so R6 applies at `q = 6` and names the instant `t = 1/6`, at which the
readings are `1/6, 1/3, 1/2, 1/3, 1/6, 1/6, 1/3` — all at least `1/8`.

So the cascade and the rules are two ways to a certificate, and they generally produce **different**
ones: `9/56` here against `1/6`. The cascade is a discovery procedure that always terminates when
the subject is lonely (Theorem A) and needs no condition; a rule is a shortcut that bypasses the
procedure entirely but applies only where its condition holds. Neither is the other's approximation.

---

## 8. Construction, Localisation, and Theorem A

> **Theorem 8.1 (Construction).** If some step of the cascade is fixed, at `T`, then: the subject is
> lonely at `T`; no positive instant before `T` is lonely; `T` is the end of a run of
> lap-completion zones from the bound, each containing the end of the one before; and some runner
> sits at exactly `1/n`, as the nearest ahead or the nearest behind.

So a fixed point is not merely *a* lonely instant. It is the **first** one, it terminates a
boundary-set run, and it carries a runner at the threshold — which is why the halting instant is
always an opening, and why the certificate has the form `(e, j)`.

> **Theorem 8.2 (Localisation).** For every positive instant `s` at which the subject is lonely:
> `s ≥ 1/(n·d_min)`; every step of the cascade is at most `s`; `s` is matched by a lonely opening no
> later than it; and **the cascade reaches a fixed point**.

The last clause is the direction that carries the equivalence, and its proof is a finiteness
argument and nothing else: below `s` the cascade's steps lie in the finite set of openings
`(k + 1/n)/d` with `0 ≤ k ≤ ⌈d·s⌉`, and a strictly increasing sequence cannot remain in a finite
set.

Together:

> **Theorem A.** For every injective arrangement `v` and every subject `k`, with no hypothesis
> beyond injectivity, the following five statements are equivalent:
>
> 1. the subject is lonely at some positive instant;
> 2. the cascade reaches a fixed point;
> 3. the cascade's instants are bounded above;
> 4. some flank has a lonely opening;
> 5. each runner is in the way at only finitely many steps.
>
> The proof is uniform in the order; the same argument gives the statement at every `n ≥ 2`.

**What Theorem A gives.** It identifies the framework's objects with the conjecture's. Whatever
holds of one holds of the other, at every arrangement and every subject: to exhibit a flank and an
opening index at which the subject is lonely is to establish the conjecture there, and conversely
every lonely subject has such a pair. The rules of §10 are the work of exhibiting them.

---

## 9. Cascade length at order five

At orders three and four, and at order `n ≥ 6` with four differences, the cascade halts within a
number of steps fixed in advance. At order five with four differences the length grows with the
arrangement.

> **Observation 9.1** `[VERIFIED — exact rational arithmetic, 3 ≤ κ ≤ 100; not formalised]`. At
> order five the disparity sets `(1, 5κ − 2, 5κ, 10κ − 2)` have cascade length `2κ + 1` for even
> `κ` and `2κ + 2` for odd `κ`. The setter word is regular: writing `A = 5κ−2`, `B = 5κ`,
> `C = 10κ−2`, it is the repeated four-cycle
>
> ```
>     B@ι ,  C@2ι ,  A@ι ,  C@(2ι+1)          for ι = κ, κ+1, κ+2, …
> ```
>
> terminating in a final `B`, the last cycle truncated when `κ` is odd. Here `X@ι` means the move is
> set by difference `X` at its lap `ι`.

Along the same family the ratio `R` of §5 tends to `3/2`. So the two quantities move independently:
the number of steps grows without bound while the halting instant stays within a fixed factor of the
earliest possible one. A long cascade and a late instant are different things, and the certificate
records the second.

This bears directly on the form of the certificate. A pair `(e, j)` is checked in `n − 1` modular
reductions whatever the length of the cascade that found it — in §7.1, two steps produced `(7, 1)`,
and the check would read the same had it taken two hundred.

**Toward a proof.** Every setter lap in the family is at least `κ − 1`: the first setter is `B` at
lap exactly `κ`, since `B·t₀ = 5κ/5 = κ`, and the instants only increase. A move at lap `Q`
multiplies the instant by less than `(nQ+1)/(nQ−1)` (§7). Composing, a cascade whose laps are all at
least `κ` and whose ratio reaches `c` takes at least

```
    log c / log( (5κ+1)/(5κ−1) )   ~   (5κ/2)·log c
```

steps. The verification gives `R → 3/2`, so what remains is a lower bound on `R` along the family:
an inequality in three parameters. The growth bound it composes with is already a theorem.

## 10. The certificate rules

Each rule below is a decidable condition on the disparity set together with a named instant, and a
proof that the instant is lonely whenever the condition holds. Each is elementary. Each is proved
at general `n` unless stated.

| rule | condition on the disparity set | the instant it names |
|---|---|---|
| **R1** the ratio condition | `d_max ≤ (n−1)·d_min` | `1/(n·d_min)` |
| **R2** the band ladder | every disparity in `[(nL+1)e/(nj+1), (nL+n−1)e/(nj+1)]` for some `j, L` | the `j`-th opening of `e` |
| **R3** the non-resonant flank | `gcd(e, n) = 1` and no disparity divisible by `n` | `a = e·(e⁻¹ mod n)` |
| **R4** the divisible flank *(`n` prime)* | `n \| e`, no other disparity divisible by `n`, `e` largest | `a = r·e + 1`, `r` from a pigeonhole |
| **R5** the self-similar reduction | every non-flank disparity a multiple of `n` | inherited from the problem at modulus `e` |
| **R6** the divisibility rules | for some `q ≤ n`, no disparity divisible by `q` | `t = 1/q` |
| **R7** the free disparity | one disparity off the `P`-lattice of the rest; the rest at most three and sharing it | inherited from the reduced set |

Each row is a theorem; what the table compresses, the following unpacks.

**R1, the ratio condition.** If no disparity exceeds `n−1` times the least, every reading at the
earliest possible instant lies in `[1, n−1]`, hence at distance at least 1 from `n·ℤ`. This is
Theorem 5.2, and it is the widest single rule.

**R2, the band ladder.** Fix a flank `e` and an opening index `j`. The reading of `d` there is
`(d/e)(nj+1)`, so `d` is clear when that quantity lands between consecutive multiples of `n`, at
distance at least 1 from each. Writing `L` for which multiple — a lap counter — and requiring **one
shared `(j, L)` for every disparity at once**, the condition becomes
`(nL+1)e/(nj+1) ≤ d ≤ (nL+n−1)e/(nj+1)`: all disparities in a single band. Here `e`, `j` and `L` are
all existential, `L` does not vary with `d`, and `j` ranges over `0 ≤ j < e`. At `j = L = 0` the
band is `[e, (n−1)e]`, which with the flank at `d_min` is R1 exactly — so R1 is R2's zeroth rung,
and R2 is R1 restated at every opening index. Eliminating `L` gives a necessary condition with no
`L` in it: `(d_max − d_min)(nj+1) ≤ e(n−2)`.

**R3, the non-resonant flank.** Choose a disparity `e` coprime to `n`. If no disparity is divisible
by `n`, the inverse of `e` modulo `n` supplies an opening at which every disparity lies in the band:
take `a = e·s` with `e·s ≡ 1 (mod n)`, so the reading of `d` is `e·(d·s mod n)`, which is in band
exactly when `n ∤ d·s`, and since `s` is a unit that is exactly `n ∤ d`.

**R4, the divisible flank.** The complementary case, when the flank *is* divisible by `n`. A
pigeonhole over the units modulo `n` supplies a multiplier `r` making every other disparity's
reading land in band, provided no other disparity is divisible by `n` and the flank is the largest.
The pigeonhole needs more units than disparities, which is why this rule carries `n` prime; §11
shows the hypothesis is `φ(n) = n − 1` and not Euclid's lemma.

**R5, the self-similar reduction.** If every non-flank disparity is a multiple of `n`, say `n·m'`,
its reading is `n·((m'·a) mod e)` — the scale factors through the modulus — so the whole condition
is the same problem at modulus `e` rather than `n·e`, one scale down.

**R6, the divisibility rules.** For `q ≤ n`, the instant `1/q` is lonely exactly when no disparity is
divisible by `q`: the reading of `d` is `(d mod q)/q`, which is at distance at least `1/n` from the
integers precisely when it is nonzero, since `q ≤ n`. That is `n − 1` rules, one for each
`q = 2, …, n`, and each is an equivalence rather than an implication.

**R7, the free disparity.** Stated for arbitrary real disparity sets. Suppose one disparity `x` has
irrational ratio to the others — more generally, sits off the lattice `{ y : P·(y/e) ∈ ℤ }` that the
others share for some integer `P` — and the others number at most three. Then the others are settled
at some flank by the small-cardinality result, and `x`, being off the lattice, cannot obstruct a
whole residue class of that flank's openings, so one of them is clear of `x` too.

**Any exhibited witness certifies its flank.** If `a ≡ 1 (mod n)` with `a < n·e` and every reading
`d·a mod n·e` lies in `[e, (n−1)e]`, the corresponding opening is lonely. This is not a rule with a
condition but the general form of one, and R1–R7 are instances of it.

R1 is Theorem 5.2, and R2 contains it as its zeroth rung.

R6 stands apart in one respect: its instants depend on the disparity set only through divisibility,
and are indexed by `q` rather than by any member of the set. `t = 1/2` asks that every disparity be odd; `t = 1/3` that none be divisible by three;
`t = 1/q` for `q ≤ n` that none be divisible by `q`. The rule strengthens with the order, because
the band `[1/n, 1 − 1/n]` widens while each disparity excludes only `2/n` of the residues. It is
also an equivalence: for `2 ≤ q ≤ n`, the instant `1/q` is lonely **exactly** when no disparity is
divisible by `q`.

R7 is stated for arbitrary real disparity sets. A disparity incommensurable with the others helps:
its readings meet every residue class of a flank's openings, so some opening in any class it is
offered is clear of it. The disparity sets that resist the rules are the commensurable ones.

### 10.1 What the rules' failure conditions are

A rule that only fires is a measurement. A rule whose failure is characterised is a case in a case
analysis, and cases compose.

> **R6 fails** exactly when the disparity set covers every modulus in `[2, n]` by divisibility —
> in particular when every prime `p ≤ n` divides some disparity.
>
> **R3 applies** exactly when no disparity is divisible by `n` and some disparity is coprime to it.
>
> **R5 applies** exactly when at most one disparity avoids `n`.

Two consequences. R3 is subsumed: its condition is the `q = n` instance of R6, and R6 does not even
require a coprime flank to exist. And R3 and R5 are the two ends of a single count, which §12 makes
precise.

---

## 11. `φ(n)`, and why primality was never the mechanism

R3 was first proved with `n` prime. The hypothesis was used in exactly two places: to obtain
`gcd(e, n) = 1` from `n ∤ e`, and to split `n | d·s` by Euclid's lemma. Neither needs a prime. Take
coprimality as the hypothesis, and the second follows because `s` is a unit.

The witness is `a = e·s` where `e·s ≡ 1 (mod n)`, and the readings are `e·(d·s mod n)`. The band
holds exactly when `n ∤ d·s`, which since `gcd(s,n) = 1` is exactly `n ∤ d`. Nothing in that is
prime.

So the condition is that the flank be **non-resonant**, `gcd(e, n) = 1`. At prime `n` that
coincides with `n ∤ e`, which is why primality appeared load-bearing. The usable flanks are the
residues coprime to `n`, and there are `φ(n)` of them:

| `n` | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 15 | 16 |
|---|---|---|---|---|---|---|---|---|---|---|
| `φ(n)/n` | .800 | .333 | .857 | .500 | .667 | .400 | .909 | .333 | .533 | .500 |

Primality is the top of that scale, not a switch: `φ(p)/p = 1 − 1/p`. Evenness is a consequence and
not a cause: `2 | n` forces `φ(n)/n ≤ 1/2`, which is why even orders look uniformly worse. Neither
rule predicts the two orders that separate them — order 9, odd and composite, sits at `2/3`, and
order 15, odd and not a prime power, at `8/15`, no better than order 16.

The same quantity governs R4. Its pigeonhole ranges over the units, `φ(n)` of them, so its budget
is `|L| < φ(n)`. A subject has `n − 2` non-flank disparities, so R4 needs `n − 2 < φ(n)` — and since
`φ(n) ≤ n − 1` with equality only at primes, that holds **exactly at prime `n`**. The primality in
R4 is `φ(n) = n − 1`, not Euclid's lemma.

This is the same `φ(n)` that counts the global instants in Theorem 3.4: the units of `ℤ/n`
count both the instants at which the regular progression isolates every runner at once, and the
disparities a rule may use as a flank.

---

## 12. The trichotomy, and what is open

Write `M` for the number of disparities divisible by `n`, and `c` for the number of disparities.

| region | standing |
|---|---|
| `M = 0` | **closed** — R6 at `q = n`, equivalently R3 |
| `M ≥ c − 1` | **closed** — R5, with the lone non-multiple as the flank |
| `1 ≤ M ≤ c − 2` | **open**. R4 reaches `M = 1` when the multiple is the largest disparity |

The split is exhaustive. The two closed regions are the two ends of one count, and the open region
is its middle.

**What the middle is.** A disparity divisible by `n`, say `n·m'`, has reading

```
    (n·m'·a)  mod  n e   =   n · ( (m'·a)  mod  e ),
```

so its band condition is a band condition at modulus `e`, and it depends on `a` only through
`ρ = a mod e`. A disparity not divisible by `n` needs all of `a`. So the middle region is a
**self-similar copy of the same problem one scale down**, constrained additionally by the
non-multiples. R3 is the case where the first part is empty; R5 is the case where the second is.
Neither proof reaches a set with both, and the reason is structural rather than a matter of effort.

**The reduction is a recursion.** Scaling a disparity set by `n` and taking the flank `n·f`
reduces exactly to the problem at flank `f`, a strictly smaller modulus. That closes R5's induction.

**Why it does not reach the middle, concretely.** Take `ds = {1, 2, 3, 5}` at order five. Here
`M = 1` and `c = 4`, so this sits in the middle. The recursion asks for the set in the shape
`{ n·f } ∪ n·(others)` — every member a multiple of `n`. Scaling down by 5 sends `5 ↦ 1`, but
`1, 2, 3` are not multiples of 5 and have nowhere to go: the set does not scale. That is the whole
obstruction, and it is structural rather than a matter of effort. The recursion moves a set down
only when all of it moves together.

The set is nonetheless lonely, and the rules do reach it — the flank `e = 3` works at `j = 2`, and
so does `e = 5` at `j = 1`. What is missing is a *rule* that names which. The example of §7.1 is
also in the middle at order eight (`M = 1`, `c = 7`), and there R6 names one at `q = 6`. So the
middle is not uniformly hard; it is the region where no rule presently selects the flank.

**What the middle needs.** A condition on the disparity set under which some flank and some index
can be shown to exist — by pigeonhole, induction, contradiction or construction. Existence is what a certificate requires.

### 12.1 The reach of the rules, and how to read it

On any finite enumeration of whole-number disparity sets the rules leave a residue, and we report
it as a count. A count over an enumeration measures that enumeration: the conjecture's domain
carries no canonical measure, and the same rule scores differently under different sampling schemes.
Such figures indicate which rule does which work.

---

## 13. General `n`

Nothing in §§3–7 depends on the order. Theorem A, the boundary-set method, Construction,
Localisation and the flank formulation are proved at general `n` and instantiate at six, seven and
eight at no cost.

Two facts about small orders are worth recording because they invert the expected difficulty.

**Four disparities are settled at orders six and seven and not at five.** The four-difference
termination result carries the hypothesis `n ≥ 6`. So at six and seven every subject with at most
four distinct disparities is settled unconditionally, by the theorem that is unavailable at five. In
that respect order five is the hard one.

**Order five reduces to `card = 4` exactly.** Subjects with at most three disparities are settled at
every order `n ≥ 4`. And the case cannot be dodged by collapse: the absolute value `|vᵢ − v_k|` can
identify a runner ahead with one behind, but for the fastest and the slowest runner every difference
has one sign, so both extreme subjects of every arrangement carry the full `n − 1` disparities.

---

## 14. Formal verification

Every numbered result above except Observation 9.1 — which is flagged at its statement as verified
and not derived — is formalised in Lean 4 with mathlib, with no `sorry`, no `native_decide`, no
`unsafe` and no `admit`, and every theorem depending on at most `propext`, `Classical.choice` and
`Quot.sound`. Three artefacts carry it, each built by an explicit gate; the largest holds 4,759
theorems, of which 283 are structural and the remainder are generated instances of a single
criterion applied to an enumerated family. The declarations below are the ones this paper's results
depend on.

The formalisation is a verification of the stated claims and their dependencies. It is not part of
the mathematical argument, and nothing below should be read as requiring it. Theorem 3.4 is Palelei
(2026, Theorem 3.1) and appears here because this paper formalises it, not because it is claimed as
new; the same applies to the boundary set method of §4.

| result | declaration |
|---|---|
| Theorem 3.1 | `lonely_iff_flanks` |
| Theorem 3.2 | `gaps_all_eq` |
| Corollary 3.3 | `lonely_ne_pred` |
| Theorem 3.4 *(Palelei 2026)* | `isolation_iff_coprime`, `card_coprime_eq_totient`, `ap_reference` |
| Theorem 3.5 | `displacement` |
| Theorem 3.6 | `survives_of`, `commensurable` |
| Theorem 5.1 | `bound_le_of_lonely` |
| Theorem 5.2 | `ratio_condition` |
| Theorem 6.1 | `lonely_iff_exists_flank` |
| Theorem 6.2 | `clear_at_int_flank_iff_emod`, `flankWorks_iff`, `band_iff_beatty` |
| Theorem 8.1 | `lonely_of_fixed`, `first_isolation_of_fixed`, `first_isolation_as_zone_run`, `flank_at_first_isolation` |
| Theorem 8.2 | `bound_le_of_lonely`, `iterate_le_of_lonely`, `exists_fixed_of_lonely` |
| **Theorem A** | `doors_agree` (order 8), `LRC.SpecN.doors_agree` (general `n`) |
| R1 | `ratio_condition`, `clear_at_last_opening` |
| R2 | `lonely_flank_of_band`, `bandFits_forces_spread`, `spread_zero_iff_ratio` |
| R3 | `flankWorks_of_coprime`, `flankWorks_of_not_resonant` |
| R4 | `flankWorks_of_prime_dvd`, `exists_goodK` |
| R5 | `flankWorks_of_multiples`, `flankWorks_scale` |
| R6 | `ratWorks_le_order`, `ratWorks_one_iff`, `ratWorks_family_fails_iff` |
| R7 | `lonely_of_one_free`, `lonely_of_one_irrational` |
| the general witness form | `flankWorks_of_witness` |
| §11's `φ(n)` count | `card_nonresonant_eq_totient`, `shifted_budget_is_totient` |
| §12's trichotomy | `multiples_trichotomy`, `self_rule_applies_iff`, `coprime_rule_applies_iff` |
| Observation 9.1 | verified in exact rational arithmetic; **not formalised**, and flagged as an observation |

One body of material in the development record is deliberately absent here: an enumerated census of
difference-set families, which was evidence for the record rather than mathematics for the paper.
Theorem 6.2 together with the general witness form already gives a mechanical decision procedure for
integer disparity sets, so nothing in the paper depends on it.

Each gate builds every module by explicit target, inventories `sorry`, scans for
`native_decide`/`unsafe`/`admit`, runs `#print axioms` on every declaration, and asserts its own
coverage against an independent count. One gate additionally maintains a register of every
Prop-valued definition, because such a definition is type-checked and never proved: a false one
passes a build, a `sorry` scan and an axiom check alike. Details, digests and the gate outputs are
in the development record.

---

## 15. Glossary

**arrangement** — an injective assignment of real speeds to the `n` runners.
**band** — the readings at circle distance at least `1/n` from the integers.
**boundary set method** — evaluate open cells and boundary points separately; never merge touching
zones; decide a cell by an interior point.
**cascade** — the sequence of moves from the bound.
**certificate** — a flank and an opening index, `(e, j)`, together with a proof that the opening is
lonely.
**disparity** — one of the subject's speed differences `|vᵢ − v_k|`; the term avoids collision with the *common difference* of a progression.
**global instant** — an instant at which all `n` runners are lonely at once.
**flank** — a disparity used as the denominator of a candidate instant.
**in the way** — at circle distance strictly less than `1/n` from the subject.
**move** — the step sending `t` to the largest next opening among the runners in the way.
**non-resonant** — coprime to `n`.
**opening** — the instant `(j + 1/n)/e`, at which the flank `e` sits at exactly `1/n`.
**reading** — the quantity `d·t`, or `s·u` in the local coordinate.
**resonant** — sharing a factor with `n`.
**subject** — the runner whose loneliness is at issue.

---

## References

Barajas, J. and Serra, O. (2008). The lonely runner with seven runners. *Electron. J. Combin.* 15,
R48.

Bohman, T., Holzman, R. and Kleitman, D. (2001). Six lonely runners. *Electron. J. Combin.* 8(2),
R3.

Palelei, T. (2026). The φ(n) law for arithmetic progressions in the lonely runner conjecture:
algebraic structure and computational fragility. Zenodo.
https://doi.org/10.5281/zenodo.18158886

Rosenfeld, M. (2025). The lonely runner conjecture holds for eight runners. arXiv:2509.14111.
Preprint.

*Full references, the development record, the version history, the record of routes closed, and the
verification apparatus are in `MANUSCRIPT_v20.md`.*
