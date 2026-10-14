# A Bounding Framework for Eight Lonely Runners

**T. Palelei.** Draft v1, 2026-09-22. Submission draft, extracted from `MANUSCRIPT_v20.md`, which
remains the manuscript of record and holds the development history, the verification apparatus and
the record of routes closed. Nothing here is new relative to that document; what is new is the
order of presentation and the separation of two claims that it stated together.

---

## 1. Introduction

Let `v₁, …, vₙ` be distinct real speeds. The Lonely Runner Conjecture asserts that each runner is,
at some instant, at circle distance at least `1/n` from every other. At `n = 8` the case has been
settled by computer verification (Rosenfeld 2025, preprint). This paper is not a second proof of
that statement.

It is an account of a different object: a deterministic procedure, driven by the speeds alone, that
either exhibits a lonely instant or does not halt — and a proof that it halts exactly when the
runner is lonely. Two things follow, and this paper is careful to keep them apart, because a single
word covering both has caused every misreading of earlier drafts.

> **Theorem A (the equivalence).** For every injective `v : Fin 8 → ℝ` and every subject `k`, each
> of four conditions on the procedure — that it halts; that its instants are bounded; that some
> *flank* has a clear *opening*; that each runner obstructs at only finitely many steps — is
> **equivalent** to the subject being lonely at some positive instant. Both directions, no
> hypothesis beyond injectivity.
>
> **Proved here.** §7.

> **Theorem B (the derivation).** A collection of explicit rules, each a decidable condition on the
> subject's difference set paired with a named instant, together with a proof that the named
> instant is lonely whenever the condition holds.
>
> **Partial.** The rules proved here are listed in §9 with their conditions; the conditions are not
> yet jointly exhaustive, and §11 identifies exactly the class that remains.

Theorem A is a statement about the framework's objects and the conjecture. It says the procedure is
not an approximation to loneliness, nor a sufficient condition for it, but the same statement in
different vocabulary. It supplies no instant and closes no case.

Theorem B is the work of producing instants. Each rule is elementary and constructive: given a
difference set satisfying its condition, it names `(e, k)` and the instant `(k + 1/8)/e` is lonely.
Together the rules cover a large and describable class of difference sets. They do not yet cover
all of them.

**Neither theorem is stated as, nor implies, a new proof of the conjecture at eight runners**, and
no claim in this paper should be read that way. What Theorem A gives is a reformulation whose
objects are finite and arithmetic; what Theorem B gives is an elementary derivation on the class
its conditions reach.

### 1.1 What is distinctive

Three features of the framework are worth stating before the definitions.

**The scale is per-runner and autonomous.** No runner is pinned to zero, and no global clock is
imposed. Each subject is analysed in its own differences and its own time coordinate.

**The procedure is search-free.** At each step the runners currently obstructing the subject
determine the next step uniquely. Nothing is guessed, ranked, or chosen from a candidate list.

**The certificate is piecewise by construction.** There is no single closed form for the lonely
instant in sight, and §8 argues that expecting one is the wrong shape of expectation. What the
framework produces is a collection of exact rules with different conditions.

### 1.2 What a certificate is, and three shapes that are not required

The conjecture asks for a lonely instant to *exist*. It carries no obligation about when that
instant falls, how many steps of any procedure reach it, or what form a description of it takes.
Three stronger statements are therefore **not** what a certificate must supply, and §8 shows that
the distinction is not academic.

| stronger statement | what it would additionally require |
|---|---|
| a **cap** — a bound on how far the procedure runs | a bound on the run, which the conjecture does not ask for |
| a **move count** — "the `N`-th step is fixed", for a fixed `N` | a bound on how many steps, likewise not asked for — and §8.2 shows that at order five no such `N` exists |
| a **uniform witness formula** — a closed form `(e, k) = f(v)` | a formula, where existence is what is owed |

The third is worth naming carefully. Uniform *theorems* are exactly what this paper proves —
Theorem A is one, and so are the results of §4. What is not required is a uniform *witness
formula*: a single expression producing the flank and the index from the arrangement. A rule that
proves `∃ (e, k)` by pigeonhole, by contradiction or by induction discharges its case completely.

Counting arguments are admissible as **tools** throughout. What the framework does not do is state
its target as a covering — forming a complement and showing it empty.

---

## 2. Notation

| symbol | meaning | introduced |
|---|---|---|
| `n` | the number of runners; `n = 8` unless stated | §1 |
| `v : Fin n → ℝ` | an **arrangement**: injective speeds | §1 |
| `k` | the **subject**, the runner whose loneliness is at issue | §1 |
| `‖x‖` | circle distance from `x` to the nearest integer, `min(frac x, 1 − frac x)` | §3 |
| `d` | a **disparity**: `\|vᵢ − v_k\|` for some `i ≠ k` | §3 |
| `ds` | the subject's set of disparities; `\|ds\| ≤ n − 1` | §3 |
| `m`, `d_min` | the least disparity | §4 |
| `d_max` | the greatest disparity | §4 |
| `t` | time | §3 |
| `u` | the local time coordinate `d_min · t` | §4 |
| `e` | a **flank**: a disparity used as the denominator of a candidate instant | §5 |
| `k` (as index) | the **opening index** of a flank; context distinguishes it from the subject | §5 |
| `(k + 1/n)/e` | the `k`-th **opening** of the flank `e` | §5 |
| `S` | the **ratio** `d_max / d_min` | §9 |
| `R` | the ratio of the halting instant to the bound `1/(n·d_min)` | §8 |
| `φ` | Euler's totient | §10 |
| `M` | the number of disparities divisible by `n` | §11 |

A reading is a quantity `d · t`; a **band** is the set of readings at circle distance at least
`1/n` from the integers, namely `[1/n, 1 − 1/n]` modulo 1.

## 3. Loneliness, and why the boundary matters

Fix a subject `k`. Runner `i` sits at circle distance `‖(vᵢ − v_k)t‖` from the subject at time `t`.

> **Definition.** The subject is **lonely at `t`** when `‖d·t‖ ≥ 1/n` for every disparity `d`.

The condition is closed: a runner at distance exactly `1/n` does not obstruct. Correspondingly, the
set of times at which a given runner *does* obstruct is a union of **open** intervals,

```
    ( (N − 1/n)/d , (N + 1/n)/d ),     N ∈ ℤ,
```

one about each of that runner's relative laps. We call these the runner's **in-the-way zones**, and
the endpoints belong to the complement.

That the zones are open, and the loneliness condition closed, is not a technicality. It has two
consequences the rest of the paper depends on.

**Endpoints are clear.** At `t = (N + 1/n)/d` the runner `d` is at distance exactly `1/n`. Every
candidate instant this paper constructs is such an endpoint, for some runner and some lap.

**A cell cannot be decided by its endpoints.** Partition the positive axis by all the zone
endpoints of all the disparities. Within one cell every runner's status is constant, so a cell is
decided by any interior point. But the endpoints bounding a cell may both be clear while the cell's
interior is not — the two bounding zones can be different runners' zones, overlapping across the
cell. Deciding a cell therefore requires an interior point, and never an endpoint.

This is the **boundary set method**: evaluate open cells and boundary points separately, never
merge touching zones, and decide a cell by an interior point.

### 3.1 Loneliness is a two-neighbour condition

At any instant the `n` runners cut the circle into `n` cyclic gaps summing to 1.

> **Theorem 3.1.** Runner `i` is lonely if and only if both gaps flanking it are at least `1/n`.

The converse needs only the two flanking pairs, and not the attainment of any minimum. Two
consequences fix the shape of the problem.

> **Theorem 3.2.** All `n` runners are simultaneously lonely if and only if every gap is exactly
> `1/n` — the regular `n`-gon.

> **Corollary 3.3.** The number of simultaneously lonely runners lies in `{0, …, n−2} ∪ {n}`. It is
> never exactly `n − 1`.

Theorem 3.2 is what makes the regular progression the extremal configuration throughout, and
Corollary 3.3 is a conservation law: the gaps sum to 1, so one runner cannot be the only one
excluded.

## 4. The local scale

Normalise by the nearest runner. Writing `u = d_min · t`, each disparity `d` has a **ratio**
`s = d / d_min ≥ 1`, and the reading of `d` at time `t` is `s · u`.

> **Theorem 4.1 (the bound).** If the subject is lonely at `t > 0`, then `t ≥ 1/(n·d_min)`; that is,
> `u ≥ 1/n`.

Below that instant the nearest runner has not yet left the subject. The bound is the natural
starting point for any search, and it is where the procedure of §6 begins.

> **Theorem 4.2 (the ratio condition).** If `d_max ≤ (n−1)·d_min` then the subject is lonely at
> `u = 1/n`, that is at `t = 1/(n·d_min)`.

Immediately: at that instant every reading `s` lies in `[1, n−1]`, hence at distance at least 1
from `n·ℤ`. The constant `n − 1` is one below the first multiple of `n`, and is not special to
eight. Theorem 4.2 is the first and widest single rule, and it settles a subject outright whenever
the spread of its disparities is within a factor of `n − 1`.

---

## 5. Flanks and openings

> **Definition.** For a disparity `e` and an integer `k ≥ 0`, the `k`-th **opening** of the flank
> `e` is the instant `(k + 1/n)/e`.

At such an instant the runner `e` sits at distance exactly `1/n` — on the boundary, hence clear —
and the content of the condition is carried by the other disparities. The following says the family
loses nothing.

> **Theorem 5.1.** The subject is lonely at some positive instant if and only if some flank has a
> lonely opening.

The forward direction is the substantive one: from any lonely `t`, the opening `(⌊e·t⌋ + 1/n)/e` of
a suitable disparity `e` is lonely and no later than `t`. So a search for lonely instants may be
confined to this countable family without loss.

For whole-number disparities the family is finite and the condition is arithmetic.

> **Theorem 5.2.** Let the disparities be positive integers and `e` one of them. The opening `k` of
> the flank `e` is lonely if and only if
>
> ```
>     d · (n k + 1)  mod  n e   ∈   [ e , (n−1) e ]        for every disparity d.
> ```
>
> The reading is periodic in `k` with period exactly `e`, so the search `0 ≤ k < e` decides the
> question. No real number survives in the criterion.

Written on the floor rather than the residue, the same condition reads

```
    ⌊ d · a / e ⌋  mod  n   ∈   {1, …, n−2},    or  = n−1 with e | d·a,
```

where `a = n k + 1`. So `⌊d·a/e⌋` is the Beatty sequence of slope `d/e`, and an opening index is a
point at which `|ds| − 1` Beatty sequences simultaneously avoid two residues modulo `n`. The flank
itself is free, since `d = e` gives `⌊a⌋ = a ≡ 1 (mod n)`.

Two remarks. Every opening index `a = nk + 1` is coprime to `n`; the framework never exhibits a
witness outside the unit group of `ℤ/n`. And the clause `= n−1 with e | d·a` is the closed endpoint
of the band and is not optional: dropping it makes difference sets appear to have no working
opening when in fact they do.

---

## 6. The procedure, and a worked example

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

### 6.1 A complete example

Take the arrangement `0, 1, 2, 3, 4, 5, 7, 8` and the subject at speed `0`, whose disparities are

```
    ds = { 1, 2, 3, 4, 5, 7, 8 },      d_min = 1,      bound t₀ = 1/8.
```

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
which was exactly on the boundary at step 0, has been carried just past its lap and is now in the
way at distance `1/64`. Its next opening is `(1 + 1/8)/7 = 9/56`, and the move goes there.

**Step 2, `t = 9/56`.** The readings are

| `d` | 1 | 2 | 3 | 4 | 5 | 7 | 8 |
|---|---|---|---|---|---|---|---|
| `‖d·t‖` | 9/56 | 9/28 | 27/56 | 5/14 | 11/56 | **1/8** | 2/7 |

Every distance is at least `1/8`. No runner is in the way, the move fixes `t`, and the subject is
lonely at `t = 9/56`.

**Reading off the certificate.** The halting instant is `9/56 = (1 + 1/8)/7`, which is the opening
`k = 1` of the flank `e = 7`. So the certificate is the pair `(e, k) = (7, 1)`, and runner 7 sits at
exactly one eighth — as Theorem 6.1(d) below says it must.

The cascade took two moves. Nothing in the certificate records that; the pair `(7, 1)` is what is
exhibited, and it can be checked in seven divisions without reference to the procedure that found
it. This is the distinction §8 makes precise.

---

## 7. Construction, Localisation, and Theorem A

> **Theorem 6.1 (Construction).** If some step of the cascade is fixed, at `T`, then: the subject is
> lonely at `T`; no positive instant before `T` is lonely; `T` is the end of a run of
> lap-completion zones from the bound, each containing the end of the one before; and some runner
> sits at exactly `1/n`, as the nearest ahead or the nearest behind.

So a fixed point is not merely *a* lonely instant. It is the **first** one, it terminates a
boundary-set run, and it carries a runner at the threshold — which is why the halting instant is
always an opening, and why the certificate has the form `(e, k)`.

> **Theorem 6.2 (Localisation).** For every positive instant `s` at which the subject is lonely:
> `s ≥ 1/(n·d_min)`; every step of the cascade is at most `s`; `s` is matched by a lonely opening no
> later than it; and **the cascade reaches a fixed point**.

The last clause is the direction that carries the equivalence, and its proof is a finiteness
argument and nothing else: below `s` the cascade's steps lie in the finite set of openings
`(k + 1/n)/d` with `0 ≤ k ≤ ⌈d·s⌉`, and a strictly increasing sequence cannot remain in a finite
set.

Together:

> **Theorem A.** For every injective arrangement and every subject, the following are equivalent:
>
> 1. the subject is lonely at some positive instant;
> 2. the cascade reaches a fixed point;
> 3. the cascade's instants are bounded above;
> 4. some flank has a lonely opening;
> 5. each runner is in the way at only finitely many steps.
>
> Both directions, each way, with no hypothesis beyond injectivity.

**What Theorem A is.** It identifies the framework's objects with the conjecture's. The procedure
halting is not evidence that the runner is lonely, nor a sufficient condition for it: it is the same
statement. Whatever is true of one is true of the other, at every arrangement and every subject.

**What Theorem A is not.** It supplies no instant, no bound and no case. It is a change of
vocabulary in which the conjecture becomes a statement about finite arithmetic objects — and the
work of *deriving* those objects is Theorem B, which is partial.

The distinction matters because the two are easy to run together. A reader who takes Theorem A
together with the known truth of the conjecture at eight runners may conclude that the procedure
halts everywhere, and that conclusion is correct. It is also not a derivation, and this paper does
not present it as one.

---

## 8. The scope of a certificate

A certificate is a pair `(e, k)` together with a proof that the opening is lonely. The conjecture
asks for such a pair to exist. It asks for nothing about when the instant falls, how many steps of
any procedure reach it, or whether the pair is given by a formula.

The three stronger statements of §1.2 are therefore outside the target. Two of them are merely
stronger. The second is **false**, and that is worth demonstrating, because a reader who has not
seen the demonstration will keep reaching for it.

### 8.1 Where the time can be read, and where it cannot

No result here requires a bound on when an instant falls, and none is confined to a first lap or a
window. Bounds of the form `R < c` are sufficient conditions at most. The following is why.

### 8.2 At order five there is no move count

At orders three and four, and at order `n ≥ 6` with four disparities, the cascade halts within a
fixed number of steps, and the corresponding theorems have that shape: *the `N`-th iterate is
fixed*. At order five with four disparities no such `N` exists.

> **Theorem 8.1.** The difference sets `(1, 5κ − 2, 5κ, 10κ − 2)` have cascade length `2κ + 1` for
> even `κ`. Verified in exact rational arithmetic to `κ = 100`, length 201.

So for every `N` there is a five-runner difference set whose `N`-th iterate is not fixed. The
move-count shape is not unproved at order five; it is unavailable.

What stays bounded along that family is the ratio `R` of the halting instant to the bound: it tends
to `3/2`, nowhere near the value a cap would need. **Termination and short termination are
different properties, and they come apart at order five.** That is the demonstration, and it is why
a certificate is a pair and not a count.

### 8.3 Why analytic location fails at the extremal configuration

One further scope statement has a proof rather than a preference, and it is a structural fact about
the object.

> **Theorem 8.2.** At the arithmetic progression — readings `1, 2, …, n−1` — the set of instants in
> `(0, 2]` at which the subject is lonely is exactly
>
> ```
>     { 1/n, 3/n, 5/n, …, (2n−1)/n },
> ```
>
> a finite set of isolated points, of Lebesgue measure zero. Equivalently: the clear instants are
> the residues coprime to `n`, of which there are `φ(n)` per period.

Every analytic method locates a target through neighbourhoods. At the arithmetic progression there
are none, and the arithmetic progression is precisely the configuration at which any method must
succeed, since Theorem 3.2 makes it the extremal one. This closes no case and supplies no bound; it
states why the framework works in exact arithmetic and lap geometry rather than in measure or
density.

The φ(n) in Theorem 8.2 is not incidental, and §10 shows it is the quantity that governs the rules.

---

## 9. Theorem B: the rules, with their conditions

Each rule below is a decidable condition on the difference set together with a named instant, and a
proof that the instant is lonely whenever the condition holds. Each is elementary. Each is proved
at general `n` unless stated.

| rule | condition on the difference set | the instant it names |
|---|---|---|
| **R1** the ratio condition | `d_max ≤ (n−1)·d_min` | `1/(n·d_min)` |
| **R2** the band ladder | every disparity in `[(nM+1)e/(nk+1), (nM+n−1)e/(nk+1)]` for some `k, M` | the `k`-th opening of `e` |
| **R3** the non-resonant flank | `gcd(e, n) = 1` and no disparity divisible by `n` | `a = e·(e⁻¹ mod n)` |
| **R4** the divisible flank | `n \| e`, no other disparity divisible by `n`, `e` largest | `a = κ·e + 1`, `κ` from a pigeonhole |
| **R5** the self-similar reduction | every non-flank disparity a multiple of `n` | inherited from the problem at modulus `e` |
| **R6** the divisibility rules | for some `q ≤ n`, no disparity divisible by `q` | `t = 1/q` |
| **R7** the free disparity | one disparity off the `P`-lattice of the rest; the rest at most three and sharing it | inherited from the reduced set |
| **R8** the witness certificate | any exhibited `a ≡ 1 (mod n)`, `a < n·e`, with all readings in band | the corresponding opening |

R1 is Theorem 4.2. R2 subsumes it: eliminating `M` from R2's condition gives
`(d_max − d_min)(nk+1) ≤ e(n−2)`, and at `k = 0` with the flank at `d_min` that inequality *is*
R1. So R1 is R2's zeroth rung, and the ladder is R1 stated at every opening index.

R6 is worth isolating because it is the only family whose instants are not indexed by the
arrangement. `t = 1/2` asks that every disparity be odd; `t = 1/3` that none be divisible by three;
`t = 1/q` for `q ≤ n` that none be divisible by `q`. The rule strengthens with the order, because
the band `[1/n, 1 − 1/n]` widens while each disparity excludes only `2/n` of the residues. It is
also an equivalence: for `2 ≤ q ≤ n`, the instant `1/q` is lonely **exactly** when no disparity is
divisible by `q`.

R7 is the only rule stated for arbitrary real difference sets rather than whole-number ones. It
matters because a disparity incommensurable with the others is not an obstacle but a help: such a
disparity can never obstruct a whole residue class of openings, so it can never be the runner that
defeats a flank. The difficult difference sets are the commensurable ones.

R8 is not a rule with a condition but the general form of one: any exhibited `a` certifies its
flank. Every other rule is an instance.

### 9.1 What the rules' failure conditions are

A rule that only fires is a measurement. A rule whose failure is characterised is a case in a case
analysis, and cases compose.

> **R6 fails** exactly when the difference set covers every modulus in `[2, n]` by divisibility —
> in particular when every prime `p ≤ n` divides some disparity.
>
> **R3 applies** exactly when no disparity is divisible by `n` and some disparity is coprime to it.
>
> **R5 applies** exactly when at most one disparity avoids `n`.

Two consequences. R3 is subsumed: its condition is the `q = n` instance of R6, and R6 does not even
require a coprime flank to exist. And R3 and R5 are the two ends of a single count, which §11 makes
precise.

---

## 10. `φ(n)`, and why primality was never the mechanism

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

This is the `φ(n)` that counts the clear instants at the arithmetic progression in Theorem 8.2. It
is the same quantity throughout.

---

## 11. The trichotomy, and what is open

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

**The reduction is a recursion.** Scaling a difference set by `n` and taking the flank `n·f`
reduces exactly to the problem at flank `f`, a strictly smaller modulus. That closes R5's induction.
It does not reach the middle: scaling sends the whole set down together, and a set with both kinds
of disparity does not scale.

**What the middle needs.** A condition under which `∃ (e, k)` is provable — by pigeonhole with the
overlaps, by induction, by contradiction, or by construction. Not a formula. Several candidate
*formulas* have been tried and refuted; none of them was what the obligation asked for.

### 11.1 The reach of the rules, and how to read it

The rules above leave a residue on any finite enumeration of whole-number difference sets. Those
counts are reported as counts, and are not a fraction of the problem: the conjecture's domain
carries no canonical measure, and the same rule scores very differently under different sampling
schemes. They say which rule does which work, and nothing about how much is done.

---

## 12. General `n`

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

## 13. Formal verification

Every numbered result above is formalised in Lean 4 with mathlib, with no `sorry`, no
`native_decide`, no `unsafe` and no `admit`, and every theorem depending on at most `propext`,
`Classical.choice` and `Quot.sound`. Three artefacts carry it, each built by an explicit gate.

| result | declaration |
|---|---|
| Theorem 3.1 | `lonely_iff_flanks` |
| Theorem 3.2 | `gaps_all_eq` |
| Corollary 3.3 | `lonely_ne_pred` |
| Theorem 4.1 | `bound_le_of_lonely` |
| Theorem 4.2 | `ratio_condition` |
| Theorem 5.1 | `lonely_iff_exists_flank` |
| Theorem 5.2 | `clear_at_int_flank_iff_emod`, `flankWorks_iff`, `band_iff_beatty` |
| Theorem 6.1 | `lonely_of_fixed`, `first_isolation_of_fixed`, `first_isolation_as_zone_run`, `flank_at_first_isolation` |
| Theorem 6.2 | `bound_le_of_lonely`, `iterate_le_of_lonely`, `exists_fixed_of_lonely` |
| **Theorem A** | `doors_agree` (order 8), `LRC.SpecN.doors_agree` (general `n`) |
| R1 | `ratio_condition`, `clear_at_last_opening` |
| R2 | `lonely_flank_of_band`, `bandFits_forces_spread`, `spread_zero_iff_ratio` |
| R3 | `flankWorks_of_coprime`, `flankWorks_of_not_resonant` |
| R4 | `flankWorks_of_prime_dvd`, `exists_goodK` |
| R5 | `flankWorks_of_multiples`, `flankWorks_scale` |
| R6 | `ratWorks_le_order`, `ratWorks_one_iff`, `ratWorks_family_fails_iff` |
| R7 | `lonely_of_one_free`, `lonely_of_one_irrational` |
| R8 | `flankWorks_of_witness` |
| §10's `φ(n)` count | `card_nonresonant_eq_totient`, `shifted_budget_is_totient` |
| §11's trichotomy | `multiples_trichotomy`, `self_rule_applies_iff`, `coprime_rule_applies_iff` |
| Theorem 8.1 | verified computationally in exact rational arithmetic; not formalised |
| Theorem 8.2 | verified computationally in exact rational arithmetic; a text proof is given in §8.3 |

Each gate builds every module by explicit target, inventories `sorry`, scans for
`native_decide`/`unsafe`/`admit`, runs `#print axioms` on every declaration, and asserts its own
coverage against an independent count. One gate additionally maintains a register of every
Prop-valued definition, because such a definition is type-checked and never proved: a false one
passes a build, a `sorry` scan and an axiom check alike. Details, digests and the gate outputs are
in the development record.

---

## 14. Glossary

**arrangement** — an injective assignment of real speeds to the `n` runners.
**band** — the readings at circle distance at least `1/n` from the integers.
**boundary set method** — evaluate open cells and boundary points separately; never merge touching
zones; decide a cell by an interior point.
**cascade** — the sequence of moves from the bound.
**certificate** — a flank and an opening index, `(e, k)`, together with a proof that the opening is
lonely.
**disparity** — one of the subject's speed differences `|vᵢ − v_k|`.
**flank** — a disparity used as the denominator of a candidate instant.
**in the way** — at circle distance strictly less than `1/n` from the subject.
**move** — the step sending `t` to the largest next opening among the runners in the way.
**non-resonant** — coprime to `n`.
**opening** — the instant `(k + 1/n)/e`, at which the flank `e` sits at exactly `1/n`.
**reading** — the quantity `d·t`, or `s·u` in the local coordinate.
**resonant** — sharing a factor with `n`.
**subject** — the runner whose loneliness is at issue.

---

## References

Barajas, J. and Serra, O. (2008). The lonely runner with seven runners. *Electron. J. Combin.* 15,
R48.

Bohman, T., Holzman, R. and Kleitman, D. (2001). Six lonely runners. *Electron. J. Combin.* 8(2),
R3.

Rosenfeld, M. (2025). The lonely runner conjecture holds for eight runners. arXiv:2509.14111.
Preprint.

*Full references, the development record, the version history, the record of routes closed, and the
verification apparatus are in `MANUSCRIPT_v20.md`.*
