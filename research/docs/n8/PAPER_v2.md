# A Bounding Framework for Eight Lonely Runners

**T. Palelei.** Draft v2, 2026-09-22. Submission draft, extracted from `MANUSCRIPT_v20.md`, which
remains the manuscript of record and holds the development history, the verification apparatus and
the record of routes closed.

---

## Abstract

For `n` runners with distinct real speeds, the Lonely Runner Conjecture asserts that each runner is
at some instant at circle distance at least `1/n` from every other. We develop, at `n = 8` and at
general `n`, a deterministic procedure driven by the speeds alone — a *cascade* on the subject's own
time scale — and prove that it halts exactly when the subject is lonely (**Theorem A**), an
equivalence with no hypothesis beyond injectivity and with both directions. The certificate it
produces is a pair `(e, j)`: a speed difference and an opening index, from which the lonely instant
is `(j + 1/n)/e` and is verified by `n − 1` modular reductions. We then give eight explicit rules,
each a decidable arithmetic condition on the subject's difference set paired with such a pair
(**the certificate rules**), and classify what their conditions do not yet reach. Two structural
results emerge. At order five the *move-count* shape — "the `N`-th step is fixed" — is unavailable:
the difference sets `(1, 5κ−2, 5κ, 10κ−2)` have cascade length growing linearly in `κ` while the
ratio of halting instant to bound tends to `3/2`, so termination and short termination come apart.
And the quantity governing the rules is Euler's totient: the usable flanks are the residues coprime
to `n`, `φ(n)` of them, and the primality that appeared in earlier statements of two rules is
`φ(n) = n − 1` rather than Euclid's lemma. All numbered results are formalised in Lean 4 except
where flagged.

---

## 1. Introduction

Let `v₁, …, vₙ` be distinct real speeds. The Lonely Runner Conjecture asserts that each runner is,
at some instant, at circle distance at least `1/n` from every other.

At `n = 8` a computer verification has been announced (Rosenfeld 2025, preprint). It is an
empirical result: it reports the outcome of a search and supplies no analytic derivation, and it
has not been through refereeing. We neither rely on it nor duplicate it. What follows is
independent of whether it stands.

This paper develops a different object: a deterministic procedure, driven by the speeds alone, that
either exhibits a lonely instant or does not halt — together with a proof that it halts exactly when
the runner is lonely. Two claims follow, and the paper keeps them apart throughout, because a single
word covering both is what made earlier drafts of this material hard to read.

> **Theorem A (the equivalence).** For every injective `v : Fin 8 → ℝ` and every subject `k`, each
> of four conditions on the procedure — that it halts; that its instants are bounded; that some
> *flank* has a clear *opening*; that each runner obstructs at only finitely many steps — is
> **equivalent** to the subject being lonely at some positive instant. Both directions, no
> hypothesis beyond injectivity. **Proved here** (§7).

> **The certificate rules (the derivation).** Eight explicit rules, each a decidable condition on
> the subject's difference set paired with a named instant, together with a proof that the named
> instant is lonely whenever the condition holds. **Partial** (§9): the conditions are not yet
> jointly exhaustive, and §11 identifies exactly the class that remains.

Theorem A is a statement relating the framework's objects to the conjecture. It says the procedure
is not an approximation to loneliness, nor a sufficient condition for it, but the same statement in
different vocabulary. It supplies no instant and settles no case.

The certificate rules are the work of producing instants. Each is elementary and constructive: given
a difference set satisfying its condition, it names `(e, j)`, and the instant `(j + 1/8)/e` is
lonely. Together they cover a large and describable class. They do not yet cover all of it.

**Neither claim is, nor implies, a proof of the conjecture at eight runners**, and nothing here
should be read that way.

**What the framework contributes at `n = 8`.** A constructive certificate on a describable class of
arrangements, verifiable in `n − 1` modular reductions and independent of the procedure that found
it; an equivalence identifying the procedure's halting with loneliness, which reformulates the
conjecture in finite arithmetic objects; and a reduction of what remains to a single arithmetic
question about one integer parameter (§11). The contribution is the framework, not a case.

**How the paper is arranged.** §3 establishes the boundary geometry — the in-the-way zones are open,
the loneliness condition closed, and a cell cannot be decided by its endpoints. §4 fixes the
subject's own scale. §5 reduces arbitrary lonely instants to *openings* of *flanks*, and shows the
resulting condition is finite and arithmetic. §6 defines the cascade and traces it completely on one
arrangement. §7 proves Construction and Localisation, and hence Theorem A. §8 says what a
certificate must and need not supply, with the order-five family as the evidence that the
distinction is not academic. §9 gives the rules; §10 shows `φ(n)` is the quantity behind two of
them; §11 classifies the remainder by one integer count and identifies what is open. §12 treats
general `n`, §13 the formal verification.

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
| a **uniform witness formula** — a closed form `(e, j) = f(v)` | a formula, where existence is what is owed |

The third is worth naming carefully. Uniform *theorems* are exactly what this paper proves —
Theorem A is one, and so are the results of §4. What is not required is a uniform *witness
formula*: a single expression producing the flank and the index from the arrangement. A rule that
proves `∃ (e, j)` by pigeonhole, by contradiction or by induction discharges its case completely.

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
| `j` | the **opening index** of a flank | §5 |
| `(j + 1/n)/e` | the `j`-th **opening** of the flank `e` | §5 |
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

> **Theorem 4.1 (the earliest possible lonely instant).** If the subject is lonely at `t > 0`, then `t ≥ 1/(n·d_min)`; that is,
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

> **Definition.** For a disparity `e` and an integer `j ≥ 0`, the `j`-th **opening** of the flank
> `e` is the instant `(j + 1/n)/e`.

At such an instant the runner `e` sits at distance exactly `1/n` — on the boundary, hence clear —
and the content of the condition is carried by the other disparities. The following says the family
loses nothing.

> **Theorem 5.1.** The subject is lonely at some positive instant if and only if some flank has a
> lonely opening.

The forward direction is the substantive one: from any lonely `t`, the opening `(⌊e·t⌋ + 1/n)/e` of
a suitable disparity `e` is lonely and no later than `t`. So a search for lonely instants may be
confined to this countable family without loss.

For whole-number disparities the family is finite and the condition is arithmetic.

> **Theorem 5.2.** Let the disparities be positive integers and `e` one of them. The opening `j` of
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
exactly one eighth — as Theorem 7.1(d) says it must.

The cascade took two moves. Nothing in the certificate records that; the pair `(7, 1)` is what is
exhibited, and it can be checked in seven modular reductions without reference to the procedure
that found it. This is the distinction §8 makes precise.

**And the rules of §9 reach this set by another route entirely.** Its largest disparity exceeds
seven times its least, so R1 does not apply; one disparity is divisible by 8, so R3 does not. But no
disparity is divisible by 6, so R6 applies at `q = 6` and names the instant `t = 1/6`, at which the
readings are `1/6, 1/3, 1/2, 1/3, 1/6, 1/6, 1/3` — all at least `1/8`.

So the cascade and the rules are two ways to a certificate, and they generally produce **different**
ones: `9/56` here against `1/6`. The cascade is a discovery procedure that always terminates when
the subject is lonely (Theorem A) and needs no condition; a rule is a shortcut that bypasses the
procedure entirely but applies only where its condition holds. Neither is the other's approximation.

---

## 7. Construction, Localisation, and Theorem A

> **Theorem 7.1 (Construction).** If some step of the cascade is fixed, at `T`, then: the subject is
> lonely at `T`; no positive instant before `T` is lonely; `T` is the end of a run of
> lap-completion zones from the bound, each containing the end of the one before; and some runner
> sits at exactly `1/n`, as the nearest ahead or the nearest behind.

So a fixed point is not merely *a* lonely instant. It is the **first** one, it terminates a
boundary-set run, and it carries a runner at the threshold — which is why the halting instant is
always an opening, and why the certificate has the form `(e, j)`.

> **Theorem 7.2 (Localisation).** For every positive instant `s` at which the subject is lonely:
> `s ≥ 1/(n·d_min)`; every step of the cascade is at most `s`; `s` is matched by a lonely opening no
> later than it; and **the cascade reaches a fixed point**.

The last clause is the direction that carries the equivalence, and its proof is a finiteness
argument and nothing else: below `s` the cascade's steps lie in the finite set of openings
`(k + 1/n)/d` with `0 ≤ k ≤ ⌈d·s⌉`, and a strictly increasing sequence cannot remain in a finite
set.

Together:

> **Theorem A.** For every injective arrangement and every subject, the following five statements
> are equivalent — loneliness, together with the four conditions on the procedure named in §1:
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
work of *deriving* those objects is the certificate rules of §9, which are partial.

The distinction matters because the two are easy to run together. A reader who takes Theorem A
together with the known truth of the conjecture at eight runners may conclude that the procedure
halts everywhere, and that conclusion is correct. It is also not a derivation, and this paper does
not present it as one.

---

## 8. The scope of a certificate

A certificate is a pair `(e, j)` together with a proof that the opening is lonely. The conjecture
asks for such a pair to exist. It asks for nothing about when the instant falls, how many steps of
any procedure reach it, or whether the pair is given by a formula.

The three stronger statements of §1.2 are therefore outside the target. Two of them are merely
stronger. The second is **false**, and that is worth demonstrating, because a reader who has not
seen the demonstration will keep reaching for it.

### 8.1 The ratio `R`, and why it is a diagnostic

Write `R` for the ratio of the halting instant to the earliest possible one, `R = n·d_min·T`. It is
a convenient measurement of how far past `1/(n·d_min)` a given subject's cascade runs — in the
example of §6.1, `T = 9/56` against `t₀ = 1/8`, so `R = 9/7`.

`R` is a diagnostic and not a target. A bound `R < c` holding for every arrangement would be
sufficient for the conjecture, and is therefore at least as strong as it; no such bound is proved
here or needed. No result below is confined to a first lap or a window, and none requires a bound
on when an instant falls.

The next subsection shows that the corresponding statement about *step counts* is not merely
stronger but false.

### 8.2 At order five there is no move count

At orders three and four, and at order `n ≥ 6` with four disparities, the cascade halts within a
fixed number of steps, and the corresponding theorems have that shape: *the `N`-th iterate is
fixed*. At order five with four disparities no such `N` exists.

> **Observation 8.1** `[VERIFIED — exact rational arithmetic, 3 ≤ κ ≤ 100; not formalised]`. At
> order five the difference sets `(1, 5κ − 2, 5κ, 10κ − 2)` have cascade length `2κ + 1` for even
> `κ` and `2κ + 2` for odd `κ`. The setter word is completely regular: writing `A = 5κ−2`,
> `B = 5κ`, `C = 10κ−2`, it is the repeated four-cycle
>
> ```
>     B@ι ,  C@2ι ,  A@ι ,  C@(2ι+1)          for ι = κ, κ+1, κ+2, …
> ```
>
> terminating in a final `B`, the last cycle truncated when `κ` is odd. Here `X@ι` means the move
> is set by disparity `X` at its lap `ι`.

This is stated as an observation and not a theorem: the length is verified, not derived. What it
indicates is that for every `N` there is a five-runner difference set whose `N`-th iterate is not
fixed, so the move-count shape is unavailable at order five rather than merely unproved.

**What would upgrade it**, recorded because the route is concrete. Every setter lap in the family is
at least `κ − 1`: the first setter is `B` at lap exactly `κ`, since `B·t₀ = 5κ/5 = κ`, and the
instants only increase. The framework's growth bound says a move at lap `Q` multiplies the instant
by less than `(nQ+1)/(nQ−1)`. So if the ratio `R` of §8.1 is bounded below by a constant `c > 1`
along the family, the number of moves is at least
>
> ```
>     log c / log( (5κ+1)/(5κ−1) )   ~   (5κ/2)·log c,
> ```
>
> which is unbounded. The verification gives `R → 3/2`, so the missing ingredient is a proof that
`R` stays bounded away from 1 along the family — an inequality in three parameters, not a search.
The growth bound it would be composed with is already a theorem.

What stays bounded along that family is `R`: it tends to `3/2`, nowhere near the value a cap would
need. **Termination and short termination are
different properties, and they come apart at order five.** That is the demonstration, and it is why
a certificate is a pair and not a count.

### 8.3 Why analytic location fails at the extremal configuration

One further scope statement has a proof rather than a preference, and it is a structural fact about
the object.

> **Theorem 8.2.** At the arithmetic progression — readings `1, 2, …, n−1` — the instants at which
> the subject is lonely are exactly
>
> ```
>     { a/n  :  1 ≤ a,  gcd(a, n) = 1 },
> ```
>
> a set of isolated points, of Lebesgue measure zero, with `φ(n)` of them in each period. At `n = 8`
> the units are `1, 3, 5, 7`, so on `(0, 2]` the lonely instants are the eight points
> `1/8, 3/8, 5/8, 7/8, 9/8, 11/8, 13/8, 15/8`.

*Proof.* At `t = a/n` the reading of `i` is `ia/n`, whose distance to the integers is
`‖ia/n‖ = (ia mod n)/n` or its complement. If `gcd(a,n) = 1` then `i ↦ ia mod n` is injective on
`{1,…,n−1}` and never `0`, so every reading is at distance at least `1/n`. If `gcd(a,n) = g > 1`
then `i = n/g` is a reading with `ia ≡ 0`, and that runner sits on the subject. Off the grid `a/n`,
the reading `i = 1` already forces `‖t‖ ≥ 1/n` and the reading `i = n−1` forces
`‖(n−1)t‖ ≥ 1/n`; together these leave only the grid points. ∎

The consequence is about the object, not about the limits of any method in general. A measure or
density argument certifies existence by showing that a set of instants has positive measure, or that
a typical instant works. At the arithmetic progression the set of lonely instants has measure zero
and no instant is typical, so no argument of that shape can certify one there — and by Theorem 3.2
the arithmetic progression is the extremal configuration, which any general argument must cover.
This closes no case and supplies no bound. It states why the framework works in exact arithmetic and
lap geometry, and it is a fact about the configuration rather than a methodological preference.

The φ(n) in Theorem 8.2 is not incidental, and §10 shows it is the quantity that governs the rules.

---

## 9. The certificate rules

Each rule below is a decidable condition on the difference set together with a named instant, and a
proof that the instant is lonely whenever the condition holds. Each is elementary. Each is proved
at general `n` unless stated.

| rule | condition on the difference set | the instant it names |
|---|---|---|
| **R1** the ratio condition | `d_max ≤ (n−1)·d_min` | `1/(n·d_min)` |
| **R2** the band ladder | every disparity in `[(nM+1)e/(nk+1), (nM+n−1)e/(nk+1)]` for some `k, M` | the `j`-th opening of `e` |
| **R3** the non-resonant flank | `gcd(e, n) = 1` and no disparity divisible by `n` | `a = e·(e⁻¹ mod n)` |
| **R4** the divisible flank *(`n` prime)* | `n \| e`, no other disparity divisible by `n`, `e` largest | `a = c·e + 1`, `c` from a pigeonhole |
| **R5** the self-similar reduction | every non-flank disparity a multiple of `n` | inherited from the problem at modulus `e` |
| **R6** the divisibility rules | for some `q ≤ n`, no disparity divisible by `q` | `t = 1/q` |
| **R7** the free disparity | one disparity off the `P`-lattice of the rest; the rest at most three and sharing it | inherited from the reduced set |

Each row is a theorem; what the table compresses, the following unpacks.

**R1, the ratio condition.** If no disparity exceeds `n−1` times the least, every reading at the
earliest possible instant lies in `[1, n−1]`, hence at distance at least 1 from `n·ℤ`. This is
Theorem 4.2, and it is the widest single rule.

**R2, the band ladder.** Fix a flank `e` and an opening index `j`. The reading of `d` there is
`(d/e)(nj+1)`, so `d` is clear when that quantity lands between consecutive multiples of `n`, at
distance at least 1 from each. Writing `M` for which multiple — a lap counter — and requiring **one
shared `(j, M)` for every disparity at once**, the condition becomes
`(nM+1)e/(nj+1) ≤ d ≤ (nM+n−1)e/(nj+1)`: all disparities in a single band. Here `e` and `j` and `M`
are all existential, `M` does not vary with `d`, and `j` ranges over `0 ≤ j < e`. At `j = M = 0` the
band is `[e, (n−1)e]`, which with the flank at `d_min` is R1 exactly — so R1 is R2's zeroth rung,
and R2 is R1 restated at every opening index. Eliminating `M` gives a necessary condition with no
`M` in it: `(d_max − d_min)(nj+1) ≤ e(n−2)`.

**R3, the non-resonant flank.** Choose a disparity `e` coprime to `n`. If no disparity is divisible
by `n`, the inverse of `e` modulo `n` supplies an opening at which every disparity lies in the band:
take `a = e·s` with `e·s ≡ 1 (mod n)`, so the reading of `d` is `e·(d·s mod n)`, which is in band
exactly when `n ∤ d·s`, and since `s` is a unit that is exactly `n ∤ d`.

**R4, the divisible flank.** The complementary case, when the flank *is* divisible by `n`. A
pigeonhole over the units modulo `n` supplies a multiplier `c` making every other disparity's
reading land in band, provided no other disparity is divisible by `n` and the flank is the largest.
The pigeonhole needs more units than disparities, which is why this rule carries `n` prime; §10
shows the hypothesis is `φ(n) = n − 1` and not Euclid's lemma.

**R5, the self-similar reduction.** If every non-flank disparity is a multiple of `n`, say `n·m'`,
its reading is `n·((m'·a) mod e)` — the scale factors through the modulus — so the whole condition
is the same problem at modulus `e` rather than `n·e`, one scale down.

**R6, the divisibility rules.** For `q ≤ n`, the instant `1/q` is lonely exactly when no disparity is
divisible by `q`: the reading of `d` is `(d mod q)/q`, which is at distance at least `1/n` from the
integers precisely when it is nonzero, since `q ≤ n`. That is `n − 1` rules, one for each
`q = 2, …, n`, and each is an equivalence rather than an implication.

**R7, the free disparity.** Stated for arbitrary real difference sets. Suppose one disparity `x` has
irrational ratio to the others — more generally, sits off the lattice `{ y : P·(y/e) ∈ ℤ }` that the
others share for some integer `P` — and the others number at most three. Then the others are settled
at some flank by the small-cardinality result, and `x`, being off the lattice, cannot obstruct a
whole residue class of that flank's openings, so one of them is clear of `x` too.

**Any exhibited witness certifies its flank.** If `a ≡ 1 (mod n)` with `a < n·e` and every reading
`d·a mod n·e` lies in `[e, (n−1)e]`, the corresponding opening is lonely. This is not a rule with a
condition but the general form of one, and R1–R7 are instances of it.

R1 is Theorem 4.2. R2 subsumes it, as above.

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

**Why it does not reach the middle, concretely.** Take `ds = {1, 2, 3, 5}` at order five. Here
`M = 1` and `c = 4`, so this sits in the middle. The recursion asks for the set in the shape
`{ n·f } ∪ n·(others)` — every member a multiple of `n`. Scaling down by 5 sends `5 ↦ 1`, but
`1, 2, 3` are not multiples of 5 and have nowhere to go: the set does not scale. That is the whole
obstruction, and it is structural rather than a matter of effort. The recursion moves a set down
only when all of it moves together.

The set is nonetheless lonely, and the rules do reach it — the flank `e = 3` works at `j = 2`, and
so does `e = 5` at `j = 1`. What is missing is a *rule* that names which. The example of §6.1 is
also in the middle at order eight (`M = 1`, `c = 7`), and there R6 names one at `q = 6`. So the
middle is not uniformly hard; it is the region where no rule presently selects the flank.

**What the middle needs.** A condition under which `∃ (e, j)` is provable — by pigeonhole with the
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

Every numbered result above except Observation 8.1 — which is flagged at its statement as verified
and not derived — is formalised in Lean 4 with mathlib, with no `sorry`, no `native_decide`, no
`unsafe` and no `admit`, and every theorem depending on at most `propext`, `Classical.choice` and
`Quot.sound`. Three artefacts carry it, each built by an explicit gate; the largest holds 4,759
theorems, of which 283 are structural and the remainder are generated instances of a single
criterion applied to an enumerated family. The declarations below are the ones this paper's results
depend on.

The formalisation is a verification of the stated claims and their dependencies. It is not part of
the mathematical argument, and nothing below should be read as requiring it.

| result | declaration |
|---|---|
| Theorem 3.1 | `lonely_iff_flanks` |
| Theorem 3.2 | `gaps_all_eq` |
| Corollary 3.3 | `lonely_ne_pred` |
| Theorem 4.1 | `bound_le_of_lonely` |
| Theorem 4.2 | `ratio_condition` |
| Theorem 5.1 | `lonely_iff_exists_flank` |
| Theorem 5.2 | `clear_at_int_flank_iff_emod`, `flankWorks_iff`, `band_iff_beatty` |
| Theorem 7.1 | `lonely_of_fixed`, `first_isolation_of_fixed`, `first_isolation_as_zone_run`, `flank_at_first_isolation` |
| Theorem 7.2 | `bound_le_of_lonely`, `iterate_le_of_lonely`, `exists_fixed_of_lonely` |
| **Theorem A** | `doors_agree` (order 8), `LRC.SpecN.doors_agree` (general `n`) |
| R1 | `ratio_condition`, `clear_at_last_opening` |
| R2 | `lonely_flank_of_band`, `bandFits_forces_spread`, `spread_zero_iff_ratio` |
| R3 | `flankWorks_of_coprime`, `flankWorks_of_not_resonant` |
| R4 | `flankWorks_of_prime_dvd`, `exists_goodK` |
| R5 | `flankWorks_of_multiples`, `flankWorks_scale` |
| R6 | `ratWorks_le_order`, `ratWorks_one_iff`, `ratWorks_family_fails_iff` |
| R7 | `lonely_of_one_free`, `lonely_of_one_irrational` |
| the general witness form | `flankWorks_of_witness` |
| §10's `φ(n)` count | `card_nonresonant_eq_totient`, `shifted_budget_is_totient` |
| §11's trichotomy | `multiples_trichotomy`, `self_rule_applies_iff`, `coprime_rule_applies_iff` |
| Observation 8.1 | verified in exact rational arithmetic; **not formalised**, and flagged as an observation |
| Theorem 8.2 | proved in the text at §8.3 |

One body of material in the development record is deliberately absent here: an enumerated census of
difference-set families, which was evidence for the record rather than mathematics for the paper.
Theorem 5.2 together with the general witness form already gives a mechanical decision procedure for
integer difference sets, so nothing in the paper depends on it.

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
**certificate** — a flank and an opening index, `(e, j)`, together with a proof that the opening is
lonely.
**disparity** — one of the subject's speed differences `|vᵢ − v_k|`.
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

Rosenfeld, M. (2025). The lonely runner conjecture holds for eight runners. arXiv:2509.14111.
Preprint.

*Full references, the development record, the version history, the record of routes closed, and the
verification apparatus are in `MANUSCRIPT_v20.md`.*
