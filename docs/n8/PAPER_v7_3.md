# Deformations of Global Isolation in the Lonely Runner Conjecture

**T. Palelei.** v7.3.

*Changes in v7.3: retitled from "A Bounding Framework for Eight Lonely Runners". The old title was
wrong on both halves — the paper establishes no bound and says so twice (§13, §18), and all sixteen
numbered results are general-`n` statements, the only order-specific one being Observation 16 at
order five. The new title required the body to earn it: §3 was self-described as a **precursor**
whose material the §8 chain "does not pass through", which contradicted a title naming it as the
subject. §3 is now the setup rather than a precursor, and the abstract and introduction lead with
global isolation and its deformation. The φ(n) law remains Palelei (2026a) and is not claimed here;
making it load-bearing does not make it ours.*

*Changes in v7.2: corrections from the audits in `PAPER_v7_1_AUDIT_v1.md` and the Lean/manuscript
cross-check — a citation corrupted by v7.1's renumbering restored to Palelei (2026a, Theorem 3.1);
the artefact-and-gate sentence dropped from v6's §14 restored, with the one declaration lying
outside the gated tree named; the `n − 3` blocker bound given the first-band hypothesis that its own
Lean statement carries, in all three places it appears; Theorem 14 given the loneliness hypothesis
its minimum requires; the `R < 16` sufficient condition restated so it does not presuppose
existence; R4's prime hypothesis noted in §16. **Two audit findings remain open and need the
author**: six theorems are stated without argument (§17 meanwhile disclaims that the formalisation
is one), and §12's `{1,2,3,5}` example contradicts §11's own table, since R4 does name its flank.*

*Changes from v7 (carried in v7.1): the abstract and introduction written; the draft apparatus removed; internal
filenames replaced by citations to Palelei (2026a/2026b); numbered results renumbered consecutively
`Theorem 1`–`Observation 16`, because `Theorem 7.1` and `§7.1` denoted different things and
`Theorem 7.1` was stated in `§7.2`. **`PAPER_v7.md` on disk was edited in place through those
changes, so the body-only draft delivered as v7 is not recoverable** — the same versioning breach
recorded for v4. This file exists so that subsequent changes do not repeat it.*

---

## Abstract

Let `n` runners with distinct real speeds move on a circle of unit circumference, and call a runner
**lonely** at an instant when every other is at distance at least `1/n`. All `n` are lonely at once
exactly when they stand at the vertices of a regular `n`-gon; for speeds in arithmetic progression
that configuration recurs at exactly `φ(n)` instants per period, a law of Palelei (2026a). Deforming
the speeds destroys the simultaneity, and we give an exact criterion for when a global instant
survives. The Lonely Runner Conjecture asserts that a deformation removes only the simultaneity —
that the isolation disperses to the runners individually rather than vanishing — and we locate the
dispersed instants exactly. For any runner of any arrangement, with no hypothesis beyond
distinctness of the speeds, loneliness is equivalent to the existence of a lonely **opening**
`(j + 1/n)/e` of one of that runner's own speed differences `e`, and equivalently to the halting of
a deterministic construction started at the earliest possible instant and driven only by the runners
currently obstructing. For whole-number differences the opening condition is a finite conjunction of
modular memberships decided by the `e` indices `0 ≤ j < e`, so `(e, j)` is a certificate verified in
`n − 1` modular reductions. The conjecture thereby becomes the question whether a certificate exists
for every configuration; we give seven structural conditions that each produce one, closing both
ends of a trichotomy on the differences divisible by `n`. All results are formalised in Lean 4.

---

## 1. Introduction

Let `v₁, …, vₙ` be distinct real speeds, each runner moving on a circle of unit circumference at its
own speed, and let `‖x‖` denote the distance from `x` to the nearest integer. Runner `i` is **lonely**
at time `t` if `‖(vⱼ − vᵢ)t‖ ≥ 1/n` for every `j ≠ i`. The Lonely Runner Conjecture, due to Wills and
independently to Cusick, asserts that every runner is lonely at some instant. It is settled for
`n ≤ 7` by arguments particular to each order, the last two being Bohman, Holzman and Kleitman (2001)
at six runners and Barajas and Serra (2008) at seven.

The difficulty at a fixed order is that the conjecture asks for a single instant meeting `n − 1`
simultaneous conditions, with no evident reason why the times satisfying each should ever intersect.
This paper begins where the intersection is forced rather than accidental, and that is where all `n`
runners are lonely together.

**Global isolation, and its deformation.** Simultaneous isolation is rigid: the `n` runners are all
lonely at one instant precisely when they stand at the vertices of a regular `n`-gon, with no freedom
at all (Theorem 2). For speeds in arithmetic progression that configuration is reached, at instants
one can write down, and there are exactly `φ(n)` of them in each period — the law of Palelei (2026a),
restated here as Theorem 4. Every other arrangement is a deformation of a progression, and we give an
exact criterion for when a global instant survives one (Theorem 6). Generically none does: survival
requires commensurable speeds and an alignment condition, and an irrational deviation destroys it
outright.

What a deformation removes is the *simultaneity*, and Corollary 3 says it can remove nothing less —
the number of simultaneously lonely runners is never exactly `n − 1`, so isolation cannot be taken
from one runner while the others keep theirs together. Simultaneity therefore goes all at once. The
conjecture is the assertion that what remains is not nothing but a full set of individual instants:
the isolation disperses to the runners rather than vanishing. Locating the dispersed instants is the
business of this paper, and the count `φ(n)` of the undeformed configuration returns as the budget
available in the deformed one (§10.7).

**How they are located.** The loneliness condition is **closed** — a runner at distance exactly `1/n` leaves
the subject alone — and so the times at which a given runner obstructs form a union of *open*
intervals, one about each of its relative laps. The endpoints of those intervals therefore belong to
the complement: they are instants at which that runner is clear by exactly the threshold. The
framework is built on that boundary rather than on the time axis. It does not examine candidate times
and test them; it shows that the boundary structure forces every lonely state to admit a canonical
representation, and then reads that representation arithmetically.

The consequence is a chain of **equivalences**, not of sufficient conditions:

```
    loneliness   ⟺   lonely opening   ⟺   certificate   ⟺   cascade outcome
```

The substantive direction is the forward one. That a certificate implies loneliness is immediate once
the certificate is defined correctly; that loneliness *necessarily produces* a certificate is the
content of the paper. Every lonely instant is represented by a lonely opening — the openings are not
a family one may restrict attention to, they are the form loneliness takes.

Working on the boundary also fixes the method. At speeds in arithmetic progression the set of
instants at which all `n` runners are lonely together is finite in each period, hence of measure
zero; that configuration is extremal, so any general argument must cover it, and there are no
neighbourhoods there for an averaging or density argument to act on. The framework accordingly works
in exact arithmetic and lap geometry throughout.

**What is established.** For every arrangement and every runner, with no hypothesis beyond
injectivity of the speeds and uniformly in the order: loneliness is equivalent to the existence of a
lonely opening of one of the runner's own differences; for whole-number differences that condition is
an explicit finite conjunction of modular memberships; a deterministic construction — the **cascade**
— started at the earliest possible instant halts exactly when the runner is lonely, at the *first*
such instant, with a certificate readable off its halting state. Seven structural conditions on a
difference set each exhibit a certificate outright, and they close the two ends of an exact
trichotomy. The characterisation is formalised in Lean 4.

**What remains.** The conjecture is the universal quantifier over configurations: that a certificate
exists for every admissible difference set. This is not a gap in the characterisation, which is proved
in both directions and is complete. It is a separate and harder statement, and the later sections
constrain it — showing that it may be attacked entirely over `ℤ`, on an explicit candidate family,
against at most `n − 3` obstructing readings per candidate, with a witness known to sit at the edge of
a constraint if it exists at all. It is not proved here.

**Organisation.** The paper is in two layers. Layer 1, §§2–8, establishes the characterisation and is
self-contained; it ends with the chain stated in one place. Layer 2, §§9–15, is the analysis of the
universal question and revisits none of the equivalences. §16 separates what holds at general `n`
from what is specific to order eight, §17 records the formal verification, and §18 states what is
proved and what remains.

---

# LAYER 1 — THE FRAMEWORK

*§§2–8 characterise loneliness exactly, in the framework's own objects. Every arrow in the chain is
an equivalence, proved in both directions with no hypothesis beyond injectivity of the speeds.*

---

## 2. Loneliness is a closed condition, and its boundary

Let `v₁, …, vₙ` be distinct real speeds, each runner moving on a circle of unit circumference at its
own speed, and let `‖x‖` denote the distance from `x` to the nearest integer. Fix a **subject** `k`.
Runner `i` sits at circle distance `‖(vᵢ − v_k)t‖` from the subject at time `t`. Write the subject's
**disparities** for its `n − 1` positive speed differences `|vᵢ − v_k|`.

> **Definition.** The subject is **lonely at `t`** when `‖d·t‖ ≥ 1/n` for every disparity `d`.

The condition is **closed**: a runner at distance exactly `1/n` leaves the subject alone. This is not
a convention chosen for convenience. It is the mechanism, and everything below runs on it.

At any instant the `n` runners cut the circle into `n` cyclic gaps summing to 1.

> **Theorem 1.** Runner `i` is lonely if and only if both gaps flanking it are at least `1/n`.

The converse needs only the two flanking pairs, and not the attainment of any minimum. Two
consequences fix the shape of the problem.

> **Theorem 2.** All `n` runners are simultaneously lonely if and only if every gap is exactly
> `1/n` — the regular `n`-gon.

> **Corollary 3.** The number of simultaneously lonely runners lies in `{0, …, n−2} ∪ {n}`. It is
> never exactly `n − 1`.

Theorem 2 says simultaneous isolation is a rigid configuration, with no freedom at all.
Corollary 3 is a conservation statement: the gaps sum to 1, so isolation cannot be removed from
one runner while the others keep theirs simultaneously.

### 2.1 The boundary discipline

Because the condition is closed, the set of times at which a given runner obstructs is a union of
**open** intervals,

```
    ( (N − 1/n)/d , (N + 1/n)/d ),     N ∈ ℤ,
```

one about each of that runner's relative laps. We call these its **in-the-way zones**; the endpoints
belong to the complement. Two consequences carry through everything that follows.

**Endpoints are clear.** At `t = (N + 1/n)/d` the runner `d` stands at distance exactly `1/n`. Every
candidate instant this paper constructs is such an endpoint, for some runner and some lap — that is
what makes the certificate of §6 a pair of integers rather than a real number.

**A cell is decided by an interior point.** Partition the positive axis by all the zone endpoints of
all the disparities. Within one cell every runner's status is constant, so any interior point decides
it. The endpoints bounding a cell may both be clear while the cell's interior is not: the two
bounding zones can belong to different runners and overlap across the cell between them. Deciding a
cell therefore requires an interior point.

This is the **boundary set method** of Palelei (2026a, §2.2), whose Lemmas 2.1–2.2 establish that a
runner's status can change only at these endpoints, so that the cells are exactly the intervals on
which every status is constant: evaluate open cells and boundary points separately, never merge
touching zones, and decide a cell by an interior point. The worked example of §7.1 shows it
operating — two runners sit exactly on the boundary at the first step and are clear, and one of them
becomes the next obstruction.

---

## 3. Global isolation, and how it deforms

Theorem 2 says that simultaneous isolation is rigid: the `n` runners must stand at the vertices of a
regular `n`-gon, with no freedom at all. That rigidity is the starting point. There is one family of
arrangements at which the configuration is reached, its instants can be written down, and there are
exactly `φ(n)` of them in each period; every other arrangement is a deformation of it, and the
question this paper answers is what becomes of the isolation under deformation.

The `φ(n)` law itself is prior work and is not claimed here — it is Palelei (2026a), restated with
its proof so the paper is self-contained. What is developed below is the deformation: an exact
criterion for when a global instant survives (§3.1), and then, for the arrangements where none does,
the location of the isolation that remains (§§4–8).

For speeds in arithmetic progression the global instants can be written down exactly. This is the
`φ(n)` law of Palelei (2026a, Theorem 3.1); it is stated here, with its proof, so that the paper is
self-contained, and no part of it is claimed as new.

> **Theorem 4** (the `φ(n)` law; Palelei 2026a, Theorem 3.1)**.** Let the speeds be
> `v₀, v₀ + d, …, v₀ + (n−1)d`. All `n` runners are simultaneously lonely precisely at the instants
>
> ```
>     t = a/(n d),      a ≥ 1,      gcd(a, n) = 1,
> ```
>
> and at no others. There are `φ(n)` such instants in each period. At `n = 8` there are four, at
> `t d = 1/8, 3/8, 5/8, 7/8`.

*Proof* (Palelei 2026a; restated). Work relative to runner `0`. At time `t` runner `i` stands at
`(vᵢ − v₀)t = i d t` on the circle, so writing `u = d t` the `n` relative positions are
`{ i u mod 1 : 0 ≤ i < n }`. By Theorem 2 all `n` runners are lonely exactly when these are the `n`
vertices of a regular `n`-gon, that is when

```
    { i u mod 1 : 0 ≤ i < n }  =  { 0, 1/n, 2/n, …, (n−1)/n }.
```

Suppose they are. Runner `1` stands at `u`, which is then a vertex, so `u = a/n` for some integer
`a ≥ 1`. The positions are `{ i a/n mod 1 }`, and as `i` runs over `ℤ/n` the image of `i ↦ i a` is
the subgroup generated by `gcd(a, n)`, of size `n / gcd(a, n)`. That is all of `ℤ/n` exactly when
`gcd(a, n) = 1`. Conversely, if `gcd(a, n) = 1` then `i ↦ i a` is a bijection of `ℤ/n` and the
positions are precisely the `n` vertices. Hence the global instants are `u = a/n` with
`gcd(a, n) = 1`, that is `t = a/(n d)`, and there are `φ(n)` of them per period. ∎

The count recurs, and that recurrence is one thread of the paper: §10.7 shows that the same `φ(n)`
counts the disparities a certificate rule may use as a flank. The global instants are exactly the
units of `ℤ/n`, and so are the usable flanks — the invariant of the undeformed configuration
reappears as the budget available after deformation.

Two further consequences are worth recording. The lonely set here is finite in each period, hence of
measure zero, so at this configuration there is no positive-measure set of lonely instants for an
averaging argument to act on. And by Theorem 2 this is the extremal configuration, the one any
general argument must cover; the framework accordingly works in exact arithmetic and lap geometry
throughout.

### 3.1 Perturbation, and why the problem goes runner by runner

Palelei (2026a, Proposition 4.1) shows that the configuration of Theorem 4 has zero stability
radius: exact grid formation cuts out a measure-zero set, so arbitrarily small perturbations destroy
it. What follows sharpens that from a measure-theoretic statement to an exact criterion, naming which
perturbations survive and which do not.

Let the speeds be arbitrary. Write them against a progression, `v = A + e`, with `A_k = v₀ + k d` and
deviations `e_k`, normalising `e₀ = 0`.

> **Theorem 5.** At `t = a/(n d)` with `gcd(a, n) = 1`, the progression part places the `n` runners
> one to each `n`-th, simultaneously; the deviation displaces runner `k` from its vertex by exactly
> `e_k · a / d` of an `n`-th.

> **Theorem 6.** The global instant survives the deviation if and only if every displacement is a
> whole number of `n`-ths and `k ↦ k a + e_k a / d (mod n)` is a bijection of `ℤ/n`.

So simultaneity requires the displacements to be integral, which forces commensurable speeds, and
requires the resulting map of the vertices to remain a permutation. An irrational deviation destroys
it outright; a rational one destroys it as soon as two runners are sent to the same vertex.

**Where the isolation goes.** When the global instant fails, what has been lost is the
*simultaneity*, and only that: no single instant now serves every runner, and each must be given one
of its own. Corollary 3 is the fragment of this picture which is already a theorem — isolation
cannot be removed from one runner while the rest keep theirs together, so simultaneity goes all at
once, which is why Theorem 6 reads as an all-or-nothing condition. It goes all at once, and the
conjecture is the assertion that what it leaves behind is a full set of individual instants rather
than nothing.

**That assertion is what the rest of the paper is about.** Layer 1 locates the individual instants
exactly, in the deformed arrangement's own arithmetic; Layer 2 asks whether they are always there.

---

## 4. One runner, one scale

Here the paper stops being a general discussion of the conjecture and becomes the framework.

Normalise by the nearest runner. Writing `u = d_min · t`, each disparity `d` has a **ratio**
`s = d / d_min ≥ 1`, and the **reading** of `d` at time `t` is `s · u`.

> **Theorem 7 (the earliest possible lonely instant).** If the subject is lonely at `t > 0` then
> `t ≥ 1/(n·d_min)`; equivalently `u ≥ 1/n`.

We write `t₀ = 1/(n·d_min)` and call it **the bound**: below it the nearest runner has not yet left
the subject, so nothing earlier can be lonely. It is where the construction of §7 begins.

The whole problem is now visible in one line: **find `u ≥ 1/n` at which every reading lies in the
clear band**, that is at distance at least 1 from `n·ℤ` in the local coordinate.

One case falls out immediately.

> **Theorem 8 (the ratio condition).** If `d_max ≤ (n−1)·d_min` then the subject is lonely at
> `u = 1/n`, that is at `t = 1/(n·d_min)`.

At that instant every reading `s` lies in `[1, n−1]`, hence at distance at least 1 from `n·ℤ`. The
constant `n − 1` is one below the first multiple of `n`, and is not special to eight. Theorem 8
settles a subject outright whenever the spread of its disparities is within a factor of `n − 1`; it
returns in Layer 2 as rule R1.

---

## 5. Localisation: every lonely instant is represented by an opening

> **Definition.** For a disparity `e` and an integer `j ≥ 0`, the `j`-th **opening** of the flank
> `e` is the instant `(j + 1/n)/e`.

At such an instant the runner `e` sits at distance exactly `1/n` — on the boundary, hence clear — and
the content of the condition is carried by the other disparities.

> **Theorem 9 (Localisation).** The subject is lonely at some positive instant if and only if some
> flank has a lonely opening.

**The forward direction is the substantive one, and it is a structural statement, not a reduction in
search space.** From any lonely `t`, the opening `(⌊e·t⌋ + 1/n)/e` of a suitable disparity `e` is
itself lonely, and no later than `t`. So *every lonely instant is necessarily represented by a lonely
opening*: the openings are not a family one may restrict attention to, they are the form loneliness
takes. The converse — an opening that is lonely is a lonely instant — is immediate.

Theorem 9 is the paper's hinge. Everything after it works with the countable family of openings,
and loses nothing by doing so, because nothing was ever outside it.

---

## 6. The certificate: the exact arithmetic form

For whole-number disparities the family of openings is finite and the condition on it is arithmetic.

> **Theorem 10.** Let the disparities be positive integers and `e` one of them. The opening `j` of
> the flank `e` is lonely if and only if
>
> ```
>     d · (n j + 1)  mod  n e   ∈   [ e , (n−1) e ]        for every disparity d.
> ```
>
> The condition is periodic in `j` with period `e` — replacing `j` by `j + e` adds `n e` to the
> numerator — so the `e` indices `0 ≤ j < e` decide the question outright. No real number survives in
> the criterion.

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
of the band and is not optional: dropping it makes disparity sets appear to have no working opening
when in fact they do.

> **Definition.** A **certificate** for a subject is a pair `(e, j)` — a flank and an opening index —
> satisfying the condition of Theorem 10.

A certificate is checked in `n − 1` modular reductions. It carries no trace of how it was found.

---

## 7. The cascade: constructing the certificate

Theorems 9 and 10 say what loneliness *is*. They do not, by themselves, produce a certificate. The
cascade does, deterministically, from the bound.

> **Definition.** A runner at disparity `d` is **in the way** at `t` when `‖d·t‖ < 1/n`. Its **next
> opening** after `t` is the least `(N + 1/n)/d` at or after `t`. The **move** sends `t` to the
> largest next opening among the runners in the way at `t`, and fixes `t` if none is. The
> **cascade** is the sequence of moves from the bound `1/(n·d_min)`.

Three facts make this well defined and free of search. A runner in the way at `t` stays in the way
until its own next opening; the next opening is strictly later than `t`; and each move lands on the
opening of one runner in the way. There is no candidate list: the runners in the way at `t` fix the
move.

It is a recursion on the scale. At `1/(nD)` a runner of reading `s = d/D` is in the way exactly when
`|s − nN| < 1` for some `N`, and its next opening is the first point of the progression of gap
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
is a convenience and never a hypothesis; the construction is carried out separately for each subject,
in that subject's own differences.

**Step 0, `t = 1/8`.** The readings `d·t` are

| `d` | 1 | 2 | 3 | 4 | 5 | 7 | 8 |
|---|---|---|---|---|---|---|---|
| `d·t` | 1/8 | 1/4 | 3/8 | 1/2 | 5/8 | 7/8 | 1 |
| `‖d·t‖` | 1/8 | 1/4 | 3/8 | 1/2 | 3/8 | 1/8 | **0** |

Runner 8 is at distance 0 — it has completed exactly one relative lap and sits on the subject. It is
the only runner in the way. Its next opening is `(1 + 1/8)/8 = 9/64`, and the move goes there.

Note what runners 1 and 7 are doing: both sit at distance exactly `1/8`, on the boundary. They are
clear. This is the closed condition of §2 doing visible work — had the inequality been strict, this
instant would have three obstructions rather than one.

**Step 1, `t = 9/64`.** The readings are now

| `d` | 1 | 2 | 3 | 4 | 5 | 7 | 8 |
|---|---|---|---|---|---|---|---|
| `‖d·t‖` | 9/64 | 9/32 | 27/64 | 7/16 | 19/64 | **1/64** | 1/8 |

Runner 8 has been cleared — it now reads `9/8`, distance `1/8`, on the boundary. But runner 7, which
sat exactly on the boundary at step 0, now reads `63/64`: it has been carried to within `1/64` of
completing its lap, and is in the way. Its next opening is `(1 + 1/8)/7 = 9/56`, and the move goes
there.

**Step 2, `t = 9/56`.** The readings are

| `d` | 1 | 2 | 3 | 4 | 5 | 7 | 8 |
|---|---|---|---|---|---|---|---|
| `‖d·t‖` | 9/56 | 9/28 | 27/56 | 5/14 | 11/56 | **1/8** | 2/7 |

Every distance is at least `1/8`. No runner is in the way, the move fixes `t`, and the subject is
lonely at `t = 9/56`.

**Reading off the certificate.** The halting instant is `9/56 = (1 + 1/8)/7`, which is the opening
`j = 1` of the flank `e = 7`. So the certificate is `(e, j) = (7, 1)`, and runner 7 sits at exactly
one eighth — as Theorem 11(d) says it must.

The cascade took two moves. Nothing in the certificate records that; the pair `(7, 1)` is what is
exhibited, and it can be checked in seven modular reductions without reference to the procedure that
found it.

**And the rules of §10 reach this set by another route entirely.** Its largest disparity exceeds
seven times its least, so R1 does not apply; one disparity is divisible by 8, so R3 does not. But no
disparity is divisible by 6, so R6 applies at `q = 6` and names the instant `t = 1/6`, at which the
readings are `1/6, 1/3, 1/2, 1/3, 1/6, 1/6, 1/3` — all at least `1/8`.

So the cascade and the rules are two ways to a certificate, and they generally produce **different**
ones: `9/56` here against `1/6`. The cascade is a construction that always terminates when the
subject is lonely and needs no condition; a rule is a shortcut that bypasses the construction
entirely but applies only where its condition holds. Neither is the other's approximation.

### 7.2 Construction and Localisation

> **Theorem 11 (Construction).** If some step of the cascade is fixed, at `T`, then: (a) the subject
> is lonely at `T`; (b) no positive instant before `T` is lonely; (c) `T` is the end of a run of
> lap-completion zones from the bound, each containing the end of the one before; and (d) some runner
> sits at exactly `1/n`, as the nearest ahead or the nearest behind.

So a fixed point is not merely *a* lonely instant. It is the **first** one, it terminates a
boundary-set run, and it carries a runner at the threshold — which is why the halting instant is
always an opening, and why the certificate has the form `(e, j)`.

> **Theorem 12 (Cascade localisation).** For every positive instant `s` at which the subject is
> lonely: `s ≥ 1/(n·d_min)`; every step of the cascade is at most `s`; `s` is matched by a lonely
> opening no later than it; and **the cascade reaches a fixed point**.

The last clause carries the equivalence, and its proof is a finiteness argument and nothing else:
below `s` the cascade's steps lie in the finite set of openings `(k + 1/n)/d` with `0 ≤ k ≤ ⌈d·s⌉`,
and a strictly increasing sequence cannot remain in a finite set.

> **Theorem 13.** For every injective arrangement `v` and every subject `k`, with no hypothesis
> beyond injectivity, the following five statements are equivalent:
>
> 1. the subject is lonely at some positive instant;
> 2. the cascade reaches a fixed point;
> 3. the cascade's instants are bounded above;
> 4. some flank has a lonely opening;
> 5. each runner is in the way at only finitely many steps.
>
> The proof is uniform in the order; the same argument gives the statement at every `n ≥ 2`.

---

## 8. The framework stated

Layer 1 is complete. Collecting Theorems 9, 10, 11, 12 and 13:

```
    loneliness   ⟺   lonely opening   ⟺   certificate   ⟺   cascade outcome
```

Each arrow is an **equivalence**, proved in both directions, with no hypothesis beyond injectivity of
the speeds, and uniformly in the order.

Read carefully, this is not a method that might find loneliness. It is a description of what
loneliness *is*. For a fixed subject of a fixed arrangement:

* the subject is lonely at some instant **exactly when** one of its own disparities has an opening at
  which every other disparity reads inside the band (Theorem 9);
* for whole-number disparities that condition is **exactly** a finite conjunction of modular
  membership statements, decided by the `e` indices `0 ≤ j < e` (Theorem 10);
* and the cascade, started at the bound and driven only by the runners currently in the way, halts
  **exactly when** the subject is lonely, at the first such instant, with a certificate readable off
  the halting state (Theorems 11–13).

The substantive direction throughout is the forward one. That a certificate implies loneliness is
immediate once the certificate is defined correctly; that loneliness *necessarily produces* a
certificate is the content.

**Nothing in Layer 1 is conditional, and nothing in it is outstanding.**

---

# LAYER 2 — THE EXISTENCE ANALYSIS

---

## 9. The existence question

Layer 1 settles, for a fixed disparity configuration, what loneliness is:

```
    ∃ t > 0 lonely      ⟺      ∃ (e, j) satisfying the condition of Theorem 10.
```

The Lonely Runner Conjecture is the statement obtained by quantifying over configurations:

```
    for every admissible disparity configuration, such an (e, j) exists.
```

**This is not a missing direction in the equivalence.** Layer 1 has no gap; both directions are
proved. What remains is a universal quantifier, and that is a different kind of statement: it asks
whether the equivalent condition — now an explicit finite arithmetic condition — is *universally
satisfiable*.

Everything in Layer 2 works **inside** the equivalent condition. §10 gives structural hypotheses
under which a certificate can be exhibited outright. §§11–12 classify what those hypotheses reach and
what they leave. §13 reparameterises the condition; §14 describes the structure of its satisfying
set; §15 states what the universal question has been reduced to and constrained by.

None of it revisits the equivalence, and none of it is needed for the equivalence to hold.

---

## 10. Structural certificate rules

A rule is a condition on a disparity set together with a proof that a named instant is lonely
whenever the condition holds. Each is elementary. Each is proved at general `n` unless stated. Where
a rule's condition holds, the conjecture is established for that configuration.

There are seven, and they are grouped here by mechanism rather than by order of discovery.

| rule | condition on the disparity set | the instant it names |
|---|---|---|
| **R1** the ratio condition | `d_max ≤ (n−1)·d_min` | `1/(n·d_min)` |
| **R2** the band ladder | every disparity in `[(nL+1)e/(nj+1), (nL+n−1)e/(nj+1)]` for some `j, L` | the `j`-th opening of `e` |
| **R3** the non-resonant flank | `gcd(e, n) = 1` and no disparity divisible by `n` | `a = e·(e⁻¹ mod n)` |
| **R4** the divisible flank *(`n` prime)* | `n \| e`, no other disparity divisible by `n`, `e` largest | `a = r·e + 1`, `r` from a pigeonhole |
| **R5** the self-similar reduction | every non-flank disparity a multiple of `n` | inherited from the problem at modulus `e` |
| **R6** the divisibility rules | for some `q ≤ n`, no disparity divisible by `q` | `t = 1/q` |
| **R7** the free disparity | one disparity off the `P`-lattice of the rest; the rest at most three and sharing it | inherited from the reduced set |

### 10.1 Scale control — R1

If no disparity exceeds `n−1` times the least, every reading at the bound lies in `[1, n−1]`, hence
at distance at least 1 from `n·ℤ`. This is Theorem 8, and it is the widest single rule.

### 10.2 Band control — R2

Fix a flank `e` and an opening index `j`. The reading of `d` there is `(d/e)(nj+1)`, so `d` is clear
when that quantity lands between consecutive multiples of `n`, at distance at least 1 from each.
Writing `L` for which multiple — a lap counter — and requiring **one shared `(j, L)` for every
disparity at once**, the condition becomes `(nL+1)e/(nj+1) ≤ d ≤ (nL+n−1)e/(nj+1)`: all disparities
in a single band. Here `e`, `j` and `L` are all existential, `L` does not vary with `d`, and `j`
ranges over `0 ≤ j < e`. At `j = L = 0` the band is `[e, (n−1)e]`, which with the flank at `d_min` is
R1 exactly — so R1 is R2's zeroth rung, and R2 is R1 restated at every opening index. Eliminating `L`
gives a necessary condition with no `L` in it: `(d_max − d_min)(nj+1) ≤ e(n−2)`.

### 10.3 Non-resonant structure — R3

Choose a disparity `e` coprime to `n`. If no disparity is divisible by `n`, the inverse of `e` modulo
`n` supplies an opening at which every disparity lies in the band: take `a = e·s` with
`e·s ≡ 1 (mod n)`, so the reading of `d` is `e·(d·s mod n)`, which is in band exactly when `n ∤ d·s`,
and since `s` is a unit that is exactly `n ∤ d`.

### 10.4 Resonant structure — R4 and R5

**R4, the divisible flank.** The complementary case, when the flank *is* divisible by `n`. A
pigeonhole over the units modulo `n` supplies a multiplier `r` making every other disparity's reading
land in band, provided no other disparity is divisible by `n` and the flank is the largest. The
pigeonhole needs more units than disparities, which is why this rule carries `n` prime; §10.7 shows
the hypothesis is `φ(n) = n − 1` and not Euclid's lemma.

**R5, the self-similar reduction.** If every non-flank disparity is a multiple of `n`, say `n·m'`,
its reading is `n·((m'·a) mod e)` — the scale factors through the modulus — so the whole condition is
the same problem at modulus `e` rather than `n·e`, one scale down.

### 10.5 Divisibility — R6

For `q ≤ n`, the instant `1/q` is lonely exactly when no disparity is divisible by `q`: the reading
of `d` is `(d mod q)/q`, which is at distance at least `1/n` from the integers precisely when it is
nonzero, since `q ≤ n`. That is `n − 1` rules, one for each `q = 2, …, n`, and each is an equivalence
rather than an implication.

R6 stands apart in one respect: its instants depend on the disparity set only through divisibility,
and are indexed by `q` rather than by any member of the set. `t = 1/2` asks that every disparity be
odd; `t = 1/3` that none be divisible by three; `t = 1/q` for `q ≤ n` that none be divisible by `q`.
The rule strengthens with the order, because the band `[1/n, 1 − 1/n]` widens while each disparity
excludes only `2/n` of the residues.

### 10.6 The free disparity, and the real case — R7

Stated for arbitrary real disparity sets. Suppose one disparity `x` has irrational ratio to the
others — more generally, sits off the lattice `{ y : P·(y/e) ∈ ℤ }` that the others share for some
integer `P` — and the others number at most three. Then the others are settled at some flank by the
small-cardinality result, and `x`, being off the lattice, cannot obstruct a whole residue class of
that flank's openings, so one of them is clear of `x` too.

A disparity incommensurable with the others therefore *helps*: its readings meet every residue class
of a flank's openings, so some opening in any class it is offered is clear of it. **The disparity
sets that resist the rules are the commensurable ones.**

### 10.7 The general witness form, and the `φ(n)` behind the rules

**Any exhibited witness certifies its flank.** If `a ≡ 1 (mod n)` with `a < n·e` and every reading
`d·a mod n·e` lies in `[e, (n−1)e]`, the corresponding opening is lonely. This is not a rule with a
condition but the general form of one, and R1–R7 are instances of it.

R3 was first proved with `n` prime. The hypothesis was used in exactly two places: to obtain
`gcd(e, n) = 1` from `n ∤ e`, and to split `n | d·s` by Euclid's lemma. Neither needs a prime. Take
coprimality as the hypothesis, and the second follows because `s` is a unit. The witness is
`a = e·s` where `e·s ≡ 1 (mod n)`, and the readings are `e·(d·s mod n)`; the band holds exactly when
`n ∤ d·s`, which since `gcd(s,n) = 1` is exactly `n ∤ d`. Nothing in that is prime.

So the condition is that the flank be **non-resonant**, `gcd(e, n) = 1`. At prime `n` that coincides
with `n ∤ e`, which is why primality appeared load-bearing. The usable flanks are the residues
coprime to `n`, and there are `φ(n)` of them.

The same quantity governs R4. Its pigeonhole ranges over the units, `φ(n)` of them, so its budget is
`|L| < φ(n)`. A subject has `n − 2` non-flank disparities, so R4 needs `n − 2 < φ(n)` — and since
`φ(n) ≤ n − 1` with equality only at primes, that holds **exactly at prime `n`**. The primality in R4
is `φ(n) = n − 1`, not Euclid's lemma.

Primality is the top of a scale, not a switch: `φ(p)/p = 1 − 1/p`, and `φ(n)/n = ∏(1 − 1/p)` over the
primes dividing `n`. Parity is a consequence and not a cause: `2 | n` forces `φ(n)/n ≤ 1/2`, which is
why even orders are harder. Order eight is `2³`, and that — not its size — is the difficulty.

This is the same `φ(n)` that counts the global instants in Theorem 4: the units of `ℤ/n` count both
the instants at which the regular progression isolates every runner at once, and the disparities a
rule may use as a flank.

### 10.8 What the rules' failure conditions are

A rule that only fires is a measurement. A rule whose failure is characterised is a case in a case
analysis, and cases compose.

> **R6 fails** exactly when the disparity set covers every modulus in `[2, n]` by divisibility — in
> particular when every prime `p ≤ n` divides some disparity.
>
> **R3 applies** exactly when no disparity is divisible by `n` and some disparity is coprime to it.
>
> **R5 applies** exactly when at most one disparity avoids `n`.

Two consequences. R3 is subsumed: its condition is the `q = n` instance of R6, and R6 does not even
require a coprime flank to exist. And R3 and R5 are the two ends of a single count, which §11 makes
exact.

---

## 11. What the rules cover: the trichotomy

Write `M` for the number of disparities divisible by `n`, and `c` for the number of disparities.

| region | standing |
|---|---|
| `M = 0` | **closed** — R6 at `q = n`, equivalently R3 |
| `M ≥ c − 1` | **closed** — R5, with the lone non-multiple as the flank |
| `1 ≤ M ≤ c − 2` | **open**. R4 reaches `M = 1` when the multiple is the largest disparity |

The split is exhaustive. **The rules close the two ends of the resonance count and leave a
structurally defined middle.** That is the content of this section, and it is a statement about the
count, not about how often the rules happen to fire.

**A remark on reach figures.** On any finite enumeration of whole-number disparity sets the rules
leave a residue, and it can be reported as a count. Such a count measures that enumeration: the
conjecture's domain carries no canonical measure, and the same rule scores differently under
different sampling schemes. Figures of that kind indicate which rule does which work, and nothing
more. They are not progress, and none is quoted as such in this paper.

---

## 12. The middle is self-similar, but mixed

A disparity divisible by `n`, say `n·m'`, has reading

```
    (n·m'·a)  mod  n e   =   n · ( (m'·a)  mod  e ),
```

so its band condition is a band condition at modulus `e`, and it depends on `a` only through
`ρ = a mod e`. A disparity *not* divisible by `n` needs all of `a`. So the middle region is a
**self-similar copy of the same problem one scale down, constrained additionally by the
non-multiples**:

```
    middle   =   self-similar resonant component   +   non-resonant constraints.
```

R3 is the case where the first part is empty; R5 is the case where the second is. The middle is
where both are present, and the recursion does not close on its own because the two components do not
descend together.

**Why it does not close — the example.** Take the disparity set `{1, 2, 3, 5}` at order five. The
resonant part is `{5}`, which descends. But `1, 2, 3` are not multiples of 5 and have nowhere to go:
the set does not scale. That is the whole obstruction, and it is structural rather than a matter of
effort. **The recursion moves a set down only when all of it moves together.**

The set is nonetheless lonely, and the rules do reach it — the flank `e = 3` works at `j = 2`, and so
does `e = 5` at `j = 1`. What is missing is a *rule* that names which. The example of §7.1 is also in
the middle at order eight (`M = 1`, `c = 7`), and there R6 names one at `q = 6`. So the middle is not
uniformly hard; it is the region where no rule presently selects the flank.

**What the middle needs.** A condition on the disparity set under which some flank and some index can
be shown to exist — by pigeonhole, induction, contradiction or construction.

---

## 13. The certificate condition reparameterised: `R` and the clear set

The rest of Layer 2 works with the certificate condition in a second coordinate. The change is an
exact reparameterisation; it neither strengthens nor weakens anything in Layer 1.

Let `R = d_min/D_final` be the contraction the cascade performs, equivalently `R = t/t₀` — the
halting instant measured in units of the bound.

> **Theorem 14 (`R` in closed form).** At the final scale every reading is `s_i·R` with
> `s_i = d_i/d_min`, so clearance is `s_i·R mod n ∈ [1, n−1]` for all `i`. **If the subject is lonely**
> — equivalently, by Theorem 9, if that clear set is non-empty — then, since the cascade walks forward
> from `R = 1`,
>
> ```
>     R  =  min { R ≥ 1  :  ∀ i,  s_i·R  mod n  ∈  [1, n−1] }.
> ```

That the clear set *is* `{R : ∀i, s_i·R mod n ∈ [1, n−1]}` is immediate: the reading of `d_i` at a
scale `D` is `d_i/D = (d_i/d_min)(d_min/D) = s_i·R`, and clearance is that every reading is at least
1 from a multiple of `n`. That the cascade's value is the **minimum** such `R ≥ 1` follows from
Theorem 12: every lonely instant is at or after every step of the cascade. So `R` is computable from
the reading profile alone, with no iteration.

> **Theorem 15 (the bands).** `R/n = d_min·t*` is `d_min`'s own lap coordinate at the isolation
> instant, and `d_min` is a disparity, so `R mod n ∈ [1, n−1]`. At order eight, `R` can never lie in
> `(7,9)`, `(15,17)`, … Stated and proved for arbitrary `n`.

So `⌊R/n⌋` counts the complete laps `d_min` makes before isolation. A **deep** cascade is one that
pushes `d_min` past its first lap; depth and band are the same phenomenon seen twice.

Combining Theorem 14 with Layer 1, existence at order eight is equivalent to

> for every profile `1 = s₁ < s₂ < … < s₇`, some `R ≥ 1` has all `s_i·R mod 8 ∈ [1,7]`.

***This is a reformulation, not progress toward a proof.*** No bound is established. A sufficient
condition over a bounded region follows from Theorem 15, stated so that it does not presuppose what
it is meant to give: if for every profile the clear set meets `[1, 16)`, existence at order eight
follows, since by Theorem 15 that interval contributes only `[1,7] ∪ [9,15]`. The evidence for it is
measurement — a clear point below 12 in 12.2 million profile evaluations, extended to 16 by
Theorem 15 — and the counting is no help: six combs at density `1/4` over 12 units give 18 units of bad measure, a
factor of 1.5 against.

**A method note, stated plainly.** The paragraph above argues by covering: it forms complements and
asks whether a set is empty. The framework's own discipline (Palelei 2026b, §6A) bans exactly that,
and the ban's wording is formal rather than a test of provenance. This section is therefore *not*
admitted by reading that row; it is admitted by the author's ruling of 2026-09-18 that the ban exists
to prevent a covering argument being *imported* from outside the framework, and that an argument
built from the framework's own objects — the readings, the bad bands, `R` — is not that. Readers who
reject the ruling should read this paragraph as conditional on it. **Theorems 14 and 15 do not
depend on it.**

### 13.1 Why `R`, and not cascade length

At orders three and four, and at order `n ≥ 6` with four disparities, the cascade halts within a
number of steps fixed in advance. At order five with four disparities the length grows with the
arrangement.

> **Observation 16** `[VERIFIED — exact rational arithmetic, 3 ≤ κ ≤ 100; not formalised]`. At
> order five the disparity sets `(1, 5κ − 2, 5κ, 10κ − 2)` have cascade length `2κ + 1` for even `κ`
> and `2κ + 2` for odd `κ`. The setter word is regular: writing `A = 5κ−2`, `B = 5κ`, `C = 10κ−2`, it
> is the repeated four-cycle
>
> ```
>     B@ι ,  C@2ι ,  A@ι ,  C@(2ι+1)          for ι = κ, κ+1, κ+2, …
> ```
>
> terminating in a final `B`, the last cycle truncated when `κ` is odd. Here `X@ι` means the move is
> set by disparity `X` at its lap `ι`.

Along the same family `R` tends to `3/2`. **The two quantities move independently**: the number of
steps grows without bound while the halting instant stays within a fixed factor of the earliest
possible one. A long cascade and a late instant are different things.

This is why Layer 2 works with `R` and not with cascade length, and it also bears on the form of the
certificate: a pair `(e, j)` is checked in `n − 1` modular reductions whatever the length of the
cascade that found it. In §7.1, two steps produced `(7, 1)`, and the check would read the same had it
taken two hundred.

---

## 14. Candidate geometry

*This section describes the structure of the satisfying set of the condition in §13. Every result
cited here is machine-checked and axiom-clean; statements are given in groups, with the individual
theorems and their declarations in Palelei (2026b), §§13–15. **No result in this section bears on
existence** — each constrains the question rather than answering any part of it, and the manuscript
records that explicitly at §13F and §14I.*

### 14.1 The covering question, made exact over `ℤ`

For a reading `s` at level `m` the bad interval ends at `(nm+1)/s`; the next, of reading `s'` at
level `m'`, begins at `(nm'−1)/s'`. The width between them is `N/(s·s')` with
`N = s(nm'−1) − s'(nm+1)`, and for integer readings `N` is an integer, so a gap has width at least
`1/(s·s')`. Two consecutive intervals meet or overlap exactly when `s(nm'−1) ≤ s'(nm+1)` — a linear
inequality over `ℤ`, not over `ℝ`. Being within 1 of a multiple of `n` at a point `A/s` is the
integer inequality `|A − nks| < s`.

So **for integer readings, at any order, deciding whether `[1, n−1]` is covered is a finite
conjunction of integer inequalities over an explicitly enumerable candidate set** — proved equivalent
to the real statement, not approximating it. `[Palelei 2026b, §§13A–13D, Theorems 13.1–13.10; general `n`.]`

**A retraction follows immediately, and it is against this work.** The smallest possible gap for
readings bounded by `H` is `1/H²`, so the minimum uncovered length *decays*. A figure of `53/462`
recorded for the integer-reading branch is exact and exhaustive for readings `≤ 40` and **is not a
floor beyond that range.** It was never a bound, and is not one now.

### 14.2 The candidate family, and rescaling

The satisfying points of interest carry numerators `n m + 1`; at order eight the candidates
`(8m+1)/s_k` are the spine of the problem **rescaled by `s_k`**, the modulus moving accordingly. A
reading `s_j = c·s_k` blocks the `s_k`-candidates exactly when `8 | c` — the divisibility test applied
to the rescaled reading. `[Palelei 2026b, §14A, Theorems 14.1–14.4.]`

At small moduli the picture collapses to bare non-divisibility: for `2 ≤ b ≤ n − 1` a unit constraint
is exactly non-divisibility, and the pattern **breaks at `b = 8`**, one past `n − 1`. `[Palelei 2026b, §14B,
Theorem 14.5; M §15A, Theorems 15.1–15.3, at every order.]`

### 14.3 Who can block

A reading never blocks its own candidates — `(s_k·A) mod 8s_k = s_k` exactly, with no further
hypothesis — and the unit reading never blocks a candidate **whose ratio lies in the first band**,
`s_k ≤ A ≤ 7 s_k`, equivalently `1 ≤ R ≤ 7`. Hence **at such a candidate the blocker count is at most
`n − 3`.** The band hypothesis is not decorative: without it the unit can block and the bound is
`n − 2`.
`[Palelei 2026b, §14C, Theorems 14.6–14.8.]`

This constrains without closing. Removing the two non-blockers takes the mean blockers per candidate
from `1.75` to `1.1867` over 2,773,580 pairs `[EMPIRICAL]`; a counting argument would need it below
1, so counting still does not close the question.

### 14.4 Reflection, and the two patterns

For an integer reading the bad condition is invariant under `x ↦ 8 − x`, since
`s(8−x) − 8k = −(sx − 8(s−k))`, so the clear set is symmetric about `x = 4`. This is time reversal,
and no novelty is claimed for it. On residues the same symmetry reads `r ↦ b − r`, and the two are
not two results. `[Palelei 2026b, §14D, Theorems 14.9–14.11.]`

The reflection is obstructed at exactly two residues: `b ≡ 0 (mod 8)`, the collision residue, and
`b ≡ 1 (mod 8)`, the guard residue. **Why**, and not merely where: candidates carry numerators
`8q+1`, and under `q ↦ m−q` the numerator becomes `8m − (8q+1) + 2`, of residue `−1`. The continuum
has the symmetry; the `+1` lattice does not — it maps to the `−1` lattice. `[Palelei 2026b, §14D, Theorems
14.12–14.13.]`

The endpoints accordingly form two inverted patterns, `s·x ≡ 1` and `s·x ≡ −1 (mod 8)`. The
arithmetic progression's four isolation events are where the two patterns **coincide**, forced by the
Klein identity: `u·u ≡ 1` puts `x = u` on the `+1` pattern via reading `u`, and `u·(8−u) ≡ −1` puts
the same point on the `−1` pattern via reading `8−u`. **Four events because there are four units
modulo 8** — Theorem 4's count, arrived at from the other side. `[Palelei 2026b, §14E, Theorems 14.14–14.16.]`

That coincidence does **not** transfer off the progression. What transfers is that each pattern
supplies a witness, generally at two different points.

### 14.5 The edge witness

Let `Sat q` say that `q` satisfies every constraint `L ≤ q mod b ≤ U`. If `Sat` holds somewhere and
fails below, then a satisfying point exists with **one constraint exactly at its lower edge**;
stepping up gives the upper edge; hence both.

The argument is a unit step: a constraint can only separate `q` from `q−1` by being exactly at its
lower edge at `q`, because if `q mod b > L` then `(q−1) mod b = q mod b − 1` is still in `[L,U]`, and
the walk must stop because `Sat` fails below. **It does not iterate** — inside a residue class mod `b`
the step is `b`, and a constraint can be leapt rather than landed on. `[Palelei 2026b, §14G, Theorems 14.20–14.23.]`

A solution off the reflection centre brings its mirror with it, so the solution set is never a
singleton unless everything in it is the centre; and `q = 0` is never a solution, since the lower edge
is positive. `[Palelei 2026b, §14G, Theorems 14.24–14.26.]`

**These seven are order-agnostic.** `Sat` is an arbitrary list of `(modulus, lower, upper)` triples;
no order appears in its definition or in any of the seven statements. They apply to any finite system
of congruence-interval constraints, at any order, and outside this setting entirely. `[Palelei 2026b, §14H.]`

### 14.6 The window, and the clear set as a ball

Clearing is exactly membership of a window: `b ≤ 8r+1 ≤ 7b`. So the blocked set is the cyclic ball
around `0` — a residue is blocked exactly when it lies within about `b/8` of `0` cyclically. The
window is at least half the modulus, and a proper divisor is at most half, so **a window covers a full
period of any proper divisor**: the clear interval of `b` is wide enough to contain a complete residue
cycle of `b'`. `[Palelei 2026b, §15N, Theorems 15.63–15.67.]`

At the small end, a single candidate has a ratio-7 reach: for `0 < q < b` the residue is `q` itself,
so clearing is the two-sided bound `(8q+1)/7 ≤ b ≤ 8q+1`, and one candidate covers every modulus in
that window. The candidate `q = 1` clears every modulus up to 9 and fails from 10 on, so 9 is its
exact reach. `[Palelei 2026b, §15L, Theorems 15.51–15.56.]`

For `2 ≤ b ≤ 9` the window is `[1, U(b)]`, so clearing forbids only the residue `0`, and additionally
`b−1` when `b` is 8 or 9: **small moduli forbid at most two residues each.** `[Palelei 2026b, §15P, Theorems
15.71–15.73.]`

### 14.7 Flanks and candidates are one language

Being in the way is invariant under shifting the disparity by a multiple of `n·e` — the residue is
all that enters — which is why the flank description of §6 and the candidate description of §13 are
the same description. `[Palelei 2026b, §15D, Theorem 15.15.]`

Two cautions travel with this group, and both are the manuscript's own.

**Theorem 15.20 is vacuous and must not be cited as a route.** `FlankBridge.existence_of_largest_-
flank_clear` remains a true implication, but its hypothesis is refuted by the arrangement
`[-4, 0, 1, 3, 4, 5, 7, 8]` at subject `0` and flank `e = 8`. `[Palelei 2026b, §15S.]`

**The largest flank is a strengthening the framework does not require.** Theorem 9 permits *any*
flank, and results stated for the largest one are correspondingly narrower.

---

## 15. What the universal question has been reduced to

Collecting Layer 2. For a subject with integer disparities, existence at that subject is the
statement that some flank is clear at some opening — equivalently, that the clear set of §13 is
non-empty. The following are established about that set, without settling whether it is always
non-empty.

**It is decided by finitely many integer inequalities.** Not approximated by them: proved equivalent
(§14.1). Whatever the eventual argument, it may be conducted entirely over `ℤ`.

**Its candidates are an explicit arithmetic family.** The numerators are `n m + 1`, the flank supplies
the denominator, and rescaling by a reading moves the whole picture to a known modulus (§14.2).

**At most `n − 3` readings can block a candidate in the first band** — a reading never blocks its own
candidates unconditionally, and the unit never blocks one with `s_k ≤ A ≤ 7 s_k` (§14.3).

**If the set is non-empty at all, it has a witness with a constraint exactly at an edge**, and it is
never a singleton off the reflection centre (§14.5). These seven statements hold for arbitrary finite
systems of congruence-interval constraints and are not specific to this problem, to order eight, or
to the conjecture.

**Its blocked residues form a cyclic ball around zero**, its clear window is at least half the
modulus and therefore covers a full period of any proper divisor, and at moduli below 10 each
constraint forbids at most two residues (§14.6).

**A flank has exactly `e` openings**, and the covering of those openings by a mover's blocked set is
counted exactly: with `q | e`, a mover whose blocked openings are the `C`-classes mod `q` covers
`|C|·(e/q)` of them, and `e/q = gcd(d, e)` for the reduced denominator. So **shadowing every opening
requires the gcd-weighted count to reach `e`.** `[Palelei 2026b, §15H, Theorems 15.36–15.39; M §15J, Theorems
15.47–15.50.]`

**There are proved sufficient conditions that are not among the rules of §10** — first-lap clearance,
the `−7` opening, the small-denominator and last-class results — each naming an opening and each
requiring no homogeneity hypothesis. `[Palelei 2026b, §15E–§15G, §15I, §15O.]`

### 15.1 The rules revisited

The certificate rules of §10 are explicit mechanisms guaranteeing an unblocked candidate. Their
**failure conditions** (§10.8) therefore describe the residual configurations on which any general
existence argument must operate, and the trichotomy of §11 is one exact description of that residual
space: the two ends of the resonance count are closed, and the middle — self-similar in its resonant
part, unconstrained in its non-resonant part (§12) — is what remains.

That is the sense in which the rules are useful even where they do not settle the conjecture: they
are not an unrelated collection preceding the real problem, they are partial solutions of it, and
their boundary is a description of the remainder.

### 15.2 What is not established

**No bound on `R` is proved.** The bounded-region sufficient condition of §13 is supported by
measurement and by Theorem 15, and by nothing else.

**Counting does not close it.** At the level of measure the six combs give a factor of 1.5 against;
at the level of blockers the mean is 1.1867 where an argument would need it below 1.

**The middle of the trichotomy is open** at `1 ≤ M ≤ c − 2`, save for the `M = 1` cases R4 reaches.

**No result of §14 bears on existence.** Each constrains the shape of the satisfying set. None of them,
alone or together, shows it non-empty for every configuration.

---

## 16. General `n`

Nothing in §§2–8 depends on the order. Theorem 9, Theorem 10, the boundary set method,
Construction, Localisation and Theorem 13 are proved at general `n` and instantiate at six, seven and
eight at no cost. **Layer 1 is order-free.**

In Layer 2 the position is mixed, and the split is recorded rather than smoothed over:

* **General `n`.** The rules R1–R7 with the exact conditions of §10, R4 among them carrying its
  prime hypothesis; the `φ(n)` count of usable
  flanks and the `φ(n)` budget in R4's pigeonhole; the trichotomy of §11; Theorem 15; the
  covering-question results of §14.1; the spine and small-modulus laws of §14.2; and the seven
  edge-witness results of §14.5, which mention no order at all.
* **Order eight.** The guard and blocking results, the reflection statements of §14.4 (proved at
  order 8; the two-centre law and its two obstructing residues are computed at every order
  `4 ≤ n ≤ 13` and are `[EMPIRICAL]` over that range), and the numerical frontier of §13.

Two facts about small orders are worth recording because they invert the expected difficulty.

**Four disparities are settled at orders six and seven and not at five.** The four-difference
termination result carries the hypothesis `n ≥ 6`. So at six and seven every subject with at most four
distinct disparities is settled unconditionally, by the theorem that is unavailable at five. In that
respect order five is the hard one.

**Order five reduces to `card = 4` exactly.** Subjects with at most three disparities are settled at
every order `n ≥ 4`. And the case cannot be dodged by collapse: the absolute value `|vᵢ − v_k|` can
identify a runner ahead with one behind, but for the fastest and the slowest runner every difference
has one sign, so both extreme subjects of every arrangement carry the full `n − 1` disparities.

**`φ(n)` is the discriminator, not primality and not parity.** `φ(n)/n = ∏(1 − 1/p)` over the primes
dividing `n`; primality is where that product is largest, and `2 | n` forces it to at most `1/2`.

---

## 17. Verification

Every numbered result in §§2–8 and §§10–13 is formalised in Lean 4 with mathlib, with no `sorry`, no
`native_decide`, no `unsafe` and no `admit`, and every theorem depending on at most `propext`,
`Classical.choice` and `Quot.sound` — **with two exceptions, both stated here and in the table**:
Observation 16, flagged at its statement as verified and not derived; and Theorem 14, which is
proved in the text rather than formalised as a single declaration, its second half resting on
Theorem 12, which is formalised. Three artefacts carry the development, each built by an explicit
gate; the largest holds 4,759 theorems, of which 283 are structural and the remainder are generated
instances of a single criterion applied to an enumerated family. The declarations in the table below
are the ones this paper's results depend on; all but one lie in the gated tree, the exception being
Theorem 15's `RBand.R_avoids_bad_bands`, which sits in the development directory alongside the
grouped results of §14 and is axiom-checked there rather than by a gate. The grouped results cited in
§14 are likewise machine-checked and axiom-clean; their individual declarations are indexed in
Palelei (2026b), §§13F, 14I and 15S.

The formalisation is a verification of the stated claims and their dependencies. It is not part of the
mathematical argument, and nothing below should be read as requiring it. Theorem 4 is Palelei
(2026a, Theorem 3.1) and appears here because this paper formalises it, not because it is claimed as
new; the same applies to the boundary set method of §2.1.

| result | declaration |
|---|---|
| Theorem 1 | `lonely_iff_flanks` |
| Theorem 2 | `gaps_all_eq` |
| Corollary 3 | `lonely_ne_pred` |
| Theorem 4 *(Palelei 2026)* | `isolation_iff_coprime`, `card_coprime_eq_totient`, `ap_reference` |
| Theorem 5 | `displacement` |
| Theorem 6 | `survives_of`, `commensurable` |
| Theorem 7 | `bound_le_of_lonely` |
| Theorem 8 | `ratio_condition` |
| **Theorem 9** | `lonely_iff_exists_flank` |
| **Theorem 10** | `clear_at_int_flank_iff_emod`, `flankWorks_iff`, `band_iff_beatty` |
| Theorem 11 | `lonely_of_fixed`, `first_isolation_of_fixed`, `first_isolation_as_zone_run`, `flank_at_first_isolation` |
| Theorem 12 | `bound_le_of_lonely`, `iterate_le_of_lonely`, `exists_fixed_of_lonely` |
| **Theorem 13** | `doors_agree` (order 8), `LRC.SpecN.doors_agree` (general `n`) |
| R1 | `ratio_condition`, `clear_at_last_opening` |
| R2 | `lonely_flank_of_band`, `bandFits_forces_spread`, `spread_zero_iff_ratio` |
| R3 | `flankWorks_of_coprime`, `flankWorks_of_not_resonant` |
| R4 | `flankWorks_of_prime_dvd`, `exists_goodK` |
| R5 | `flankWorks_of_multiples`, `flankWorks_scale` |
| R6 | `ratWorks_le_order`, `ratWorks_one_iff`, `ratWorks_family_fails_iff` |
| R7 | `lonely_of_one_free`, `lonely_of_one_irrational` |
| the general witness form | `flankWorks_of_witness` |
| §10.7's `φ(n)` count | `card_nonresonant_eq_totient`, `shifted_budget_is_totient` |
| §11's trichotomy | `multiples_trichotomy`, `self_rule_applies_iff`, `coprime_rule_applies_iff` |
| Theorem 14 | **proved in the text**; second half from Theorem 12 (`exists_fixed_of_lonely`); `[VERIFIED — 10,677 of 10,677 against the cascade]` |
| Theorem 15 | `RBand.R_avoids_bad_bands` |
| Observation 16 | verified in exact rational arithmetic; **not formalised**, and flagged as an observation |

One body of material in the development record is deliberately absent here: an enumerated census of
difference-set families, which was evidence for the record rather than mathematics for the paper.
Theorem 10 together with the general witness form already gives a mechanical decision procedure for
integer disparity sets, so nothing in the paper depends on it.

Each gate builds every module by explicit target, inventories `sorry`, scans for
`native_decide`/`unsafe`/`admit`, runs `#print axioms` on every declaration, and asserts its own
coverage against an independent count. One gate additionally maintains a register of every
Prop-valued definition, because such a definition is type-checked and never proved: a false one passes
a build, a `sorry` scan and an axiom check alike. Details, digests and the gate outputs are in the
development record.

---

## 18. What remains to prove

**Proved — the structural reductions.** Loneliness is a two-neighbour condition; simultaneous
isolation is the regular `n`-gon; the number of simultaneously lonely runners is never `n − 1`; the
obstruction sets are open and their endpoints clear (§2).

**Proved — the certificate equivalences.** Every lonely instant is represented by a lonely opening,
and conversely (§5); for integer disparities the opening condition is exactly a finite conjunction of
modular memberships, decided by `e` indices (§6).

**Proved — the cascade localisation.** A fixed point is the first lonely instant, ends a boundary-set
run and carries a runner at the threshold; a lonely instant anywhere forces a fixed point; and the
five formulations of Theorem 13 are equivalent, unconditionally and at every order (§7).

**Proved — the closed regions of the rule classification.** Seven certificate rules with exact
conditions, and a trichotomy in which `M = 0` and `M ≥ c − 1` are closed (§§10–11).

**Proved — the candidate and edge structural results.** The covering question is exact over `ℤ`; the
candidate family and its rescaling; the blocker bound `n − 3`; the reflection and its two obstructing
residues; the edge witness and the non-singleton property, both order-agnostic; the window geometry;
the exact covering count on a flank's `e` openings (§14).

**Remaining.** A theorem that rules out the complete blocking of all admissible candidates — that is,
that the clear set of §13 is non-empty for every admissible profile. Equivalently, in the framework's
own objects: that for every disparity configuration some flank has an opening at which every other
disparity reads inside the band.

The reduction achieved is that this statement may be attacked entirely over `ℤ`, on an explicit
candidate family, against at most `n − 3` blockers per candidate in the first band, with a witness
known to sit at an edge if it exists at all, and with the two ends of the resonance count already closed. **It has not
been proved, and nothing in this paper should be read as proving it.**

---

## 19. Glossary

**arrangement** — an injective assignment of real speeds to the `n` runners.
**band** — the readings at circle distance at least `1/n` from the integers.
**boundary set method** — evaluate open cells and boundary points separately; never merge touching
zones; decide a cell by an interior point.
**candidate** — a point `(n m + 1)/s` of the arithmetic family in the `R` coordinate.
**cascade** — the sequence of moves from the bound.
**certificate** — a flank and an opening index, `(e, j)`, together with a proof that the opening is
lonely.
**clear set** — `{ R ≥ 1 : ∀ i, s_i·R mod n ∈ [1, n−1] }`.
**disparity** — one of the subject's speed differences `|vᵢ − v_k|`; the term avoids collision with
the *common difference* of a progression.
**flank** — a disparity used as the denominator of a candidate instant.
**global instant** — an instant at which all `n` runners are lonely at once.
**in the way** — at circle distance strictly less than `1/n` from the subject.
**move** — the step sending `t` to the largest next opening among the runners in the way.
**non-resonant** — coprime to `n`.
**opening** — the instant `(j + 1/n)/e`, at which the flank `e` sits at exactly `1/n`.
**reading** — the quantity `d·t`, or `s·u` in the local coordinate.
**resonant** — sharing a factor with `n`.
**subject** — the runner whose loneliness is at issue.

---

## Data and code availability

The Lean 4 development, the gate scripts that build and audit it, and the measurement scripts quoted
in §§13–14 accompany this paper as supplementary material. The individual statements grouped in §14,
the declaration indices, the version history and the record of routes closed are in Palelei (2026b).

---

## References

Barajas, J. and Serra, O. (2008). The lonely runner with seven runners. *Electron. J. Combin.* 15,
R48.

Bohman, T., Holzman, R. and Kleitman, D. (2001). Six lonely runners. *Electron. J. Combin.* 8(2),
R3.

Palelei, T. (2026a). The φ(n) law for arithmetic progressions in the lonely runner conjecture:
algebraic structure and computational fragility. Zenodo.
https://doi.org/10.5281/zenodo.18158886

Palelei, T. (2026b). A bounding framework for eight lonely runners: development record, statements
and verification apparatus. Technical report, supplementary material to the present paper.

Rosenfeld, M. (2025). The lonely runner conjecture holds for eight runners. arXiv:2509.14111.
Preprint.

