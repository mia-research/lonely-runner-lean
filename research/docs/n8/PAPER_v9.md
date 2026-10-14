

# Deformations of Global Isolation in the Lonely Runner Conjecture

**T. Palelei.** v9.0.

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
for every configuration, and a certificate exhibited under a condition proves the conjecture for
every configuration meeting it. We give seven structural conditions on the differences. On the
count of differences divisible by `n` they close one end of a trichotomy and reduce the other to
the same question with one difference fewer, at the same threshold. The characterisation and the
conditions are formalised in Lean 4.

---

## 1. Introduction

Let `v₁, …, vₙ` be distinct real speeds, each runner moving on a circle of unit circumference at its
own speed, and let `‖x‖` denote the distance from `x` to the nearest integer. Runner `i` is **lonely**
at time `t` if `‖(vⱼ − vᵢ)t‖ ≥ 1/n` for every `j ≠ i`. The Lonely Runner Conjecture, due to Wills and
independently to Cusick, asserts that every runner is lonely at some instant. It is settled for
`n ≤ 7` by arguments particular to each order, the last two being Bohman, Holzman and Kleitman (2001)
at six runners and Barajas and Serra (2008) at seven. A computer-assisted proof for eight runners
has been posted as a preprint (Rosenfeld 2025); nothing in this paper depends on it.

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
business of this paper, and the units of `ℤ/n` that the count `φ(n)` counts in the undeformed
configuration return in the deformed one as the multipliers the certificate rules construct
(§10.7).

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
such instant, with a certificate readable off its halting state. Structural conditions on a difference
set exhibit a certificate outright; on an exact trichotomy they close one end and reduce the other
to the same question with one difference fewer. The characterisation is formalised in Lean 4.

**What remains.** The conjecture is the universal quantifier over configurations: that a certificate
exists for every admissible difference set. This is not a gap in the characterisation, which is proved
in both directions. It is the universal quantifier, and the later sections constrain it — showing
that it may be attacked entirely over `ℤ`, on an explicit candidate family, with a witness known to
sit at the edge of a constraint wherever one exists. What is not yet done is the closing of the
list: the conditions given here do not yet cover every difference set.

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

*Proof.* Order the runners around the circle, and write `g_j` for the gap between consecutive
runners `j` and `j+1`, indices mod `n`.

Suppose both gaps flanking `i` are at least `1/n`, and let `m ≠ i`. The circle is cut by `i` and `m`
into two arcs whose lengths sum to 1, and `circDist` is the shorter of them. One arc runs from `i`
in the direction of increasing index and therefore contains the whole of `g_i`; the other runs in
the direction of decreasing index and contains the whole of `g_{i−1}`. Both arcs are therefore at
least `1/n`, hence so is the shorter, which is what loneliness asks.

Conversely, suppose runner `i` is lonely, and take `m = i+1`. One of the two arcs between them is
exactly `g_i`, and `circDist` is the smaller of the two, so `circDist ≤ g_i`. Loneliness gives
`1/n ≤ circDist`, hence `1/n ≤ g_i`. Taking `m = i−1` gives `1/n ≤ g_{i−1}`. ∎

The converse needs only the two flanking pairs, and not the attainment of any minimum. Two
consequences fix the shape of the problem.

> **Theorem 2.** All `n` runners are simultaneously lonely if and only if every gap is exactly
> `1/n` — the regular `n`-gon.

*Proof.* If every gap is exactly `1/n` then every runner's two flanking gaps are `1/n`, so every
runner is lonely by Theorem 1.

Conversely, suppose all `n` are lonely. Each gap flanks the two runners at its ends, so Theorem 1
gives `g_j ≥ 1/n` for every `j`. The gaps partition the circle, so `Σ_j g_j = 1`. The slacks
`g_j − 1/n` are therefore nonnegative and sum to `1 − n·(1/n) = 0`, so each is zero. ∎

> **Corollary 3.** The number of simultaneously lonely runners lies in `{0, …, n−2} ∪ {n}`. It is
> never exactly `n − 1`.

*Proof.* Suppose exactly `n − 1` runners are lonely at `t`, all but runner `j`. Every gap has two
endpoints, and at most one of them is `j`, so every gap flanks at least one lonely runner and is
therefore at least `1/n` by Theorem 1. The gaps sum to 1, so by the argument of Theorem 2 every gap
is exactly `1/n`. But then both gaps flanking `j` are `1/n`, so `j` is lonely too, and `n` runners
are lonely rather than `n − 1`. ∎

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
instant the cascade of §7 constructs, and every certificate of §6, is such an endpoint, for some
runner and some lap — that is what makes the certificate a pair of integers rather than a real
number. An instant named by a rule of §10 need not be one (R6's `1/q` generally is not); Theorem 9
converts any lonely instant into an endpoint no later than it.

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

### 2.2 What the method excludes, and why

The arguments below use exact arithmetic and the geometry of lap zones. They use no measure, no
density, no equidistribution, and no covering. That is not a stylistic preference, and it is worth
saying why at the outset, because each exclusion has a reason in the object rather than in taste.

**No measure or density argument, because at the extremal configuration there is nothing to
average over.** An analytic method locates a target through neighbourhoods. At the arithmetic
progression — which Theorem 2 identifies as the rigid configuration any general argument must
cover — the set of instants at which all `n` runners are lonely is, on `(0,2]`, exactly the eight
points `1/8, 3/8, 5/8, 7/8, 9/8, 11/8, 13/8, 15/8`. Lebesgue measure zero. There are no
neighbourhoods there, so the exclusion is a consequence of the object.

**No covering, and no argument that concludes by emptiness.** The construction forms no complement
and exhibits no set to be shown empty; it runs to a named instant and produces the pair `(e, j)`.
An argument that establishes a lonely opening exists without naming or bounding one is a different
kind of object. The test is worth stating precisely, because it is about proofs rather than statements: a result
here may perfectly well conclude with an unbounded `∃`. What is required is that the *argument*
produce a bound on the witness. A reader checking this should read the proof, not the quantifier.

**No bound on when the instant falls, and no count of the steps taken to reach it.** The conjecture
asks for loneliness at *some* positive time. A cap on the cascade, and a count of its moves, are both
stronger obligations than it carries. Nor is a single formula covering every disparity set
required: the form is conditions with proofs (§8).

**No search, because there is nothing to search.** The cascade is fixed by the speeds: the runners
in the way at `t` determine the move, there is no candidate list, and nothing is ranked or guessed
(§7).

**No global clock, and no pinned runner.** Each runner receives its own instant, read in its own
coordinate `u = d_min·t` (§4); loneliness of runner `i` is a statement about the differences `v_j − v_i`,
so no runner is placed at rest. The one qualification is the reference progression itself, which
*is* globally isolated (§3) — and deviations from it are then read runner by runner.

**Boundary discipline throughout.** Open cells and boundary points are evaluated separately,
touching zones are never merged, and a cell is decided by an interior point (§2.1).

These exclusions are what make the paper's positive results the shape they are. A proof in this
framework is a finite list of cases, each a condition on the disparity set together with a proof
that a certificate exists under it, the list closing when the conditions are jointly exhaustive.
Each case is discharged by establishing existence — by pigeonhole, induction, contradiction or
construction — and a closed form for `e` or `j` is more than the obligation asks. Counting
arguments are admissible **as tools**; what is excluded is covering as the *form* of a conclusion.

---

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

The count recurs, and that recurrence is one thread of the paper. The global instants are exactly
the units of `ℤ/n`; §10.7 shows the same units in the certificate — every opening index `n j + 1` is
a unit, and the multipliers the rules of §10 construct (R3's inverse `s`, R4's `k`) are units, with
R4's pigeonhole budgeted by `φ(n)`. The invariant of the undeformed configuration reappears in the
arithmetic of the deformed one.

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

*Proof.* A direct computation. At `t = a/(n d)` runner `k` of the deformed arrangement sits at

```
    (v₀ + k d + e_k) · a/(n d)  =  v₀ a/(n d)  +  (k a)/n  +  (e_k a / d) · (1/n).
```

The first term is common to every runner and is a rotation of the whole configuration. The second
places runner `k` at the vertex `k a / n`, and by Theorem 4 these vertices are all `n` of them,
since `gcd(a,n) = 1`. The third is the displacement, and written in units of the `n`-th `1/n` its
size is exactly `e_k a / d`. ∎

> **Theorem 6.** The global instant survives the deviation if and only if every displacement is a
> whole number of `n`-ths and `k ↦ k a + e_k a / d (mod n)` is a bijection of `ℤ/n`.

*Proof.* Write `w_k = e_k a / d` for the displacement of Theorem 5, so that runner `k` sits at
`(k a + w_k)/n` up to the common rotation.

Suppose each `w_k` is an integer and `k ↦ k a + w_k` is a bijection of `ℤ/n`. For `k ≠ k'` the two
runners are separated by `((k a + w_k) − (k' a + w_{k'}))/n`, whose numerator is an integer not
divisible by `n` — by injectivity — so the circle distance between them is at least `1/n`. Every
pair is separated, so every runner is lonely, and the global instant survives.

Conversely, suppose the global instant survives, so all `n` runners are lonely at `t`. By Theorem 2
every gap is exactly `1/n`, so the `n` positions are a translate of the uniform grid
`{0, 1/n, …, (n−1)/n}`. Runner `k` sits at `(k a + w_k)/n` up to that common translate, so
`k a + w_k` differs from an integer by a quantity independent of `k`; normalising `e₀ = 0` makes
runner `0`'s value the integer `0`, so the quantity is `0` and every `k a + w_k` is an integer.
Since `k a` is an integer, so is `w_k`: every displacement is a whole number of `n`-ths. Finally the
`n` positions are distinct and lie on the `n` grid points, so `k ↦ k a + w_k (mod n)` is injective
on `ℤ/n` and hence a bijection. ∎

Both directions are formalised: the forward one as `ConstructionN.survives_of`, the converse as
`int_of_pairwise_sep` (integrality of every displacement) and `not_dvd_of_sep` (non-congruence,
hence injectivity), in `ConstructionN/Integrality.lean`.

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

*Proof.* If `0 < t < 1/(n·d_min)` then `0 < d_min·t < 1/n`, so the distance from `d_min·t` to the
nearest integer is at most `d_min·t < 1/n`, and the subject is not lonely at `t`. ∎

We write `t₀ = 1/(n·d_min)` and call it **the bound**: below it the nearest runner has not yet left
the subject, so nothing earlier can be lonely. It is where the construction of §7 begins.

The whole problem is now visible in one line: **find `u ≥ 1/n` at which every reading lies in the
clear band**, that is at distance at least `1/n` from the integers.

One case falls out immediately.

> **Theorem 8 (the ratio condition).** If `d_max ≤ (n−1)·d_min` then the subject is lonely at
> `u = 1/n`, that is at `t = 1/(n·d_min)`.

At that instant every reading is `s/n` with `s ∈ [1, n−1]`, hence at distance at least `1/n` from the
integers. The
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

*Proof.* The converse is immediate, an opening being an instant.

For the forward direction let `t > 0` be lonely. For a disparity `e` put
`T_e = (⌊e·t⌋ + 1/n)/e`, the opening of `e` at its last completed lap before `t`. Since `t` is
lonely, `‖e·t‖ ≥ 1/n`, so the fractional part of `e·t` lies in `[1/n, 1 − 1/n]`; in particular it is
at least `1/n`, which says exactly `T_e ≤ t`. Let `T = max_e T_e`, attained at some `e*`, so that
`T` is an opening of the flank `e*` and `T ≤ t`.

`T` is lonely. Let `d` be any disparity. From `T ≥ T_d` we get `d·T ≥ ⌊d·t⌋ + 1/n`, and from
`T ≤ t` we get `d·T ≤ d·t < ⌊d·t⌋ + 1`. So `d·T` lies in `[⌊d·t⌋ + 1/n, ⌊d·t⌋ + 1)`, whence its
fractional part is `d·T − ⌊d·t⌋ ≥ 1/n`; and that fractional part is at most the fractional part of
`d·t`, which is at most `1 − 1/n` because `t` is lonely. So `‖d·T‖ ≥ 1/n` for every `d`. ∎

**The forward direction is the substantive one, and it is a structural statement, not a reduction in
search space.** The proof produces, from any lonely `t`, a lonely opening no later than `t`. So *every lonely instant is necessarily represented by a lonely
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

*Proof.* At the opening `(j + 1/n)/e` the reading of `d` is `d·(j + 1/n)/e = d(n j + 1)/(n e)`.
Loneliness asks that this be at distance at least `1/n` from the integers, which after multiplying
by `n e` says that `d(n j + 1)` is at distance at least `e` from the multiples of `n e`. Writing
`x = d(n j + 1) mod n e`, so that `0 ≤ x < n e`, the two conditions are `x ≥ e` and `n e − x ≥ e`,
that is `e ≤ x ≤ (n−1)e`.

For the periodicity, `d(n(j + e) + 1) = d(n j + 1) + d·n e`, which is congruent to `d(n j + 1)`
modulo `n e`, so the residue — and hence the condition — is unchanged. ∎

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
> at which the opening `(j + 1/n)/e` is lonely.

The definition holds for arbitrary real disparities, and by Theorem 9 a subject has a certificate
exactly when it is lonely. For whole-number disparities it is exactly the condition of Theorem 10,
checked in `n − 1` modular reductions. A certificate carries no trace of how it was found.

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

The instant `1/6` is not an opening of any flank; Theorem 9 returns a lonely opening no later than
it, here the cascade's `9/56`. So the cascade and the rules are two ways to a lonely instant, and
they generally name **different** ones: `9/56` here against `1/6`. The cascade is a construction that always terminates when the
subject is lonely and needs no condition; a rule is a shortcut that bypasses the construction
entirely but applies only where its condition holds. Neither is the other's approximation.

### 7.2 Construction and Localisation

> **Theorem 11 (Construction).** If some step of the cascade is fixed, at `T`, then: (a) the subject
> is lonely at `T`; (b) no positive instant before `T` is lonely; (c) `T` is the end of a run of
> lap-completion zones from the bound, each containing the end of the one before, and every such run
> that ends at a lonely instant ends at `T`; and (d) some runner
> sits at exactly `1/n`, as the nearest ahead or the nearest behind.

*Proof.* **(a)** The move fixes `t` exactly when no runner is in the way at `t`, and "no runner in
the way" says `‖d·t‖ ≥ 1/n` for every disparity `d`, which is loneliness.

**(b)** Nothing below the bound is lonely, by Theorem 7. It therefore suffices to show that no
instant strictly between two consecutive cascade steps is lonely, and that none strictly between the
last step and `T` is. Let `t` be a step that is not fixed, and let `d` be a runner in the way at `t`.
A runner in the way at `t` remains in the way until its own next opening, so every instant in
`[t, o_d)` has `d` in the way and is not lonely, where `o_d` is that next opening. The move sends `t`
to the **largest** next opening among the runners in the way, so for every instant `u` in `(t, T')`,
where `T'` is the image of `t`, some runner in the way at `t` has not yet reached its next opening
and so is in the way at `u`. Hence no instant in `(t, T')` is lonely. Chaining along the finitely
many steps from the bound to `T` leaves no lonely instant below `T`.

**(c)** Each move lands on the next opening of one runner in the way, that is on the far endpoint of
that runner's lap-completion zone `((N − 1/n)/d, (N + 1/n)/d)`. The runner that sets the following
move is in the way at that endpoint, so the endpoint lies inside its zone: each zone in the sequence
contains the end of the one before. The sequence begins at the bound and ends at `T`, which is the
required run. Conversely, let a run of such zones from the bound end at a lonely instant `T'`. Its
zones are open and each contains the end of the one before, so together they cover every instant
from the bound up to `T'`. If `T' > T`, then `T` lies inside one of them and is not lonely, against
(a); and `T' < T` is excluded by (b). So `T' = T`. The run itself need not be unique — for
`{1, 8, 16}` at order eight the runs `zone(8)` and `zone(16) → zone(8)` both end at `9/64` — but its
end is.

**(d)** If `T` is the bound then `d_min` reads exactly `1/n` there. Otherwise `T` is the image of the
previous step, hence the next opening `(N + 1/n)/d` of some runner `d`, and at that instant
`‖d·T‖ = 1/n` exactly. Since the reading is at the threshold and every other reading is at least
`1/n`, that runner is the nearest ahead or the nearest behind. ∎

So a fixed point is not merely *a* lonely instant. It is the **first** one, it terminates a
boundary-set run, and it carries a runner at the threshold — which is why the halting instant is
always an opening, and why the certificate has the form `(e, j)`.

> **Theorem 12 (Cascade localisation).** For every positive instant `s` at which the subject is
> lonely: `s ≥ 1/(n·d_min)`; every step of the cascade is at most `s`; `s` is matched by a lonely
> opening no later than it; and **the cascade reaches a fixed point**.

*Proof.* The first clause is Theorem 7. The third is the forward direction of Theorem 9, whose proof
produces a lonely opening no later than the given instant.

For the second, induct along the cascade. The bound is at most `s` by the first clause. Suppose a
step `t` satisfies `t ≤ s` and is not fixed, and let `d` be any runner in the way at `t`. Then `d` is
obstructing at `t` and clear at `s`, and `t ≤ s`, so `d`'s first opening at or after `t` is at most
`s`. The move sends `t` to the largest of those openings over the runners in the way, so its image is
at most `s`.

The last clause carries the equivalence, and its proof is a finiteness argument and nothing else:
by the second clause every step is at most `s`, so the steps lie in the finite set of openings
`(k + 1/n)/d` with `0 ≤ k ≤ ⌈d·s⌉`, and a sequence that strictly increases until it is fixed cannot
remain in a finite set without being fixed. ∎

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

*Proof.* **(2) ⟹ (1)** is Theorem 11(a), and **(1) ⟹ (2)** is the last clause of Theorem 12.

**(2) ⟹ (3).** A cascade that reaches a fixed point is constant from that step on, hence bounded.

**(3) ⟹ (2).** Suppose the steps are bounded by `U`. Every step is an opening `(k + 1/n)/d` of one
of the finitely many disparities with `0 ≤ k ≤ ⌈d·U⌉`, so the steps lie in a finite set. A step that
is not fixed is strictly less than its image, so if no step were fixed the sequence would be
strictly increasing inside a finite set, which is impossible.

**(1) ⟹ (4)** is Theorem 12's third clause: a lonely instant is matched by a lonely opening of one
of the subject's own disparities, no later than it. **(4) ⟹ (1)** is immediate, an opening being an
instant.

**(2) ⟹ (5).** Beyond a fixed point no runner is in the way, and below it there are finitely many
steps, so each runner is in the way at finitely many steps.

**(5) ⟹ (2).** If each of the `n − 1` runners is in the way at only finitely many steps then, there
being finitely many runners, beyond some step none is in the way; that step is fixed. ∎

Nothing in the argument mentions the order except through the threshold `1/n`, which is why it holds
at every `n ≥ 2`.

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

**And this fixes what a proof is.** Because the equivalence is unconditional and runs both ways,
exhibiting a flank and an opening index is not evidence *for* the conjecture at that configuration.
It **is** the conjecture there, written in the framework's own objects. A case discharged is
therefore a case proved outright, with nothing held in reserve and nothing further owed on it; and a
proof of the whole is a finite list of such cases whose conditions are jointly exhaustive.

Three shapes ask for more than that, and importing any of them puts an attempt on a route the
conjecture does not require.

| foreign shape | why it is more than is owed |
|---|---|
| a **cap** — a bound on how far the cascade runs | the conjecture asks for loneliness at *some* instant; bounding how far a run goes is an obligation it does not carry |
| a **move count** — "the `N`-th step is fixed" | a bound on *how many* steps, where the conjecture places none |
| a **uniform theorem** — one statement or formula covering every disparity set | the form is conditions with proofs. Demanding a single formula is the same shape in another hat |

None of the three is used below, and none is needed. Counting arguments — pigeonhole, residue counts
— are admissible as **tools** throughout; what is excluded is covering as the *form* of a conclusion
(§2.2).

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

This is not a missing direction in the equivalence. What remains is a universal quantifier: it asks
whether the equivalent condition — for whole-number disparities an explicit finite arithmetic
condition — is *universally satisfiable*.

Everything in Layer 2 works **inside** the equivalent condition. §10 gives conditions under which a
certificate is exhibited outright — each of which, by §8, therefore *proves* the conjecture wherever
it holds, rather than supporting it. §§11–12 classify what those hypotheses reach and
what they leave. §13 fixes a second coordinate; §14 describes the candidates a certificate is drawn
from; §15 states what the universal question has been reduced to and constrained by.

---

## 10. Structural certificate rules

A rule is a condition on a disparity set together with a proof that a named instant is lonely
whenever the condition holds. Each is elementary and proved at general `n`. Where a rule's
condition holds, the conjecture is established for that configuration. One entry, R5, is a
reduction rather than a rule: it trades the set for a smaller one at the same threshold.

There are seven, and they are grouped here by mechanism rather than by order of discovery.

| rule | condition on the disparity set | the instant it names |
|---|---|---|
| **R1** the ratio condition | `d_max ≤ (n−1)·d_min` | `1/(n·d_min)` |
| **R2** the band ladder | every disparity in `[(nL+1)e/(nj+1), (nL+n−1)e/(nj+1)]` for some `j, L` | the `j`-th opening of `e` |
| **R3** the non-resonant flank | `gcd(e, n) = 1` and no disparity divisible by `n` | `a = e·(e⁻¹ mod n)` |
| **R4** the divisible flank | `n \| e`, `e` largest, no other disparity divisible by `n`, fewer than `φ(n)` of them coprime to `n` | `a = k·e + 1`, `k` a unit from a pigeonhole |
| **R5** the self-similar reduction | every disparity but at most one a multiple of `n` | the opening `j₀ + f·i` of the flank `n·f`, from a certificate `(f, j₀)` of the quotients |
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

**R4, the divisible flank.** The complementary case, when the flank *is* divisible by `n`. At
`a = k·e + 1` the flank reads `e`, and every other disparity `d < e` reads `e·(d·k mod n) + d`, which
is in band exactly when `d·k mod n ∉ {0, n − 1}`. Take the multiplier `k` from the units of `ℤ/n`.
A unit never sends a disparity not divisible by `n` to `0`; and `d·k ≡ n − 1` forces `d` coprime to
`n`, since `n − 1` is a unit, and for such `d` it fixes `k`. So each non-flank disparity coprime to
`n` rules out exactly one unit and no other disparity rules out any, and a unit survives whenever
fewer than `φ(n)` of them are coprime to `n`. No primality is used. At prime `n` every non-flank
disparity is coprime to `n` and the condition reads `|L| < n − 1`, the form in which the rule was
first proved.

**R5, the self-similar reduction.** Suppose every disparity but at most one is a multiple of `n`: the
set is `n·M ∪ {x}` with `n ∤ x`, or `n·M`. A multiple `n·m` reads `n·((m·a) mod n f)` at the flank
`n·f` — the scale factors through the modulus — so it is clear exactly when `m` is clear at the flank
`f`, one scale down. A certificate `(f, j₀)` of `M` therefore clears every multiple at each index
`j₀ + f·i`, `0 ≤ i < n`, since all of them have the same residue mod `f`. At those indices the free
disparity `x` reads `n f·((q + x·i) mod n) + ρ`, with `q` and `ρ` fixed by `j₀`, and is clear once
`(q + x·i) mod n ∉ {0, n − 1}`. Because `n ∤ x`, consecutive positions differ; two consecutive ones
can both be bad only when `x ≡ ±1 (mod n)`, and then the third is `1` or `n − 2`. So at `n ≥ 3` one of
`i = 0, 1, 2` clears `x`. Conversely, if `t` is lonely for the whole set, `n·t` is lonely for `M`, and
Theorem 9 returns a certificate of `M`. Hence:

> **R5.** At `n ≥ 3`, a set `n·M ∪ {x}` with `n ∤ x` has a certificate exactly when `M` has one, and
> `n·M` has one exactly when `M` has one.

The threshold is unchanged, `1/n`: this is the same obligation with one disparity fewer.

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
condition but the general form of one. R1–R5 exhibit their witness in this form. R7 exhibits an
opening, but over real disparities, outside this integer form. R6 names an instant that need not be
an opening, and reaches one through Theorem 9.

R3 was first proved with `n` prime. The hypothesis was used in exactly two places: to obtain
`gcd(e, n) = 1` from `n ∤ e`, and to split `n | d·s` by Euclid's lemma. Neither needs a prime. Take
coprimality as the hypothesis, and the second follows because `s` is a unit. The witness is
`a = e·s` where `e·s ≡ 1 (mod n)`, and the readings are `e·(d·s mod n)`; the band holds exactly when
`n ∤ d·s`, which since `gcd(s,n) = 1` is exactly `n ∤ d`. Nothing in that is prime.

So R3's condition is that the flank be **non-resonant**, `gcd(e, n) = 1`. At prime `n` that
coincides with `n ∤ e`, which is why primality appeared load-bearing. There are `φ(n)` non-resonant
residues. They are not the only usable flanks — R4's flank is divisible by `n`, and §12's
`{1, 2, 3, 5}` is certified at `e = 5` — so `φ(n)` does not count the usable flanks in general. What it
counts is the multipliers: R3's `s` and R4's `k` are units, and every opening index `n j + 1` is
itself a unit, so the framework never exhibits a witness outside the unit group.

The same units govern R4, and there the count is a budget. Only the non-flank disparities coprime to
`n` cost a unit, so R4 needs fewer than `φ(n)` of them. Charging every non-flank disparity against the
budget, as the rule's first form did, needs `n − 2 < φ(n)`, which holds exactly at prime `n`; that is
why R4 first appeared with a prime hypothesis. At `n = 8`, `φ(8) = 4`, and the refined count admits up
to three odd non-flank disparities.

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
> **R5 reduces the set** exactly when at most one disparity avoids `n`.

Two consequences. R3 is subsumed: its condition is the `q = n` instance of R6, and R6 does not even
require a coprime flank to exist. And R3 and R5 are the two ends of a single count, which §11 makes
exact.

---

## 11. What the rules cover: the trichotomy

Write `M` for the number of disparities divisible by `n`, and `c` for the number of disparities.

| region | standing |
|---|---|
| `M = 0` | **closed** — R6 at `q = n`, equivalently R3 |
| `M ≥ c − 1` | **reduced** — R5: the same obligation with one disparity fewer, at the same threshold |
| `1 ≤ M ≤ c − 2` | **not closed by the count alone**. R4 reaches `M = 1` when the multiple is the largest disparity and fewer than `φ(n)` of the others are coprime to `n` |

The split is exhaustive. **R6 closes the lower end of the resonance count, and R5 reduces the upper
end to the same question with one disparity fewer**, so in the difference-set form a configuration
with the fewest disparities on which the conjecture fails would lie in the middle. That is a
statement about the count, not about how often the rules happen to fire.

**The middle is not the remaining region, and this section should not be read as saying so.** Only
R3 and R5 are indexed by `M`. R1, R2, R4, R6 and R7 are conditions of other kinds — R1 fires
whenever the spread is within `n − 1`, R6 whenever any `q ≤ n` divides no disparity — and each
reaches into the middle without reference to the count. Both middle examples worked in this paper
are settled: §7.1's set by R6 at `q = 6`, and §12's `{1,2,3,5}` by R4. What remains is the set on
which **all** of R1–R7 fail, R5 applied as a reduction, and §10.8 gives those conditions.

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

R3 is the case where the first part is empty; R5 is the case where the second has at most one
member. The middle is where the second has two or more, and there the recursion does not close on
its own.

**Why it does not close — the example.** Take the disparity set `{1, 2, 3, 5}` at order five. The
resonant part is `{5}`, which descends. But `1, 2, 3` are not multiples of 5 and have nowhere to go:
the set does not scale. That is the whole obstruction, and it is structural rather than a matter of
effort. **The recursion carries a set down when at most one disparity stays behind**: a single free
disparity is absorbed by a shift of the opening index (R5). With two or more, one shift must clear
all of them at once.

The lift itself is not limited to one free disparity. A certificate `(f, j₀)` of `M` lifts to the
flank `n·f` of `n·M ∪ X` whenever one shift `i < n` puts every `x ∈ X` at a position
`(q_x + x·i) mod n ∉ {0, n − 1}`. A free disparity coprime to `n` blocks exactly two shifts; one
sharing the factor `g = gcd(x, n) ≥ 2` with `n` blocks at most `g`, because `0` and `n − 1` never lie
in the same coset of `gℤ/n`. So a shift survives whenever those costs total less than `n`. (The lift
is formalised; the cost count is proved here and is not yet formalised.)

The set is nonetheless lonely, and the rules reach it: R4 applies — `n = 5` is prime, `5` is the
largest disparity and the only multiple of `5` — and names the flank `e = 5` at `j = 1`. The flank
`e = 3` at `j = 2` also clears. What the set illustrates is not that the rules miss it but that the
**recursion** stalls: the resonant part descends and the non-resonant part does not. The example of
§7.1 is likewise in the middle (`M = 1`, `c = 7`) and is settled by R6 at `q = 6`. The middle is
where the self-similar descent fails to close on its own, not where the conditions of §10 fail.

**What the middle needs.** A condition on the disparity set under which some flank and some index can
be shown to exist — by pigeonhole, induction, contradiction or construction.

---

## 13. The `R` coordinate

§14 works with the certificate condition in a second coordinate. Measure an instant in units of the
bound, `R = t/t₀ = n·d_min·t`, and write `s_i = d_i/d_min`. The reading of `d_i` is then `s_i·R/n`,
so the subject is lonely at `R` exactly when

```
    s_i·R  mod  n   ∈   [1, n−1]      for every i.
```

This is a change of variable, not a result, and it neither strengthens nor weakens anything in
Layer 1. The companion record (Palelei 2026b, §11 and §16B) carries three statements made in this
coordinate — the cascade's halting value of `R` as a minimum over this set, the bands `R mod n` must
avoid, and the growth of the cascade's length at order five. None of them is used here.

---

## 14. Candidate geometry

*This section describes the candidates a certificate is drawn from, in the coordinate of §13. Every
result cited here is machine-checked and axiom-clean; statements are given in groups, with the
individual theorems and their declarations in Palelei (2026b), §§13–15. **No result in this section
discharges a case** — each constrains the question rather than answering any part of it.*

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

### 14.2 The candidate family, and rescaling

The satisfying points of interest carry numerators `n m + 1`; at order eight the candidates
`(8m+1)/s_k` are the spine of the problem **rescaled by `s_k`**, the modulus moving accordingly. A
reading `s_j = c·s_k` blocks the `s_k`-candidates exactly when `8 | c` — the divisibility test applied
to the rescaled reading. `[Palelei 2026b, §14A, Theorems 14.1–14.4.]`

At small moduli the picture collapses to bare non-divisibility: for `2 ≤ b ≤ n − 1` a unit constraint
is exactly non-divisibility, and the pattern **breaks at `b = 8`**, one past `n − 1`. `[Palelei 2026b, §14B,
Theorem 14.5; §15A, Theorems 15.1–15.3, at every order.]`

### 14.3 Who can block

A reading never blocks its own candidates — `(s_k·A) mod 8s_k = s_k` exactly, with no further
hypothesis — and the unit reading never blocks a candidate **whose ratio lies in the first band**,
`s_k ≤ A ≤ 7 s_k`, equivalently `1 ≤ R ≤ 7`. Hence **at such a candidate the blocker count is at most
`n − 3`.** The band hypothesis is not decorative: without it the unit can block and the bound is
`n − 2`.
`[Palelei 2026b, §14C, Theorems 14.6–14.8.]`

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
all that enters — which is why the flank description of §6 and the candidate description of §14.2 are
the same description. `[Palelei 2026b, §15D, Theorem 15.15.]`

**The largest flank is a strengthening the framework does not require.** Theorem 9 permits *any*
flank, and results stated for the largest one are correspondingly narrower.

---

## 15. What the universal question has been reduced to

Collecting Layer 2. For a subject with integer disparities, existence at that subject is the
statement that some flank is clear at some opening — a certificate `(e, j)`. The following are
established about the candidates such a certificate is drawn from, without discharging the cases
that remain.

**It is decided by finitely many integer inequalities.** Not approximated by them: proved equivalent
(§14.1). Whatever the eventual argument, it may be conducted entirely over `ℤ`.

**Its candidates are an explicit arithmetic family.** The numerators are `n m + 1`, the flank supplies
the denominator, and rescaling by a reading moves the whole picture to a known modulus (§14.2).

**At most `n − 3` readings can block a candidate in the first band** — a reading never blocks its own
candidates unconditionally, and the unit never blocks one with `s_k ≤ A ≤ 7 s_k` (§14.3).

**Wherever a certificate exists, one exists with a constraint exactly at an edge**, and the
satisfying set is never a singleton off the reflection centre (§14.5). These seven statements hold for arbitrary finite
systems of congruence-interval constraints and are not specific to this problem, to order eight, or
to the conjecture.

**Its blocked residues form a cyclic ball around zero**, its clear window is at least half the
modulus and therefore covers a full period of any proper divisor, and at moduli below 10 each
constraint forbids at most two residues (§14.6).

**A flank has exactly `e` openings**, and the covering of those openings by a mover's blocked set is
counted exactly: with `q | e`, a mover whose blocked openings are the `C`-classes mod `q` covers
`|C|·(e/q)` of them, and `e/q = gcd(d, e)` for the reduced denominator. So **shadowing every opening
requires the gcd-weighted count to reach `e`.** `[Palelei 2026b, §15H, Theorems 15.36–15.39; §15J, Theorems
15.47–15.50.]`

**There are proved sufficient conditions that are not among the rules of §10** — first-lap clearance,
the `−7` opening, the small-denominator and last-class results — each naming an opening and each
requiring no homogeneity hypothesis. `[Palelei 2026b, §15E–§15G, §15I, §15O.]`

### 15.1 The rules revisited

The certificate rules of §10 are explicit mechanisms guaranteeing an unblocked candidate. Their
**failure conditions** (§10.8) therefore describe the residual configurations on which any general
existence argument must operate, and the trichotomy of §11 is one exact description of that residual
space: the lower end of the resonance count is closed, the upper end reduces to one disparity fewer,
and the middle — self-similar in its resonant part, constrained additionally by two or more
non-multiples (§12) — is what remains.

That is the sense in which the rules are useful even where they do not settle the conjecture: they
are not an unrelated collection preceding the real problem, they are partial solutions of it, and
their boundary is a description of the remainder.

### 15.2 What the conditions do not yet cover

**The list of §10 is not yet exhaustive.** What remains are the difference sets on which all of
R1–R7 fail — the intersection of §10.8's failure conditions. That is the whole of what is owed.

**No result of §14 discharges a case.** Each constrains the shape of the satisfying set; none of
them, alone or together, discharges a difference set that §10's conditions leave uncovered.

---

## 16. General `n`

Nothing in §§2–8 depends on the order. Theorem 9, Theorem 10, the boundary set method,
Construction, Localisation and Theorem 13 are proved at general `n` and instantiate at six, seven and
eight at no cost. **Layer 1 is order-free.**

In Layer 2 the position is mixed, and the split is recorded rather than smoothed over:

* **General `n`.** The rules R1–R7 with the exact conditions of §10, R4 with no primality and R5 as
  a reduction; the units as multipliers and the `φ(n)` budget in R4's pigeonhole; the trichotomy of
  §11; the covering-question results of §14.1; the spine and small-modulus laws of §14.2; and the seven
  edge-witness results of §14.5, which mention no order at all.
* **Order eight.** The guard and blocking results, and the reflection statements of §14.4 (proved
  at order 8; the two-centre law and its two obstructing residues are computed at every order
  `4 ≤ n ≤ 13` and not proved there).

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

Every numbered result (Theorems 1–13) and every rule of §10 is formalised in Lean 4 with mathlib,
with no `sorry`, no `native_decide`, no `unsafe` and no `admit`, and every theorem depending on at
most `propext`, `Classical.choice` and `Quot.sound`. The one statement proved in the text and not
formalised is the cost count of §12. The declarations in the table below are the ones this paper's
results depend on, and each lies in a gated tree. The grouped results cited in §14 are machine-checked
and axiom-clean in the development record; their individual declarations are indexed in
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
| Theorem 6 | `survives_of` (forward), `int_of_pairwise_sep` and `not_dvd_of_sep` (converse), `commensurable` |
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
| R4 | `flankWorks_of_resonant_flank`, `exists_unit_goodK`; the prime form `flankWorks_of_prime_dvd` as `flankWorks_of_prime_dvd'` |
| R5 | `certificate_iff_of_one_free`, `certificate_iff_of_multiples`, `flankWorks_lift`, `exists_lift_index_one` |
| R6 | `ratWorks_le_order`, `ratWorks_one_iff`, `ratWorks_family_fails_iff` |
| R7 | `lonely_of_one_free`, `lonely_of_one_irrational` |
| the general witness form | `flankWorks_of_witness` |
| §10.7's units | `witness_is_unit`, `card_nonresonant_eq_totient`, `exists_unit_goodK`, `shifted_budget_is_totient` |
| §11's trichotomy | `multiples_trichotomy`, `self_rule_applies_iff`, `coprime_rule_applies_iff` |

One body of material in the development record is deliberately absent here: an enumerated census of
difference-set families, which was evidence for the record rather than mathematics for the paper.
Theorem 10 together with the general witness form already gives a mechanical decision procedure for
integer disparity sets, so nothing in the paper depends on it.

The build gates, their outputs and the digests of the development are in the development record.

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

**Proved — the rule classification.** Certificate rules with exact conditions, and a trichotomy
whose lower end `M = 0` is closed and whose upper end `M ≥ c − 1` reduces to the same obligation with
one disparity fewer (§§10–11).

**Proved — the candidate and edge structural results.** The covering question is exact over `ℤ`; the
candidate family and its rescaling; the blocker bound `n − 3` in the first band; the reflection and its two obstructing
residues; the edge witness and the non-singleton property, both order-agnostic; the window geometry;
the exact covering count on a flank's `e` openings (§14).

**Remaining.** Further cases. A proof in this framework is a finite list of conditions on the
disparity set, each with a proof that a certificate exists under it, the list closing when the
conditions are jointly exhaustive (§2.2). The trichotomy on `M` is exhaustive; its lower end is closed and
its upper end reduces to one disparity fewer (§11). What is owed is conditions covering the disparity sets on which **all** of R1–R7
fail — the intersection of the failure conditions of §10.8, not the middle of the trichotomy, which
R1, R2, R4, R6 and R7 already reach into — each discharged by exhibiting `(e, j)`.

Those cases may be discharged entirely over `ℤ`, on the explicit candidate family of §14.2, against
at most `n − 3` blockers per candidate in the first band, and with a certificate known to sit at an
edge wherever one exists. Discharging a case asks only that a certificate exist under its condition —
by pigeonhole, induction, contradiction or construction. A closed form for `e` or `j` is more than
the obligation requires, as is any bound on when the instant falls.

**The list is incomplete; the entries on it are not provisional.** Every arrangement satisfying any
of the rules of §10 is settled, and at every order those are infinitely many. What is not yet done
is the closing of the list: the conditions of §10 do not yet jointly exhaust the disparity sets, and
the middle of §11 is not the region that remains.

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

The Lean 4 development and the gate scripts that build and audit it accompany this paper as
supplementary material. The individual statements grouped in §14,
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

