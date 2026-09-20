# LRC(8) — proof sketch (v5)

2026-09-13. n = 8, circle of circumference 1, eight runners starting together at distinct
constant speeds, threshold 1/8. T. Palelei's construction.

**What this is.** The spine of the argument, from scratch, in the construction's three objects —
**gaps**, **`d_min`**, **laps** — with each step labelled by what supplies it and the one open
joint marked. It is a sketch, not the candidate; `PROOF_CANDIDATE_v3.md` remains canonical for
the written-out proofs.

**v1** was a conversational draft; **v2** put adjacency mod `n` into §2 as the definition and
separated location from time in §5. **Changes in v5**: **§7d** is new — the three regimes (AP, rational displacement, irrational
displacement), and the **window-widening lemma** that covers the third, which turns out to be the
same lemma as the gcd case with a second trigger. Owner-raised, with the worked irrational case.

**Changes in v4**: **§7c** is new — the cascade (AP, then grid, then an enlarged step), the
**ceiling** `D ≤ 7·d_min(i)` that bounds how far the step can be enlarged at all, the closed form
for the step that clears, and the exhibited configuration where nothing clears. The sweep behind
it is pre-registered at `PREREG_DSWEEP_v1.md`; what is reported here is that spec's
characterisation block only — descriptive, no test statistic, no p-values.

**Changes in v3**, all owner-raised:
(i) §2 now says the labels are **ranks**, not identities — move a speed and the labels move with
it, so `r1` means the slowest, whoever that now is;
(ii) **§7a** is new: how far the reference reaches. For the AP of step `d` the answer is exact —
the eighth runner may sit anywhere in `8d ± (n−2)d/(n−1)` and the reference still holds the other
seven;
(iii) **§7b** is new: the mixed reading — AP for the lower runners, grid for the higher — with the
worked configuration;
(iv) §8 had the **carrier** back in it (register item 7: "which constraint is tight at the
moment"). The sentence naming which runner grants the moment is struck. The opening itself and
the lap count `k` are kept, both being Step 5 objects.

**Register.** Nothing here uses measure, density, covering, a complement, a witness, a carrier,
set emptiness, a jump chain, blocking, primes, a stationary first runner, slots, Weyl, LRC at any
other order, or Prop 4.1 of the φ(n) paper. See the handover of 2026-09-13 §6.

---

## §1 The state is the gap vector  `[PROVED]`

At every instant the eight runners cut the circle into eight cyclic gaps `g_1,…,g_8 ≥ 0` with

    SUM_k g_k = 1.

The state is the gap vector, and the sum is conserved because the circle has circumference 1.

## §2 Adjacency is adjacency mod n, and loneliness is local on the state  `[PROVED]`

**Definition.** The label is the **rank in speed order**, not an identity: `r1` is the slowest,
`r8` the fastest, and if a runner's speed changes the labels re-sort with it. Two runners are
adjacent when they are one step apart **mod `n`** in that order. The speed line
has a least and a greatest element; mod `n` there is no first and no last. In the AP,
`v_8 − v_1 = 7 ≡ −1 (mod 8)`, so r1 and r8 are one step apart exactly as r3 and r4 are. At the
reference instant the eight stand on the eight eighths via `k ↦ kr (mod 8)`, and `8 ≡ 0`, so r8 is
at `0` and r1 at `1/8` — adjacent on the track with nothing between them.

> **Runner `i` is lonely at `t` iff both gaps flanking its junction are `≥ 1/8`.**

*Proof.* The nearest other runner is a cyclic neighbour, so `min_{j≠i} ‖(v_i − v_j)t‖` is the
smaller of the two flanking gaps. Seven conditions collapse to two. ∎

*Mechanical support for the definition.* Driving each runner in turn across the entire pack,
the locality rule of §9 fails on exactly 19 of 1,376 configurations if adjacency is read on the
speed line, and every one of the 19 is r1 dropping below 1 and disturbing r8. Read mod `n`, the
failures are zero. The cyclic reading is what the arithmetic requires.

## §3 Counting on the state  `[PROVED]`

With `A(t) = { k : g_k(t) ≥ 1/8 }` and `c(A)` the number of cyclic runs of `A`,

    #lonely(t)  =  |A(t)|  −  c(A(t)),        #lonely(t)  >=  max(8 − 2b, 0),   b = 8 − |A|.

Source: `GAP_FRAME_v1` §1, with `[VERIFIED — 180,000/180,000]` on the identity.

## §4 The reference  `[PROVED]`

`|A| = 8` means every gap is `≥ 1/8`; eight such numbers summing to 1 are each exactly `1/8`. So
global isolation is the uniform 8-grid and nothing else. The instants are `{δt} = r/n` with
`gcd(r,n) = 1`, and there are `φ(n)` of them.

*Debt.* The instants and the count are `lrc_ap_phi_n_law_v1` Theorem 3.1(a)–(b) — the owner's own
prior work, and the construction's only external debt. The forcing step is formalised:
`Construction8.gaps_all_eq`.

## §5 Location and time  `[PROVED]`

The two neighbours give `m = d_min`, exact and local; sortedness cannot be deviated away, and
nothing happens before `t = 1/(8m)`. That fixes one window, `u ∈ [1/8, 7/8]` in the lap
coordinate `u = m·t`. Then:

| | |
|---|---|
| **location** | `u* = m·t*` — the fraction of one lap against the nearest neighbour at which the loneliness sits |
| **time** | `t* = u*/m`, or `t*·v_1` revolutions of the slowest runner |

`u* = 1/8` at the reference. **A permutation moves the location**; `m` fixes the scale, and the
scale converts location into time. The remaining speeds enter only through where inside
`[1/8, 7/8]` the location sits — never through the scale.

*Worked.* Base AP, r2 moved to `2.456`. Its neighbours are 1 and 3, gaps `182/125` and `68/125`,
so `m = 68/125`.

| runner | `m` | location `u*` | time `t*` | revolutions of slowest |
|---|---|---|---|---|
| 1 | 182/125 | 1/8 | 125/1456 | 0.086 |
| **2.456** | 68/125 | **153/886** | 1125/3544 | 0.317 |
| 3 | 68/125 | **153/1000** | 9/32 | 0.281 |
| 4…8 | 1 | 1/8 | 1/8 | 0.125 |

r2 and r3 share the closed gap and both locations move off `1/8`. r1 keeps its location at `1/8`
and improves in *time*, because its `m` grew when r2 moved away. Five are untouched — the
`DISTURBANCE_RULE_v1` §2 row for "r2 up" exactly.

*Contrast.* For `r1 = 2 − ε` the location stays at `1/8` for `ε = 1/10, 1/100, 1/1000` while the
time reads `2.4`, `24.9`, `249.9` revolutions of the slowest. Same place, three conversions. That
is the scale working, not the location moving.

Formalised: `Construction8.nearest_below`, `nearest_above`, `before_floor`.

## §6 Inside the window everything is read off  `[PROVED]`

At `u`, runner `j` has completed `⌊s_j u⌋` laps relative to `i` and sits at phase `s_j u mod 1`,
with `s_j = d_j/m`. It is clear of `i` when that phase lies in `[1/8, 7/8]`. Positions and lap
counts are read, not searched for. All **six** others must be read — `d_min` comes from the
nearer neighbour, and the second neighbour is read like everyone else.

## §7 What a deviation does to the reference  `[PROVED]`

Writing `V = A + e` against an arithmetic progression of common difference `d`, at
`t = r/(nd)` with `gcd(r,n) = 1`: the AP part puts the `n` runners on the `n` distinct eighths,
one each, for every runner at once; the deviation moves runner `k` by exactly `e_k·r/d` eighths;
and the instant survives iff every displacement is a whole number of eighths **and**
`k ↦ kr + e_k r/d (mod n)` is a bijection. `[VERIFIED — 12,135/12,135]`

Formalised: `Construction8.displacement`.

## §7a How far the reference reaches  `[PROVED]`

Hold seven runners on the AP of step `d` and let the eighth vary above them.

> **The reference holds the other seven exactly while the eighth lies in
> `8d ± (n−2)d/(n−1)`** — at `n = 8, d = 1`, the interval `[50/7, 62/7]`, that is `8 ± 6/7`.

*Proof.* Both ends are set by the eighth runner's two neighbours, and both by the last spine
point `p = 7`.
**Lower.** r7 is the neighbour below; its odd difference is `x − 7d`, and it keeps an instant iff
`dist((x − 7d)p/d, 8ℤ) ≥ 1` for some `p ∈ {1,3,5,7}`. The largest `p` is the binding one, giving
`x ≥ 7d + d/7`.
**Upper.** r1 is the neighbour **through the wrap**; its odd difference is `x − d`, and `p = 7`
again gives the last surviving instant, at `7(x − d)/d ≤ 8·7 − 1`, so `x ≤ d + 55d/7`. ∎

Confirmed by a sweep at denominator 1400: the measured endpoints are `50/7` and `62/7` exactly.

Two things follow, and they are the two halves of "a rule for a larger AP".

**Dilates are free.** Scaling every speed by `λ` rescales time by `1/λ` and is an exact symmetry,
so the interval for step `d` is `d` times the interval for step 1. Measured: AP step 2 gives
`[93/7, 117/7]`, width `3.430 = 2 × 1.715`. Nothing to prove beyond the symmetry.

**Irregular bases are the hard half.** `[VERIFIED]` With the reference at the base's gcd:

| base | gcd | window for the eighth runner |
|---|---|---|
| `1,…,7` — the AP | 1 | `[50/7, 62/7]`, width 1.716 |
| `1,2,3,4,5,6,8` — one gap doubled | 1 | `[57/7, 69/7]`, width 1.432 |
| `1,3,5,…,13` — AP step 2 | 2 | `[93/7, 117/7]`, width 3.430 |
| `1,2,3,4,5,7,9` — two gaps doubled | 1 | **empty** |
| `1,2,4,8,16,32,64` | 1 | **empty** |
| `10,65,101,126,159,222,256` | 1 | **empty** |

The window survives a single doubled gap, narrowing and shifting up. It is gone by two. **Whether
an enlarged step restores a window on an irregular base is open** — it is the rule this sketch
does not have.

## §7b The mixed reading — AP for the lower, grid for the higher  `[VERIFIED]`

Each runner is tried at the four instants of its own scale, `u = p/8` and `t = p/(8·d_min)`,
`p ∈ {1,3,5,7}`. Worked on `V = (10, 65, 101, 126, 159, 222, 256, 271)`:

| rank | speed | `d_min` | p | location `u` | time `t` |
|---|---|---|---|---|---|
| r1 | 10 | 55 | 1 | 1/8 | 1/440 |
| r2 | 65 | 36 | 1 | 1/8 | 1/288 |
| r3 | 101 | 25 | 1 | 1/8 | 1/200 |
| r4 | 126 | 25 | 1 | 1/8 | 1/200 |
| r5 | 159 | 33 | 1 | 1/8 | 1/264 |
| r6 | 222 | 34 | 1 | 1/8 | 1/272 |
| **r7** | 256 | **15** | **3** | **3/8** | **1/40** |
| **r8** | 271 | **15** | **3** | **3/8** | **1/40** |

All eight, no search. The lower six take the first instant; the tight pair at `d_min = 15` misses
it and takes the third.

**Why the other three instants are available at all.** By §5 of `LRC8_ANALYTIC_v2`, the four
points succeed or fail *together* exactly when `s = d/d_min` is integral. For r7 and r8 it is not
— `s = 82/5, 191/15, 31/3, 26/3, 97/15, 34/15, 1` — so the four separate and `p = 3` is a
genuinely different test from `p = 1`. That is the mechanism behind "grid for the higher": the
gcd's step is always the all-or-nothing one, and a larger step taken from the configuration's own
gaps is where the four points come apart.

**Reach.** Over 20,000 runner-instances per row, the four points name a location and a time for:

| speeds in | p=1 | p=3 | p=5 | p=7 | none of the four |
|---|---|---|---|---|---|
| [0,120) | 51.8% | 10.8% | 7.2% | 4.9% | 25.3% |
| [0,1200) | 46.8% | 10.6% | 8.2% | 6.8% | 27.6% |
| [0,5000) | 45.4% | 10.1% | 8.3% | 6.4% | 29.7% |

About 72% of runners named outright, and all eight named in roughly 8% of configurations — the
worked one above is in that 8%. The runners the four points do not name still have moments; what
they lack is a moment the reading hands over without searching.

## §7c The cascade, and how far the step can be enlarged

Three tiers, tried in order for each runner. `g` is the gcd of all differences; `d_min(i)` the
runner's nearest difference; the candidate instants are always `t = p/(8D)`, `p ∈ {1,3,5,7}`.

| tier | step `D` | |
|---|---|---|
| **AP** | `g` | the gcd's own lattice — all four instants stand or fall together (§5, integral `s`) |
| **grid** | `d_min(i)` | the runner's own scale — the four instants separate when `s = d/d_min` is non-integral |
| **enlarged** | some `D` beyond those | step up until the lattice is usable |

### The ceiling  `[PROVED]`

> **No step above `7·d_min(i)` can ever clear runner `i`.**

*Proof.* Write the condition in integers: `‖x/(8D)‖ ≥ 1/8` iff `D ≤ (x mod 8D) ≤ 7D`. Take the
nearest difference, `d_min(i)`. If `D > 7·d_min(i)` then for every `p ∈ {1,3,5,7}` we have
`p·d_min(i) ≤ 7·d_min(i) < D`, so that residue falls below the band and the `p` fails. All four
fail. ∎

`[VERIFIED — 32,000 runner-instances]` no clearing step above `7·d_min`, and the ratio
`(largest clearing D)/d_min` attains 7 exactly. So the admissible steps are the finite range
`1 ≤ D ≤ 7·d_min(i)` and a sweep over them is **exhaustive, not truncated**.

The constant is the same 7 as in `d_max ≤ 7·d_min`, and for the same reason: the nearest
difference has to survive `p ≤ 7`.

### Which step clears — a closed form  `[PROVED]`

A lattice `D` is **dead** for runner `i` if some difference is divisible by `8D`, so no `p` can
move it off zero. Since `8D | d` iff `8 | d` **and** `D | d/8`:

    M(i)    = { d_j/8  :  8 | d_j }            the eighth-parts of the differences that lie on a lap line
    Dead(i) = the divisors of the elements of M(i)
    L_0(i)  = min ( positive integers not in Dead(i) )      the first live lattice

Nothing outside `Dead(i)` is dead and every divisor of an element of `M(i)` is, so the dead
lattices are exactly a divisor-closed set. `[VERIFIED — 32,000/32,000]` this closed form agrees
with a direct search in every case.

Two bounds follow:

- `L_0(i) ≤` **the smallest prime dividing no element of `M(i)`** — a prime is dead only if it
  divides one of them.
- `D ≤ 7·d_min(i)`, the ceiling above.

`M(i)` is deliberately left unnamed here.

*This is the mechanism `WHY_IT_PREDICTS_v1` §2 states in words — "the dead lattices are a divisor
set, the `L` dividing some `s_j/8`" — with the closed form and the two bounds attached.*

### What the cascade does  `[VERIFIED — descriptive]`

12,000 runner-instances per row, 1,500 random integer 8-sets each, exact integer arithmetic:

| speeds drawn from | AP | grid | enlarged | nothing clears |
|---|---|---|---|---|
| [0, 10³) | 39.5% | 41.8% | 18.5% | **0.17%** |
| [0, 10⁵) | 40.1% | 41.0% | 18.9% | 0.00% |
| [0, 10⁷) | 39.8% | 42.4% | 17.9% | 0.00% |

The clearing step is **small and scale-free** — `D` runs `2, 3, 4, 5, 7, 6, 8, 9` in that order in
every row while `d_min` grows with the span — and it **is** `L_0(i)` in **78.6%** of the enlarged
cases, within 2 of it in 91%. That is the answer to why the step is enlarged at all: not to match
a spatial scale, but to step past divisibility, and divisibility by `8D` becomes rare as soon as
`D > 1` however large the speeds are.

### Where it fails  `[VERIFIED — exact, one exhibited case]`

```
V = [27, 45, 308, 678, 679, 799, 806, 979]      runner r4 = 678
differences  1, 121, 128, 301, 370, 633, 651
```

`128 = 2⁷`, so `M = {16}`, `Dead = {1, 2, 4, 8, 16}` and `L_0 = 3`. But `d_min = 1`, so the ceiling
is `7`. The admissible live steps are `{3, 5, 6, 7}` and all four fail the band. Nothing clears r4
on this grid.

**The two conditions are nameable and they must both hold**: a difference that is a high power of
2, which makes `Dead` eat the bottom of the range; together with a small `d_min`, which caps the
range before you can step past it. That is why the failures concentrate at small span — a large
span makes `d_min = 1` rare and the ceiling generous.

r4 *is* lonely, first at `t = 305/2408`, which is not `p/(8D)` for any admissible `D`. So this is
a statement about the `p/(8D)` grid, not about loneliness.

## §7d The three regimes, and one lemma for two of them

**1. AP.** Perfect isolation at the `φ(8)` instants, every cycle, all eight at once (§4).

**2. Rational displacement.** The configuration returns: every runner is home simultaneously after
one cycle of the slowest, the pattern repeats, and the lap count of §8 counts the rungs inside one
period.

**3. Irrational displacement.** No return, ever. The runner is lonely anyway, and §7d's lemma says
where.

### The window-widening lemma  `[PROVED, given nonemptiness]`

> Let `m = d_min(i)` and suppose the runner's other six differences are all integer multiples of
> some `h`. Their joint good set is then `(1/h)`-periodic. Runner `i`'s window
> `[1/(8m), 7/(8m)]` has length `3/(4m)`, so it contains a **full period** whenever
>
>     3/(4m)  >=  1/h        i.e.       m  <=  3h/4
>
> and a nonempty periodic set meets every interval of at least one period. So `i` is lonely,
> inside its own first window.

*The lemma has two triggers, and they are the same inequality read from opposite ends.*

| trigger | how `m ≤ 3h/4` is met | where it appears |
|---|---|---|
| **a common factor** | `h` large — the differences share a divisor | `LRC8_ANALYTIC_v2` §6b, the `gcd ≥ 2` case |
| **a near-collision** | `m` small — two speeds are close | this section |

So the `gcd ≥ 2` theorem and the near-collision case are not two results. They are one lemma, and
what differs is which side of `m ≤ 3h/4` does the work.

**Debt.** Nonemptiness of the other six constraints' good set is LRC(7) — the same outside debt
`LRC8_ANALYTIC_v2` §6b carries, and it is not discharged here. In a given configuration it can be
exhibited directly instead, as below.

`[VERIFIED — 3,000/3,000]` runners with `d_min ≤ 0.7` and six integer differences: a lonely
instant inside the window in every case.

### Worked: a near-collision at an irrational gap  `[VERIFIED — exact]`

Speeds `(1, 1+δ, 3, 4, 5, 6, 7, 8)` with `δ = √2/100`. The forced bound is
`1/(8δ) = 8.838834…`, itself irrational.

| runner | its six other differences | first isolation |
|---|---|---|
| **r1**, speed 1 | `2,3,4,5,6,7` — **integers, the pack intact** | **`71/8 = 8.875`** |
| **r2**, speed `1+δ` | `2−δ, …, 7−δ` — **all irrational** | `8.892966505…`, denominator 61 digits |
| r3 … r8 | integers | `1/8` — untouched |

r1 is the lemma: `h = 1`, `m = δ`, so the window has length `3/(4δ) ≈ 53` — fifty-three full
periods of the integer part — and the first of its spine instants past the irrational bound is
`8 + 7/8`. The irrational gap does not break the isolation; it fixes which rung of the intact
pack's ladder the runner arrives on. Checked at 60-digit precision: at `71/8` the seven distances
are `0.12551, 0.25, 0.375, 0.5, 0.375, 0.25, 0.125` — the last two at the threshold exactly.

r2 is the case the lemma does **not** reach: every one of its differences is irrational, so no
sub-pack survives to supply a period, and its moment is at no `p/(8D)` at all. It is read directly
off the lap lines, with no periodicity used anywhere.

And r3 … r8 sit at `1/8` throughout, which is §9: the displacement disturbs the mover and its
neighbour and nobody else.

## §8 The phase never varies  `[PROVED]`

> The first instant of loneliness is always `t* = (8k+1)/(8d)` — an **opening** — for one of the
> runner's own differences `d` and some integer `k ≥ 0`. It is never a closing `(8k+7)/(8d)`.

*Proof.* For a single difference `d`, the instants at which that runner is clear of `i` are the
closed intervals `[(8k+1)/(8d), (8k+7)/(8d)]`. The instants at which `i` is lonely are the
intersection over its differences — a closed set, and on any bounded range a finite union of
closed intervals. The left endpoint of each component is the largest of the left endpoints of the
constituent intervals meeting there, hence of the form `(8k+1)/(8d)`. An isolated point of the
set is a degenerate component and its left endpoint is the point itself. `t*` is the left endpoint
of the first component. ∎

`[VERIFIED — 12,672/12,672]` over the full single-mover sweep, both directions, exact rationals.

So loneliness always arrives at exactly `1/8` of a relative lap past a coincidence — an opening,
never a closing. The free quantity left is the lap count `k`, which is a Step 5 object.

*(An earlier draft added "and which runner grants it". That is the carrier, register item 7, and
it is struck. The construction never asks which constraint was last to clear.)*

## §9 A permutation disturbs only locally  `[VERIFIED — 1,376/1,376]`

> Moving one runner disturbs only `{mover} ∪ {the pair that closes up where it left} ∪ {the pair
> it now sits between}`.

Through crossings, at any distance. Sizes observed: 0 (8 configurations — the mover lands on a
grid point), 2 (304), 3 (874), 4 (190). When the mover does not cross, the two pairs coincide,
the bound collapses to three names and the observed size is two — `DISTURBANCE_RULE_v1` §1, whose
scope note lists the crossing case as untested by construction.

**Not proved.** Scope: AP base, one mover, driven across the whole pack.

## §10 The joint  `[CLAIMED]`

> Every grant falls on lap 0 of the nearest neighbour — the location lies in the first window.

`[VERIFIED — 21,600 runner-instances across seven populations; every integer arrangement with
0 = v_1 < … < v_8 ≤ 20 and gcd 1, 77,400 arrangements and 113,145 distinct profiles; and 2,432
runner-instances of the single-mover sweep, all at lap 0]`

§8 changes what this has to say. With the phase fixed, the only free quantities are the granting
difference `d` and the lap `k`, so the joint is **`k = 0`** — a statement about one integer.

**A route that does not close it.** Arguing "the reference has `k = 0`, and every permutation
preserves it" is logically the same statement re-indexed by move: if some arrangement had no
moment, a path from the reference would have a *first* move breaking the invariant. §9 is the
locality any mechanism gets to use; it cannot be the mechanism. Recorded in the handover of
2026-09-12 §5 and repeated here because it is the trap this sketch's shape invites.

**What to work up first.** §8 refines to *which* runner grants. `PREDICTION_SPREAD_GRID_v1` §4
separates the two neighbour notions — nearest in speed sets the scale, nearest in residue decides
whether the reference instant is available. If the granting runner is determined by the residue
neighbour, `k = 0` follows from §5 fixing the window and the grant lying inside it.

---

## Ledger

| | |
|---|---|
| §1 conservation | `[PROVED]` |
| §2 adjacency mod `n`; the two-gap criterion | `[PROVED]` |
| §3 run identity and the deficiency bound | `[PROVED]` |
| §4 the reference | `[PROVED]` — owes `lrc_ap_phi_n_law_v1` Thm 3.1(a)(b) for the instants and the count |
| §5 location, time, and the scale | `[PROVED]` |
| §6 the reading, all six others | `[PROVED]` |
| §7 displacement in eighths; survival condition | `[PROVED]` |
| §7a the reference's reach, `8d ± (n−2)d/(n−1)`; dilates free by scaling | `[PROVED]` |
| §7a a window on an irregular base under an enlarged step | **`[OPEN]`** |
| §7b the mixed reading; ~72% of runners named, ~8% of configurations closed | `[VERIFIED]` |
| §7c the ceiling `D ≤ 7·d_min(i)` | `[PROVED]`, `[VERIFIED — 32,000]`, attained |
| §7c the closed form `L_0 = min(ℤ⁺ \ Dead)`, `Dead` = divisors of `M(i)`; the prime bound | `[PROVED]`, `[VERIFIED — 32,000/32,000]` |
| §7c cascade rates; `D = L_0` in 78.6% | `[VERIFIED — descriptive]`, `PREREG_DSWEEP_v1` §2.3 only |
| §7c a configuration no admissible step clears | `[VERIFIED — exact]`, one case exhibited |
| §7d window-widening; the gcd case and the near-collision case are one lemma | `[PROVED, given nonemptiness]` — **owes LRC(7)** for that half |
| §7d the lemma's reach | `[VERIFIED — 3,000/3,000]` |
| §7d the irrational worked case, r1 at `71/8` and r2 off the grid | `[VERIFIED — exact, 60-digit]` |
| §8 the phase never varies | `[PROVED]`, `[VERIFIED — 12,672/12,672]` |
| §9 locality of a permutation through crossings | **`[VERIFIED — 1,376/1,376]`**, not proved |
| §10 the joint, `k = 0` | **`[CLAIMED]`** |
| LRC(8) | **not proved by this document** |

**Lean.** `LonelyRunner/LRC/Construction8/Parts.lean` — `gaps_all_eq` (§4), `nearest_below`,
`nearest_above`, `before_floor` (§5), `displacement` (§7). Zero `sorry`, no `native_decide`, all
five `[propext, Classical.choice, Quot.sound]`. All stated at general `n`.

**Owed.** `NEIGHBOUR_INTERVAL_v1` §1 step 3, "verify the other five" → six (see §6). Not yet made,
pending the owner's call on whether it goes in place or into a `v2`.

**Corrected elsewhere by this session.** The attainment rate for disturbed runners is a step-size
artefact, not a constant near one half: 0.4641, 0.4135, 0.3800, 0.3735 at steps 1/10, 1/100,
1/1000, 1/10000 over the single-mover sweep. The figures in `SCALE_RULE_v1` §3, §6,
`TWO_MOVER_PREDICTION_v1` §4, §6 and `RANDOM_PREDICTION_v1` §2, §5 are the two coarsest points of
that curve, and the cause is the small-denominator bias the handover of 2026-09-12 §2 item 12
already records.

**Scope.** n = 8. §§1, 2, 3, 5, 6 use `n` only through the threshold `1/n` and the gap count.
§§4, 7, 8 are written with 8. §9 is the AP base with one mover.

**n = 8 is not proved by this document.**
