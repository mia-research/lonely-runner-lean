# LRC(8) — proof sketch (v3)

2026-09-13. n = 8, circle of circumference 1, eight runners starting together at distinct
constant speeds, threshold 1/8. T. Palelei's construction.

**What this is.** The spine of the argument, from scratch, in the construction's three objects —
**gaps**, **`d_min`**, **laps** — with each step labelled by what supplies it and the one open
joint marked. It is a sketch, not the candidate; `PROOF_CANDIDATE_v3.md` remains canonical for
the written-out proofs.

**v1** was a conversational draft; **v2** put adjacency mod `n` into §2 as the definition and
separated location from time in §5. **Changes in v3**, all owner-raised:
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
