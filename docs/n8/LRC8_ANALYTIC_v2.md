# LRC(8) reduced to one lemma about six real numbers

2026-09-13. Analytical write-up of the predictor line. n = 8, individual isolation,
threshold 1/8.

**What this document is.** A complete, self-contained reduction of the Lonely Runner Conjecture
at n = 8 to a single statement about six real numbers on one interval. Every step of the
reduction is proved here for arbitrary distinct real speeds. **The final lemma is open.** The
reduction does not lower the difficulty of n = 8; it relocates all of it into one compact
statement and disposes of everything around it.

**Grades.** `[PROVED]` = argument given here, all distinct real speeds. `[OPEN]` = not proved.
`[VERIFIED — k]` = k instances, no exception, not a proof. Nothing is graded above what its own
argument earns.

---

## 0. Statement and setting

Eight runners start together on a circle of circumference 1 and run at distinct constant speeds
`v_1 < v_2 < … < v_8`. Runner `i` is **lonely** at time `t` if every other runner is at circle
distance at least `1/8` from it. Write `‖x‖` for the distance from `x` to the nearest integer.

Runner `i` is lonely at `t` iff

    ‖ d_j · t ‖  ≥  1/8     for all seven  d_j = |v_i − v_j|,  j ≠ i.        (∗)

**LRC(8).** For every such configuration and every `i`, there exists `t > 0` satisfying (∗).

Isolation depends only on differences, so adding a constant to every speed changes nothing, and
scaling every speed by `k > 0` rescales time by `1/k`. Both are exact symmetries and are used
without further comment. `[PROVED]`

---

## 1. Loneliness is a two-neighbour condition  `[PROVED]`

At any instant the eight runners occupy eight positions on the circle, cutting it into eight
cyclic gaps that sum to 1. The nearest other runner to `i` is one of its two cyclic neighbours.

> **Lemma 1.** Runner `i` is lonely at `t` iff both cyclic gaps adjacent to it are `≥ 1/8`.

*Proof.* `min_{j≠i} ‖(v_i − v_j)t‖` is the circle distance to the nearest other runner, which is
attained at a cyclic neighbour. ∎

**There are no end runners.** The speed line has a least and a greatest element; the track does
not. At `t = 1/8` in the arithmetic progression `(1,…,8)` the positions are
`0, 1/8, 1/4, 3/8, 1/2, 5/8, 3/4, 7/8` in the cyclic order `r8 r1 r2 r3 r4 r5 r6 r7`, so r1's two
neighbours are **r8 and r2**, each at exactly `1/8`. Every runner has two neighbours, always.

---

## 2. The reference arrangements  `[PROVED — prior work]`

A **grid** is a configuration whose reduced differences `(v_i − v_1)/g`, with `g` the gcd of all
differences, form a complete residue system mod 8. The arithmetic progression is the grid with all
deviations zero.

> **Lemma 2 (the φ(n) law).** A grid is globally isolated — all eight runners lonely at once — at
> exactly `φ(8) = 4` instants, `t = p/(8g)` with `gcd(p, 8) = 1`.

By Lemma 1 this is forced from the other side too: all eight lonely requires all eight gaps `≥ 1/8`
with total 1, hence **all eight gaps exactly `1/8`** — perfect equidistribution, and nothing else.
Equidistance is a property of grids, not of the AP specifically; the AP is its simplest form.

**Gridness cannot be manufactured.** Under `V ↦ a + kV` the reduced difference vector
`(v_i − v_1)/g` is unchanged — the translation cancels in differences, and the dilation multiplies
numerator and `g` alike. So the residues mod 8 are an invariant of the affine orbit, and a
non-grid is a non-grid permanently. `(1,2,3,4,5,6,7,9)` reduces to `(0,1,2,3,4,5,6,8)`, residues
`[0,1,2,3,4,5,6,0]`, and no affine map repairs the repeat. `[PROVED; 20,000/20,000 checked]`

Grids are 0.32% of random 8-subsets of `[0,100)`. **They are the reference frame, not the
generic case**, and the reduction below never assumes one.

---

## 3. Every runner carries its own scale  `[PROVED]`

> **Lemma 3.** Let `m_i = min(v_i − v_{i−1}, v_{i+1} − v_i)` (one-sided at `i = 1, 8`). Then
> `m_i = min_{j≠i} |v_i − v_j|`, and runner `i` is not lonely for any `t < 1/(8 m_i)`.

*Proof.* The speeds are sorted, so the nearest speed to `v_i` is an adjacent one; that gives the
first claim, from two numbers, with no reference to the rest of the configuration. For
`t < 1/(8 m_i)` we have `m_i t < 1/8`, so `‖m_i t‖ = m_i t < 1/8` and (∗) fails. ∎

This holds under **any** deviation from AP or grid: sortedness cannot be removed, so `m_i` cannot
be taken away. It is the quantity that survives leaving the reference frame.

---

## 4. Reduction to one relative revolution  `[PROVED]`

Fix a runner and write `m = m_i`. Put

    u = m·t,        s_j = d_j / m        so that  min_j s_j = 1.

Then (∗) becomes `‖s_j u‖ ≥ 1/8` for all `j`, with one of the `s_j` equal to 1. The constraint
from that `s_j = 1` confines `u` to `[1/8, 7/8] (mod 1)` — **one relative revolution against the
nearest-in-speed runner.**

> **Lemma 4 (reduction).** LRC(8) for runner `i` is equivalent to: there is
> `u ∈ [1/8, 7/8] + ℤ` with `‖s_j u‖ ≥ 1/8` for the six remaining `s_j ≥ 1`.

*Proof.* Immediate from the substitution; `m > 0` so `t ↦ u` is an increasing bijection. ∎

All configuration-level structure — AP, grid, residues, gaps, span — has now been absorbed into
the six numbers `s_2, …, s_7`. Nothing about eight runners remains.

---

## 5. The witness on the spine  `[PROVED]`

> **Lemma 5.** Let `u = p/8` with `gcd(p, 8) = 1`. Then `‖s_j u‖ ≥ 1/8` holds for every `s_j`
> with `dist(s_j p, 8ℤ) ≥ 1`.

*Proof.* `‖s_j p/8‖ ≥ 1/8` iff `dist(s_j p / 8, ℤ) ≥ 1/8` iff `dist(s_j p, 8ℤ) ≥ 1`. ∎

**Consequence for integers.** If every `s_j` is an integer — which holds whenever `m` divides
every difference, in particular for every grid with `m = g` — then `dist(s_j p, 8ℤ) ≥ 1` fails
only when `8 │ s_j p`, and since `gcd(p,8) = 1`, only when `8 │ s_j`. So for integer `s`:

> the four spine points `1/8, 3/8, 5/8, 7/8` **succeed together or fail together**, and they
> succeed iff no `s_j` is a multiple of 8.

That is Lemma 2 recovered from the normalised side, and it is why grid isolation is simultaneous:
a grid's residues are distinct, so no `s_j ≡ 0`, so `u = 1/8` works for every runner at once. For
non-integer `s` the four spine points are independent — `s = 8.5` fails at `u = 1/8`
(`dist(8.5, 8ℤ) = 0.5`) and succeeds at `u = 3/8` (`dist(25.5, 8ℤ) = 1.5`).

**Scope of what §5 settles.** Every configuration in which no `s_j` lies within 1 of a multiple
of 8. This includes every grid, every dilate of one, and — with no arithmetic hypothesis at all —
every runner whose largest `s_j` is at most 7, since the first multiple of 8 needing avoidance is
8 itself. `[VERIFIED — 9,810/9,810 for the `s_max ≤ 7` form; 485/485 for grids]`

---

## 6. The one open lemma

> **Lemma 6 (first interval).** `[OPEN]`
> For any six reals `s_2, …, s_7 ≥ 1`, there exists `u ∈ [1/8, 7/8]` with `‖s_j u‖ ≥ 1/8`
> for every `j`.

> **Theorem.** Lemma 6 implies LRC(8). `[PROVED, given Lemma 6]`
>
> *Proof.* Fix any configuration and any runner. By Lemma 3, `m > 0` exists and is exact. By
> Lemma 4 the problem becomes exactly the statement of Lemma 6 in `u`. A witness `u` pulls back
> to `t = u/m > 0`, at which (∗) holds. ∎

Lemma 6 is LRC(8) for a single runner **together with a localisation**: it asks not merely that a
witness exist, but that one exist inside the first relative revolution. It is therefore strictly
stronger than what LRC(8) needs, and it is stated with no arithmetic, no distinctness and no
configuration structure — six arbitrary reals `≥ 1`.

**§5 proves the case where some spine point survives.** What remains is to construct a witness
when every `p/8` is excluded, i.e. when some `s_j` lies within 1 of a multiple of 8 for each of
`p = 1, 3, 5, 7`.

### Evidence for Lemma 6, and what it is not

| population | runner-instances | witness in the first interval |
|---|---|---|
| random integer 8-sets `[1,80)` | 9,600 | 9,600 |
| wide spans `[1,400)` | 2,000 | 2,000 |
| near-collision pairs | 2,000 | 2,000 |
| clustered (two tight groups) | 2,000 | 2,000 |
| one far outlier (200–900) | 2,000 | 2,000 |
| rationals, denominators ≤ 29 | 2,000 | 2,000 |
| all speeds `≡ ±1 mod 8` | 2,000 | 2,000 |
| **total** | **21,600** | **21,600** |

Position of the witness, over 4,800 instances: `u` has median `0.1250` (the spine point itself),
90th percentile `0.1731`, and **maximum `0.4464`** — against an interval ending at `0.875`. The
extreme instance is `(4,5,6,9,12,13,16,17)`, runner r5, `s = {1,3,4,5,6,7,8}`, `u = 25/56`, which
sits on the boundary of the `s = 7` constraint (`7 × 25/56 = 25/8`, `‖25/8‖ = 1/8` exactly).

**This is evidence, not a proof, and the gap is not small in kind**: no finite sweep can
establish a statement quantified over six arbitrary reals.

---

## 6a. The modulus law — the problem is residue arithmetic  `[PROVED for rational s]`

> **Lemma 7.** For `u = p/q` in lowest terms,
> `‖s·p/q‖ ≥ 1/8  ⟺  dist(sp mod q, 0) ≥ q/8`.
> For rational `s` the good set is a finite union of closed intervals with rational
> endpoints, so it contains a rational whenever it is nonempty. Hence a witness exists
> **iff** there are `q` and `p` with every `s_j·p mod q` in `[q/8, 7q/8]`.

*Proof.* `‖s p/q‖ = (1/q)·dist(sp, qℤ)`. The endpoints of the good set are the solutions of
`‖s_j u‖ = 1/8`, rational when `s_j` is. ∎  (Verified: 0 disagreements with the real test in 3,000.)

`q = 8` is exactly the spine of §5 — band radius 1, condition `s_j p ≢ 0 mod 8`. Since `s₁ = 1`
is always present, `p` itself must lie in the band, which places `u = p/q` in `[1/8, 7/8]`
automatically. So Lemma 6 restated: **find a modulus and a multiplier that put every `s_j` in
the band.** No intervals, no covering, no measure — residues on `ℤ/q`.

**How large must `q` be?** `[VERIFIED — 100,000; no proof]`

| population | `q ≤ 16` | `q > 16` | largest `q` needed |
|---|---|---|---|
| true runner `s` | 39,878 | 122 | **23** |
| random `s ≤ 500` | 39,813 | 187 | **25** |
| `s_j ≡ 0 mod 8` | 19,243 | 757 | **29** |

An earlier reading of a 3,277-case sample as `q ≤ 2n = 16` was **wrong** and is retracted here:
about 0.5% of cases need `q > 16`. No bound on `q` is proved, and "some `q` exists" is Lemma 6
again — the modulus law is an exact translation into arithmetic, and becomes a new theorem only
with a bound on `q`.

---

## 6b. Where n = 8 actually lives  `[PROVED]`

Strip §4 to its bones. After normalisation the constraint from `s₁ = 1` **is nothing but the
window**: `‖u‖ ≥ 1/8` says `u ∈ [1/8, 7/8] (mod 1)`. So Lemma 6 reads:

> find `u` in a window of length `3/4`, satisfying **six** constraints `‖s_j u‖ ≥ 1/8`.

And six constraints at threshold `1/8` are implied by **LRC(7)**, which gives six constraints at
`1/7 > 1/8`, and which this programme owns — axiom-clean in Lean, `#print axioms intLRC_seven`
= `[propext, Classical.choice, Quot.sound]`.

> **The entire content of n = 8, in this frame, is that the window has length `3/4` of a period
> and not `1`.** With a full period, LRC(7) plus periodicity would close it outright.

This is the precise form of the standing observation that *existence ≠ localisation*. It is now
quantified: the deficit is `1/4` of a period.

### Theorem (the gcd case)  `[PROVED — from LRC(7)]`

> Let `s₁ = 1` and let `s_2, …, s_7` be positive integers with `gcd(s_2, …, s_7) = c ≥ 2`.
> Then Lemma 6 holds for this `s`.

*Proof.* Put `w_j = s_j/c ∈ ℤ⁺` and `v = c·u`, so `‖s_j u‖ = ‖w_j v‖`. The window
`u ∈ [1/8, 7/8]` becomes `v ∈ [c/8, 7c/8]`, of length `3c/4 ≥ 3/2 > 1`.

Let `G = { v : ‖w_j v‖ ≥ 1/8 for all j }`. The `w_j` are integers, so `G` is **1-periodic**.
Let `k ≤ 6` be the number of distinct values among the `w_j`; duplicates are duplicate
constraints. LRC(`k+1`) — proved for every `k+1 ≤ 7`, and axiom-clean in Lean for `k+1 ≤ 7` —
gives `v₀` with `‖w_j v₀‖ ≥ 1/(k+1) ≥ 1/7 > 1/8`. So `G ≠ ∅`.

A nonempty 1-periodic set meets every interval of length `≥ 1`. Hence `G ∩ [c/8, 7c/8] ≠ ∅`;
take `v` there and set `u = v/c ∈ [1/8, 7/8]`. ∎

`c ≥ 2` is exactly the condition that buys back the missing quarter-period: the window is
`3c/4`, and `3c/4 ≥ 1` iff `c ≥ 4/3`.

| check | result |
|---|---|
| conclusion, `c = 2,3,4,5,6,7,8,9,12,16` | 14,883 instances, **0 failures** |
| the period step directly (`G` meets `[c/8, 7c/8]`) | `c = 2, 3, 8`, **0 misses of 4,460** |
| coverage: runners with integral `s` and `gcd(s_2..s_7) ≥ 2` | **1.5%** |

**Coverage is small, and the case it settles is the hard one.** `s_j ≡ 0 mod 8` was the
population that most often defeated small moduli in §6a (757 of 20,000 needing `q > 16`, up to
`q = 29`). It is now closed by proof, and the proof spends no search at all.


---

## 7. Two routes that are closed, with proofs

Recorded so they are not re-entered. One of them was re-entered once in this programme already.

**(a) No measure or covering argument can prove Lemma 6.** `[PROVED]`
In the AP, `s = (1,2,3,4,5,6,7)`, the good set inside `[1/8, 7/8]` is exactly
`{1/8, 3/8, 5/8, 7/8}` — four isolated points, **total measure zero**. So any argument of the form
"the excluded sets are too small to cover the interval" is bounding below a quantity that is zero
in the extremal case, and must fail at every strength. The union bound's failure by `3/2` was a
symptom, not the obstacle.

Directly visible on the circle: each runner needs `1/16` of clearance on each side, and
`8 × 2 × (1/16) = 1` **exactly**. The circle is precisely filled with nothing spare. This is the
zero-measure fragility of the φ(8) law reappearing as an obstruction to a proof technique.

**Consequence: a proof of Lemma 6 must be pointwise — it must exhibit `u`.**

**(b) Density arguments are circular.** `[PROVED — `DYADIC_DEPTH_RESULT_v1.md` §4, 2026-09-07]`
`g(t) = min_j ‖d_j t‖` is continuous, so if `max g > 1/8` then `g > 1/8` on an open interval and a
witness of any dense type exists. That derives existence **from** LRC(8), which is what is being
proved. The same file kills the quantitative version: the required dyadic depth is unbounded,
`κ ≈ log₂ V + c` (max `κ = 7, 8, 8, 9, 10` for `V = 50, 100, 200, 400, 800`).

**(c) A local repair of the spine does not close.** `[VERIFIED — 3,234/3,234]`
When a spine point is excluded and one attempts to move to the next candidate determined by the
excluding `s_j`, the resulting point is excluded by a **different** `s_k` in every case examined.
Three candidate closed forms each resolved about 46% of instances. The excluded case has no local
closed form.

---

## 7a. Checks run on this document

Every checkable assertion above was re-verified for this write-up:

| assertion | check | result |
|---|---|---|
| AP good set in `[1/8,7/8]` is exactly the four spine points | all fractions, denominator ≤ 840 | `{1/8, 3/8, 5/8, 7/8}` |
| `s_max ≤ 7 ⟹ u = 1/8` works | 200,000 random `s ⊂ [1,7]` | 0 failures |
| `s = 17/2` breaks the all-or-nothing | direct | fails at `1/8`, holds at `3/8, 5/8, 7/8` |
| worst instance `u = 25/56` clears `s = {1,3,4,5,6,7,8}` | direct | holds; `7 × 25/56 = 25/8`, `‖·‖ = 1/8` exactly |
| gridness invariant under `V ↦ a + kV` | 20,000 random affine maps | 0 flips |

## 8. Status

| | |
|---|---|
| §1 Lemma 1, two-neighbour condition | `[PROVED]` |
| §2 Lemma 2, φ(8) law; affine invariance of gridness | `[PROVED]` |
| §3 Lemma 3, locality and exactness of `m`; the floor | `[PROVED]` |
| §4 Lemma 4, reduction to one relative revolution | `[PROVED]` |
| §5 Lemma 5, spine witness; integer all-or-nothing | `[PROVED]` |
| §6 Theorem, Lemma 6 ⟹ LRC(8) | `[PROVED, conditional]` |
| §6a Lemma 7, the modulus law | `[PROVED — rational s]` |
| §6a a bound on `q` | `[OPEN]` — verified `q ≤ 29` in 100,000; `q ≤ 2n` is **false** |
| §6b the window is `3/4` of a period, and that is the whole of n = 8 | `[PROVED]` |
| §6b Theorem, the gcd case `c ≥ 2`, from LRC(7) | `[PROVED]` — covers 1.5% |
| §6 **Lemma 6 itself** | **`[OPEN]`** |
| §7 (a), (b) obstructions | `[PROVED]` |

**n = 8 is not proved in this document.** It is proved in the literature by Rosenfeld (2025) via
a 27-prime computation, which this line does not reproduce and does not use. What is established
here is that an analytic proof of n = 8 needs exactly one further ingredient: a pointwise
construction of `u` for Lemma 6 in the case where the spine is excluded. §6b sharpens what that
means: LRC(7) already supplies the six constraints, and what is missing is the last quarter of a
period of room in which to place the witness.

**Scope.** n = 8 throughout. §§1, 3, 4 use `n` only through the threshold `1/n` and the count of
constraints, so they should carry to other `n`; §§2, 5 are written with `8` and are untested
elsewhere. n = 6 and n = 7 have axiom-clean Lean ground truth available to check against.
