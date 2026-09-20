# LRC(8) — proof candidate (v2)

2026-09-13. T. Palelei's construction, written out as a candidate. n = 8, circle of
circumference 1, eight runners starting together at distinct constant speeds, threshold 1/8.

**Changes from v1.** Two corrections, both owner-raised. (i) v1 claimed Step 2 "derives the
φ(n) law"; it does not — conservation gives the *state* (Theorem 3.1(c)), not the instants or the
count, which come from the permutation mechanism of `lrc_ap_phi_n_law_v1` Theorem 3.1(a)–(b).
(ii) v1's Step 6 read the reference through a normalised `s`-profile, which is the **stationary
first runner** reduction in disguise. Rebuilt frame-free: no runner is held still, and `v₀`
contributes only a rotation, as the φ(n) paper states.

**Status of this document.** It is a *candidate*: the argument set out in full, in its own
objects, so it can be attacked. Steps 1–6 are proved and the proofs are given. **Step 7 is the
claim** — it is stated as a claim, in one place, and it is what the candidate rests on. No step
imports machinery from outside the construction: no measure, no covering, no equidistribution,
no induction on `n`, no citation of LRC at any other order.

Notation. Speeds `v_1 < … < v_8`. `‖x‖` = distance to the nearest integer. Runner `i` is
**lonely** at time `t` if every other runner is at circle-distance `≥ 1/8`.

---

## Step 1 — Loneliness is a two-neighbour condition  `[PROVED]`

At any instant the eight runners cut the circle into eight cyclic gaps `g_1,…,g_8` with

    SUM_k g_k = 1.

Runner `i` sits at a junction between two consecutive gaps.

> **Runner `i` is lonely at `t` iff both gaps flanking its junction are `≥ 1/8`.**

*Proof.* The nearest other runner is one of `i`'s two cyclic neighbours, so
`min_{j≠i} ‖(v_i − v_j)t‖` is the smaller of the two flanking gaps. The seven constraints
collapse to two. ∎

**There are no end runners.** The speed line has a least and a greatest element; the track does
not. At `t = 1/8` in the AP the cyclic order is `r8 r1 r2 … r7`, so r1's flanks are **r8 and r2**.
Every runner has two neighbours at every instant.

## Step 2 — The reference  `[PROVED]`

**(a) The state, from conservation.**

> All eight runners are lonely at `t` **iff every gap is exactly `1/8`** — the positions are a
> translate of the uniform 8-grid.

*Proof.* All eight lonely means every gap `≥ 1/8` by Step 1. Eight numbers each `≥ 1/8` summing
to `1 = 8 × (1/8)` are all equal to `1/8`. ∎

This is Theorem 3.1(c) of `lrc_ap_phi_n_law_v1`, obtained here from the conservation law.
**It gives the state and nothing more** — not when that state occurs, and not how often.

**(b) The instants and the count — `lrc_ap_phi_n_law_v1`, Theorem 3.1(a)–(b).**

> For speeds `v_i = v₀ + (i−1)δ` with common start, perfect isolation occurs exactly at the times
> with `{δt} = r/n`, `gcd(r,n) = 1`, and there are exactly **φ(n)** of them per phase period.

*Mechanism.* `k ↦ kr (mod n)` is a permutation of `{0,…,n−1}` **iff** `gcd(r,n) = 1`; the number
of such `r` is Euler's totient. `{v₀t}` contributes only a rotation and does not affect relative
spacings.

**No runner is held still and none is privileged.** `v₀` is arbitrary. Equidistance is the grid's
property, not the AP's: `(1,…,8)` and `(2,4,…,16)` are the same object.

## Step 3 — Every runner carries its own scale  `[PROVED]`

> `m := d_min(i) = min(v_i − v_{i−1}, v_{i+1} − v_i)` equals `min_{j≠i}|v_i − v_j|`, and runner
> `i` is not lonely for any `t < 1/(8m)`.

*Proof.* The speeds are sorted, so the nearest speed to `v_i` is an adjacent one — two numbers,
no reference to the rest of the arrangement. For `t < 1/(8m)`, `mt < 1/8`, so `‖mt‖ = mt < 1/8`
and Step 1 fails. ∎

Sortedness cannot be removed by any deviation, so **`m` survives leaving the reference**. It is
the quantity that every arrangement retains.

*On frames.* Reading runner `i`'s differences `v_j − v_i` is not a WLOG that privileges `i` — it
is what "`i` is lonely" **means**. Nothing here holds a runner still; Steps 3–5 are performed
identically and independently for each of the eight.

## Step 4 — One window  `[PROVED]`

Put `u = m·t` (the **lap coordinate**: `u = 1` is one full turn of `i` relative to its nearest
runner) and `s_j = d_j/m ≥ 1`.

> The nearest runner is clear of the threshold exactly on `u ∈ [1/8, 7/8]`.

*Proof.* `‖1·u‖ ≥ 1/8` iff `u ∈ [1/8, 7/8] (mod 1)`. ∎

So Step 3 does not merely give a bound; it gives **one window**, three quarters of a lap long,
and the window is the same object for every runner of every arrangement.

## Step 5 — Every other runner is determined  `[PROVED]`

> At `u`, runner `j` has completed `⌊s_j u⌋` laps relative to `i` and sits at phase
> `s_j u mod 1`. It is clear of `i` iff its phase is **mid-lap**: in `[1/8, 7/8]`.

*Proof.* Its circle-distance from `i` is `‖d_j t‖ = ‖s_j u‖`. ∎

Nothing is searched for. Positions and lap counts are read off.

## Step 6 — The reference, and what a deviation does to it  `[PROVED]`

Write the arrangement as `V = G + e`: a grid `G` of common difference `d`, and a deviation vector
`e`. At a reference instant `t = r/(nd)` with `gcd(r,n) = 1`:

**(a) The grid part is a permutation.** Runner `k` sits at `{v₀t} + (kr mod n)/n`. Because
`gcd(r,n) = 1`, `k ↦ kr (mod n)` is a bijection, so the eight runners occupy the **eight distinct
slots** `0, 1/8, …, 7/8` — one each, every pair at distance `≥ 1/8`, **for every runner at once**.
That simultaneity is why the reference gives *global* isolation, and it needs no runner to be
stationary.

**(b) The deviation displaces in slots.**

> Runner `k` is displaced from its slot by exactly `e_k · r / d` **slots**, a slot being `1/n` of
> the circle.

`[VERIFIED — exact, 15,289 of 15,289]` over random grids `d ∈ {1,…,6}`, deviations `e ∈ [−3,3]`,
and every admissible `r`.

**(c) Consequences, all frame-free.**

- **An integer deviation lands on another slot.** With `d = 1`, the displacement `e_k r` is a whole
  number of slots, so runner `k` lands **exactly on top of** an occupied slot. `(1,…,7,9)`:
  `e = (0,…,0,1)`, `r = 1`, `r8` moves one slot and lands on `r1` at `1/8`.
- **A fractional deviation is not benign either.** `(1,…,7,17/2)` displaces `r8` by half a slot,
  to `1/16` — still inside `r1`. This is Proposition 4.1 of the φ(n) paper: exact grid formation
  is a measure-zero affine set, **zero stability radius**, so *any* perturbation destroys the
  global instant.
- **But only the local occupants lose it.** The displaced runner vacates its own slot and lands
  somewhere; it can be within `1/n` of at most **two** slots. So a single deviation costs the
  reference instant to at most two runners, and the remaining six keep `t = 1/8` **exactly**.
  Measured: 6 of 8 untouched in `(1,…,7,9)`, and `DISTURBANCE_RULE_v1` §1 records 2 (occasionally
  3) disturbed across an exhaustive sweep.

**Why `n`, structurally.** Not because a span happens to be `n−1`. Because `k ↦ kr (mod n)` is a
permutation exactly when `gcd(r,n) = 1`, which is what puts the `n` runners on the `n` distinct
`n`-ths, and there are `φ(n)` such `r`.

---

## Step 7 — The claim

> **Claim.** For every arrangement and every runner `i`, there is a `u` in the window `[1/8, 7/8]`
> at which **all six** of the other runners read mid-lap.

Granted the Claim, the construction closes: take such a `u`; by Step 5 every other runner is at
distance `≥ 1/8`; by Step 4 so is the nearest; by Step 1 runner `i` is lonely at
`t = u/m > 0`. Since `i` and the arrangement were arbitrary, **LRC(8) follows.** ∎

### What the Claim is, and is not

It is **positive and simultaneous**: six lap-phase clocks, running at rates `s_2,…,s_7`, must at
some instant of one window all read mid-lap. It is not a statement about a complement, and it
forms no bad set — the construction never takes a complement anywhere.

**It is not vacuous, and it is not free.** Steps 1–6 reduce the eight-runner problem to it and
settle every case in which the reference itself serves, but they do not deliver it.

### Where the Claim is already proved

| case | by | coverage |
|---|---|---|
| `d_max ≤ 7·d_min` | Step 6 — nobody completes a lap by `u = 1/8` | 35,467/35,467 |
| every grid, and every dilate | Step 6 — distinct residues mod 8 | 485/485 |
| any `i` with no `s_j` within 1 of a multiple of 8 | Step 6 — `u = 1/8` serves | ≈49.5% of runners in random arrangements |
| `u = p/8` for some `p ∈ {1,3,5,7}` | Step 6 with `p` in place of 1 | raises the above |

### Evidence for the Claim where it is not proved

The window is read directly, by the procedure of Steps 3–5, with the Boundary Set Method (open
cells and boundary points evaluated **separately** — the AP's own reading is four isolated points
and is lost by any method that does not).

| population | runner-instances | a mid-lap instant found in the window |
|---|---|---|
| random integer 8-sets `[1,80)` | 9,600 | 9,600 |
| wide spans `[1,400)` | 2,000 | 2,000 |
| near-collision pairs | 2,000 | 2,000 |
| clustered (two tight groups) | 2,000 | 2,000 |
| one far outlier (200–900) | 2,000 | 2,000 |
| rationals, denominators ≤ 29 | 2,000 | 2,000 |
| all speeds `≡ ±1 mod 8` | 2,000 | 2,000 |
| **total** | **21,600** | **21,600** |

Exhaustive check, every integer arrangement with `0 = v_1 < … < v_8 ≤ 20` and gcd 1: **77,400
arrangements, 113,145 distinct runner-profiles, 0 without an instant.**

The instant sits early in the window: median `u = 1/8` (the reference instant itself), 90th
percentile `0.173`, maximum observed `0.446`, against a window ending at `0.875`.

---

## Ledger

| | |
|---|---|
| Steps 1, 3, 4, 5 | `[PROVED]`, arbitrary distinct real speeds, self-contained |
| Step 2(a), Step 6(a)(c) | `[PROVED]` |
| Step 2(b) | `[PROVED — `lrc_ap_phi_n_law_v1` Thm 3.1(a)(b)]`, owner's prior work |
| Step 6(b), the slot-displacement formula | `[PROVED]`, `[VERIFIED — 15,289/15,289]` |
| Step 7, the Claim | **`[CLAIMED]`** — `[VERIFIED — 21,600 + exhaustive to 20]`, not proved |
| Step 7 ⟹ LRC(8) | `[PROVED]` |
| LRC(8) | **not proved by this document** |

**Debts.** Steps 1–7 cite nothing outside the construction. Two separate results obtained in this
session do carry outside debts and are deliberately **excluded** from the candidate, so that it is
not a mix of methods: the incommensurable case via Weyl equidistribution, and the
`gcd(s_2,…,s_7) ≥ 2` case via LRC(7). Neither is used above.

**Scope.** n = 8 throughout. Steps 1, 3, 4, 5 use `n` only through the threshold `1/n` and the
count of gaps. Steps 2 and 6 are written with 8.
