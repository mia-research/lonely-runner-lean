# LRC(8) — proof candidate

2026-09-13. T. Palelei's construction, written out as a candidate. n = 8, circle of
circumference 1, eight runners starting together at distinct constant speeds, threshold 1/8.

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

## Step 2 — The reference: equidistance  `[PROVED]`

> All eight runners are lonely at `t` **iff every gap is exactly `1/8`**.

*Proof.* All eight lonely means every gap `≥ 1/8` by Step 1. Eight numbers each `≥ 1/8` summing
to `1 = 8 × (1/8)` are all equal to `1/8`. ∎

This is the φ(8) law, obtained from the conservation law rather than assumed: a **grid** — of
which the AP is the simplest form — attains it at the four instants `t = p/(8g)`, `gcd(p,8) = 1`.
Equidistance is the grid's property, not the AP's; `(1,…,8)` and `(2,4,…,16)` are the same object.

## Step 3 — Every runner carries its own scale  `[PROVED]`

> `m := d_min(i) = min(v_i − v_{i−1}, v_{i+1} − v_i)` equals `min_{j≠i}|v_i − v_j|`, and runner
> `i` is not lonely for any `t < 1/(8m)`.

*Proof.* The speeds are sorted, so the nearest speed to `v_i` is an adjacent one — two numbers,
no reference to the rest of the arrangement. For `t < 1/(8m)`, `mt < 1/8`, so `‖mt‖ = mt < 1/8`
and Step 1 fails. ∎

Sortedness cannot be removed by any deviation, so **`m` survives leaving the reference**. It is
the quantity that every arrangement retains.

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

## Step 6 — The reference, read in the window  `[PROVED]`

> At `u = 1/8`, runner `j` reads phase `s_j/8`, and is **on its lap line** iff
> `dist(s_j, 8ℤ) < 1`.

*Proof.* `‖s_j/8‖ < 1/8` iff `dist(s_j/8, ℤ) < 1/8` iff `dist(s_j, 8ℤ) < 1`. ∎

Three consequences, all proved:

- **The AP.** `s = (1,2,3,4,5,6,7)`, so the six other runners read `2/8, 3/8, 4/8, 5/8, 6/8, 7/8`
  — the six eighths, evenly spread, every one mid-lap. Step 2 in phase coordinates.
- **Why 8.** A runner is on its lap line at `u = 1/8` exactly when it has completed a whole lap by
  the AP instant. The AP's `s` run `1..7`, every one short of 8, so none has. `d_max ≤ 7·d_min`
  ⟹ the moment is `1/(8m)` with nothing to read — verified 35,467 of 35,467.
- **Grids.** If `m` divides every difference, `s_j ∈ ℤ` and `dist(s_j, 8ℤ) < 1` means `8 │ s_j`,
  i.e. two runners sharing a residue mod 8 — impossible in a grid. So **every grid gives every
  runner the moment `1/(8g)`**, all eight at once. Verified 485/485.

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
| Steps 1–6 | `[PROVED]`, arbitrary distinct real speeds, self-contained |
| Step 7, the Claim | **`[CLAIMED]`** — `[VERIFIED — 21,600 + exhaustive to 20]`, not proved |
| Step 7 ⟹ LRC(8) | `[PROVED]` |
| LRC(8) | **not proved by this document** |

**Debts.** Steps 1–7 cite nothing outside the construction. Two separate results obtained in this
session do carry outside debts and are deliberately **excluded** from the candidate, so that it is
not a mix of methods: the incommensurable case via Weyl equidistribution, and the
`gcd(s_2,…,s_7) ≥ 2` case via LRC(7). Neither is used above.

**Scope.** n = 8 throughout. Steps 1, 3, 4, 5 use `n` only through the threshold `1/n` and the
count of gaps. Steps 2 and 6 are written with 8.
