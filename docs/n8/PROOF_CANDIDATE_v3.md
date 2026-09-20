# LRC(8) — proof candidate (v3)

2026-09-13. T. Palelei's construction. n = 8, circle of circumference 1, eight runners starting
together at distinct constant speeds, threshold 1/8.

**Changes from v2**, all owner-raised in review:
(i) v2 declared "no measure" and then used one — Proposition 4.1's measure-zero affine set. That
citation is removed; §6(c) now proves the exact slot condition instead. (The φ(n) paper's own repo
record notes Prop 4.1 is a *Proof Sketch*, so it should not have been leaned on.)
(ii) §6(b) was graded `[PROVED]` with no proof written. The proof is now given.
(iii) The Claim opened with "there is a `u`" — an existence quantifier. Restated as a property of
the procedure.
(iv) `p` replaced by `r` for the units mod 8, matching `lrc_ap_phi_n_law_v1`. `p` read as a prime
and collided with another index.
(v) §6 called its decomposition base a "grid of common difference `d`". Common difference means
**AP**; grid is the wider notion of §2. Corrected.
(vi) §6(c) said a deviation costs at most two runners; the displaced runner loses the instant too.
(vii) Editorial sentences removed.

**Status.** Steps 1–6 are proved and every proof is written out. **Step 7 is the claim.**
Nothing outside the construction is used: no measure, no covering, no equidistribution, no
induction on `n`, no citation of LRC at any other order. The only external reference is the
owner's own `lrc_ap_phi_n_law_v1`, Theorem 3.1(a)–(b), in §2.

Notation. Speeds `v_1 < … < v_8`; `‖x‖` = distance to the nearest integer; runner `i` is
**lonely** at `t` if every other runner is at circle-distance `≥ 1/8`.

---

## Step 1 — Loneliness is a two-neighbour condition  `[PROVED]`

At any instant the eight runners cut the circle into eight cyclic gaps with `Σ_k g_k = 1`.
Runner `i` sits at a junction between two consecutive gaps.

> **Runner `i` is lonely at `t` iff both gaps flanking its junction are `≥ 1/8`.**

*Proof.* The nearest other runner is a cyclic neighbour of `i`, so `min_{j≠i} ‖(v_i − v_j)t‖` is
the smaller of the two flanking gaps. Seven constraints collapse to two. ∎

**There are no end runners.** The speed line has a least and a greatest element; the track does
not. At `t = 1/8` in the AP the cyclic order is `r8 r1 r2 … r7`, so r1's flanks are **r8 and r2**.

## Step 2 — The reference  `[PROVED]`

**(a) The state, from conservation.**

> All eight are lonely at `t` **iff every gap is exactly `1/8`** — the positions are a translate
> of the uniform 8-grid.

*Proof.* All eight lonely gives every gap `≥ 1/8` by Step 1. Eight numbers each `≥ 1/8` summing
to `1 = 8 × (1/8)` are all equal. ∎

This is Theorem 3.1(c) of `lrc_ap_phi_n_law_v1`, obtained here from conservation. **It gives the
state and nothing more** — not when it occurs, not how often.

**(b) The instants and the count — `lrc_ap_phi_n_law_v1` Theorem 3.1(a)–(b).**

> For `v_i = v₀ + (i−1)δ` with common start, perfect isolation occurs exactly where `{δt} = r/n`
> with `gcd(r,n) = 1`, and there are exactly **φ(n)** such instants per phase period.

*Mechanism.* `k ↦ kr (mod n)` is a permutation of `{0,…,n−1}` **iff** `gcd(r,n) = 1`; the count
of such `r` is Euler's totient. `{v₀t}` contributes only a rotation.

**No runner is held still.** `v₀` is arbitrary. And equidistance is the **grid's** property, not
the AP's: an AP has a common difference, a grid need not — `(1,2,3,4,5,6,15,16)` is a grid and is
not an AP, and `(1,…,8)` and `(2,4,…,16)` are the same object.

## Step 3 — Every runner carries its own scale  `[PROVED]`

> `m := min(v_i − v_{i−1}, v_{i+1} − v_i)` equals `min_{j≠i}|v_i − v_j|`, and runner `i` is not
> lonely for any `t < 1/(8m)`.

*Proof.* The speeds are sorted, so the nearest speed to `v_i` is adjacent — two numbers, no
reference to the rest. For `t < 1/(8m)`, `mt < 1/8`, so `‖mt‖ = mt < 1/8`, and Step 1 fails. ∎

Sortedness cannot be removed by any deviation, so `m` survives leaving the reference.

*On frames.* Reading `v_j − v_i` is what "`i` is lonely" **means**; it is not a WLOG privileging
`i`. Steps 3–5 are performed identically and independently for each of the eight.

## Step 4 — One window  `[PROVED]`

Put `u = m·t` (the **lap coordinate**: `u = 1` is one turn of `i` relative to its nearest runner)
and `s_j = d_j/m ≥ 1`.

> The nearest runner is clear of the threshold exactly on `u ∈ [1/8, 7/8]`.

*Proof.* `‖u‖ ≥ 1/8` iff `u ∈ [1/8, 7/8] (mod 1)`. ∎

**The second neighbour is not thereby clear** and must be read like the rest. `NEIGHBOUR_INTERVAL_v1`
§1 step 3 says "verify the other five"; that undercounts by one. Counterexample:
`V = (4,12,29,37,101,121,176,196)`, runner r4 — `d_min = 8`, second neighbour at difference 64, so
`s = 8`, sitting exactly on its lap line at `u = 1/8` while all five non-neighbours are clear.
Five-only returns `1/8`; the true moment is `9/64`. Checked: five-only differs from the full
reading in **3,276 of 48,000** runner-instances.

## Step 5 — Every other runner is determined  `[PROVED]`

> At `u`, runner `j` has completed `⌊s_j u⌋` laps relative to `i` and sits at phase `s_j u mod 1`;
> it is clear of `i` iff that phase lies in `[1/8, 7/8]`.

*Proof.* Its circle-distance from `i` is `‖d_j t‖ = ‖s_j u‖`. ∎

Positions and lap counts are read off, not searched for.

## Step 6 — The reference, and what a deviation does to it  `[PROVED]`

Write `V = A + e` with `A_k = v₀ + k·d` an **arithmetic progression** (`k = 0,…,n−1`) and `e` the
deviation vector; choose `v₀` so that `e₀ = 0`. Fix a reference instant `t = r/(nd)`,
`gcd(r,n) = 1`. A **slot** is `1/n` of the circle.

**(a) The AP part is a permutation.** Runner `k` sits at `{v₀t} + (kr mod n)/n`. Since
`gcd(r,n) = 1`, `k ↦ kr (mod n)` is a bijection, so the `n` runners occupy the `n` distinct slots,
one each, every pair at distance `≥ 1/n` — **for every runner simultaneously**. That simultaneity
is why the reference gives global isolation, and no runner need be stationary.

**(b) The deviation displaces in slots.**  `[PROVED]`

> Runner `k` is displaced from its slot by exactly `e_k · r / d` slots.

*Proof.* `V_k t = (v₀ + kd + e_k)·r/(nd) = v₀r/(nd) + kr/n + e_k r/(nd)`. The first term is a
common rotation. The second is the slot `kr/n`. The third, divided by the slot width `1/n`, is
`e_k r/d`. ∎  (Independently checked exact, 15,289 of 15,289.)

**(c) When the reference instant survives.**  `[PROVED]`

> The whole configuration is globally isolated at `t = r/(nd)` **iff** every `e_k r/d` is a whole
> number of slots **and** `k ↦ kr + e_k r/d (mod n)` is a bijection.

*Proof.* By Step 2(a), all `n` lonely iff the positions are a translate of the uniform `n`-grid,
i.e. iff the `n` values `(kr + e_k r/d) mod n` are `n` distinct integers. That is exactly the two
conditions. ∎  (Checked: **12,135 of 12,135**, zero mismatches.)

Consequences, all from (b) and (c):

- **A displacement that is not a whole number of slots destroys the instant.** The runner sits
  strictly between two adjacent slot positions, so it is within less than `1/n` of one of them.
  `(1,…,7,17/2)`: `r8` is displaced half a slot, to `1/16`, and is inside `r1`.
- **A whole-slot displacement destroys it only if it breaks the bijection.** `(1,…,7,9)`:
  `e = (0,…,0,1)`, `r = 1` — `r8` moves one slot onto `r1`'s slot, two runners share it, and the
  map is not a bijection. But displacements that **permute** the slots preserve the instant:
  `e = (0,0,8,2,0,−2,0,8)` at `r = 7` moves runners between slots without collision, and all
  eight stay lonely.
- **The loss is local.** A displaced runner off its slot lies within `1/n` of at most two slots —
  an open interval of length `2/n` contains at most two points of a `1/n`-lattice. So it costs the
  instant to at most those two occupants **and to itself**: at most three runners, leaving at
  least five at `t = 1/8` exactly. Measured over an exhaustive sweep, `DISTURBANCE_RULE_v1` §1
  records 2 (occasionally 3).

**Why `n`.** Not a span. Because `k ↦ kr (mod n)` is a permutation exactly when `gcd(r,n) = 1`,
which is what puts the `n` runners on the `n` distinct `n`-ths, and there are `φ(n)` such `r`.

---

## Step 7 — The claim

> **Claim.** For every arrangement and every runner, the procedure of Steps 3–5 — form `m` from
> the two neighbours, form the window, read the other six inside it — **returns the moment**.

Granted the Claim, the construction closes: the returned `u` has every other runner mid-lap by
Step 5 and the nearest clear by Step 4, so by Step 1 runner `i` is lonely at `t = u/m > 0`. `i`
and the arrangement being arbitrary, **LRC(8) follows.** ∎

### Where the Claim is already proved

| case | by | coverage |
|---|---|---|
| `d_max ≤ 7·d_min` | §6 — no runner completes a lap by `u = 1/8` | 35,467/35,467 |
| every grid, every dilate | §6(c) — distinct residues, the map is a bijection | 485/485 |
| any runner with no `s_j` within 1 of a multiple of 8 | §6 — `u = 1/8` returns | ≈49.5% of runners |
| the same at `u = r/8`, `r ∈ {1,3,5,7}` | §6 with `r` in place of 1 | raises the above |

### Evidence where it is not proved

The window is read with the Boundary Set Method — **open cells and boundary points evaluated
separately**. The AP's own reading is four isolated points and is lost by any method that merges
touching closed zones.

| population | runner-instances | procedure returned |
|---|---|---|
| random integer 8-sets `[1,80)` | 9,600 | 9,600 |
| wide spans `[1,400)` | 2,000 | 2,000 |
| near-collision pairs | 2,000 | 2,000 |
| clustered (two tight groups) | 2,000 | 2,000 |
| one far outlier (200–900) | 2,000 | 2,000 |
| rationals, denominators ≤ 29 | 2,000 | 2,000 |
| all speeds `≡ ±1 mod 8` | 2,000 | 2,000 |
| **total** | **21,600** | **21,600** |

Exhaustive: every integer arrangement with `0 = v_1 < … < v_8 ≤ 20`, gcd 1 — **77,400
arrangements, 113,145 distinct runner-profiles, 0 without a return.**

Returned values sit early in the window: median `u = 1/8`, 90th percentile `0.173`, maximum
observed `0.446`; the window ends at `0.875`.

---

## Ledger

| | |
|---|---|
| Steps 1, 3, 4, 5 | `[PROVED]`, arbitrary distinct real speeds |
| Step 2(a) | `[PROVED]` |
| Step 2(b) | `[PROVED]` — `lrc_ap_phi_n_law_v1` Thm 3.1(a)(b), owner's prior work |
| Step 6(a), 6(b), 6(c) | `[PROVED]`, proofs written out; 6(b) and 6(c) independently checked |
| Step 7, the Claim | **`[CLAIMED]`** — `[VERIFIED — 21,600 + exhaustive to 20]`, not proved |
| Step 7 ⟹ LRC(8) | `[PROVED]` |
| LRC(8) | **not proved by this document** |

**Debts.** One, and it is the owner's own: `lrc_ap_phi_n_law_v1` Theorem 3.1(a)–(b) in Step 2(b).
Nothing else is cited. Proposition 4.1 of that paper is *not* used — it is a Proof Sketch there,
and §6(c) proves the exact condition directly instead.

**Correction owed elsewhere.** `NEIGHBOUR_INTERVAL_v1` §1 step 3 ("verify the other five") should
read six; see Step 4.

**Scope.** n = 8. Steps 1, 3, 4, 5 use `n` only through the threshold `1/n` and the gap count.
Steps 2 and 6 are written with 8.
