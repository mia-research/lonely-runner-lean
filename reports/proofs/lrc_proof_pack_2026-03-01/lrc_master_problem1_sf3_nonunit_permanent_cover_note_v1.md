# Master Problem 1 SF3 Non-Unit Permanent-Cover Note (v1)
**Date:** 2026-03-07  
**Purpose:** isolate the non-unit half of `SF3.2-R2`, the bounded-lifetime claim for permanent-cover chains.

## 0) Position in the program
The SF3 overlap problem is now modeled as repeated re-coverage of an exposed object inside a short safe block.

For non-unit runners the right object is slightly richer than in the unit case:
- a fixed residue may be re-covered,
- equivalently, a fixed non-unit support coset may persist for a short time,
- but a single non-unit runner should not be able to sustain that persistence indefinitely.

This note proves the single-runner bound.

## 1) Non-unit support algebra
Let `e` be a non-unit runner with

`g := gcd(e,n) > 1`.

Write

`n = g n_e`,
`e = g e_e`,

with `gcd(e_e,n_e)=1`.

For `q mod n_e`, define the support coset

`C_e(q) := Sol(e, -gq, n)`.

Each `C_e(q)` is a coset of the subgroup

`H_e := (n/g) Z_n`,

so `|C_e(q)| = g`, and the cosets `C_e(q)` partition `Z_n`.

## 2) Exact two-state support blocks

### Lemma NPC.1 (non-unit support block formula)
For every integer floor state `t`, exactly one of the following holds:

1. if `t = gq` for some integer `q`, then
   `bad_set(e,t,n) = C_e(q mod n_e)`;
2. if `t = gq-1` for some integer `q`, then
   `bad_set(e,t,n) = C_e(q mod n_e)`;
3. otherwise,
   `bad_set(e,t,n) = emptyset`.

Equivalently, the support of a non-unit runner is organized into blocks

`{gq-1, gq}`

of two consecutive floor states carrying the **same** coset `C_e(q)`, with all other floor states transparent.

### Proof
By definition,

`bad_set(e,t,n) = Sol(e,-t,n) union Sol(e,-(t+1),n)`.

Since `g=gcd(e,n)`, a solution set `Sol(e,k,n)` is nonempty iff `g | k`, and when nonempty it is a coset of `H_e`.

Now inspect the residues of `t mod g`.

- If `t == 0 (mod g)`, then `g` divides `t` and does not divide `t+1`, so only `Sol(e,-t,n)` survives. Writing `t=gq`, this set is exactly `C_e(q)`.
- If `t == -1 (mod g)`, then `g` does not divide `t` and divides `t+1`, so only `Sol(e,-(t+1),n)` survives. Writing `t=gq-1`, this set is again `C_e(q)`.
- If `t` is neither `0` nor `-1 mod g`, then neither `t` nor `t+1` is divisible by `g`, so both solution sets are empty.

Thus the support comes in two-state blocks `{gq-1,gq}` carrying one coset `C_e(q)`. ∎

## 3) Fixed residue and fixed coset consequences

### Corollary NPC.2 (fixed residue uses one two-state block)
Let `r in Z_n` be fixed.
Because the cosets `C_e(q)` partition `Z_n`, there is a unique `q_r mod n_e` with

`r in C_e(q_r)`.

Then

`r in bad_set(e,t,n)`

iff

`t == gq_r-1 (mod n)` or `t == gq_r (mod n)`.

So a fixed residue is covered by `e` on exactly two consecutive `e`-floor states modulo `n`.

### Proof
By Lemma NPC.1, the only nonempty support sets are the cosets `C_e(q)` realized on states `{gq-1,gq}`.
Since `r` belongs to exactly one such coset, it can be covered only on that corresponding two-state block. ∎

### Corollary NPC.3 (fixed support coset uses one two-state block)
For fixed `q mod n_e`,

`bad_set(e,t,n) = C_e(q)`

iff

`t == gq-1 (mod n)` or `t == gq (mod n)`.

So a fixed support coset also persists for exactly one two-state block of `e`-floor states.

## 4) Transparency gap

### Corollary NPC.4 (forced transparency for `g >= 3`)
If `g >= 3`, then between consecutive active support blocks

`{gq-1,gq}` and `{g(q+1)-1,g(q+1)}`

there are exactly `g-2` transparent floor states:

`gq+1, gq+2, ..., gq+g-2`.

So a non-unit runner with `g >= 3` is forced to cover **nothing** for `g-2` consecutive `e`-states between adjacent support cosets.

### Proof
This is immediate from Lemma NPC.1: only residues `0` and `-1 mod g` yield nonempty support. The intermediate `g-2` residue classes are all empty. ∎

## 5) Event-path theorem
Call a **non-unit `e`-episode** for a fixed residue `r` or fixed support coset `C_e(q)` a maximal connected portion of the event path on which that object lies in `S_e(alpha)`.

### Theorem NPC.5 (non-unit permanent-cover bound)
Let `e` be non-unit with `g = gcd(e,n) > 1`.

1. Every non-unit `e`-episode for a fixed residue `r` meets at most two consecutive `e`-floor states.
2. Every non-unit `e`-episode for a fixed support coset `C_e(q)` meets at most two consecutive `e`-floor states.
3. If `g >= 3`, successive non-unit `e`-episodes are separated by at least `g-2` transparent `e`-states.
4. If `g = 2`, there is no transparency gap, but after each two-state block the support jumps to a different coset, so the same residue or same support coset still cannot persist across three consecutive `e`-states.

Hence a single non-unit runner cannot sustain a permanent-cover chain for a fixed residue or fixed support coset across three of its own consecutive states.

### Proof
By Corollaries NPC.2 and NPC.3, a fixed residue and a fixed support coset are each realized on only one two-state block of `e`-floor states.
Along the monotone event path, the realized `e`-floor state changes by `1` at each `e`-event.
Therefore the path can stay inside the relevant block for at most two consecutive `e`-states, proving (1) and (2).

Statement (3) is Corollary NPC.4.
For (4), when `g=2`, the active blocks are adjacent, but Lemma NPC.1 still says block `q` carries coset `C_e(q)` and the next block carries `C_e(q+1) != C_e(q)`. Since a fixed residue belongs to only one coset, it cannot persist into the next block. ∎

## 6) Consequence for SF3.2
This gives the non-unit single-runner part of `SF3.2-R2`:

> if overlap collapse inside a short safe block is being sustained by one non-unit runner, that mechanism has bounded lifetime.

There are two distinct mechanisms:
- `g >= 3`: the runner is forced into transparent states between active blocks;
- `g = 2`: the runner never becomes transparent, but its support coset changes every two states, so a fixed exposed object still cannot be carried indefinitely.

So in either case, after at most one immediate continuation, either:
- the exposed object becomes uncovered again,
- or the cover burden must transfer to another runner.

## 7) What remains open
This note does **not** prove the full overlap bound.
The remaining debt is now narrower:
- transfer control between different unit and non-unit coverers,
- a chain-level constant bounding how many such transfers can occur inside one short safe block,
- final aggregation to an explicit overlap constant `K`.

## 8) Status
`PROVED` for the non-unit single-runner bound; `OPEN-PROGRAM-TARGET` for full `SF3.2`.
