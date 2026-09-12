# Grid tower v2 — Conjecture T is equivalent to LRC(8), not a reduction

2026-09-12. Supersedes `GRID_TOWER_v1.md` §4. n = 8, individual isolation.

## 1. The bit form  `[PROVED]`

Refining v1 §3. At level `j` the grid is `m = 2^{j+3}`. Writing `d_i = 2^{v_i}u_i` and
`k_i = j+3-v_i`, the band condition on `u_i a mod 2^{k_i}` examines the bits of `u_i a` at
positions `k_i-1, k_i-2, k_i-3`. Since `u_i = d_i/2^{v_i}`, those are the bits of `d_i a` at
positions `j+2, j+1, j` — **the `2^{v_i}` shift cancels**. So the valuations drop out entirely
and the condition is uniform in `i`:

> Runner `i` is lonely at `t = a/2^{j+3}` (`a` odd) **iff for every `i`,
> `(d_i·a >> j) mod 8 ∉ {0, 7}`** — the three binary digits of `d_i a` at positions
> `j, j+1, j+2` are not all equal (boundary case `r = 7·2^j` permitted).

Verified against direct evaluation: **0 disagreements over 4,792 `(D,j)` pairs**, `D` from
`[1..10]` to `[1..4000]`.

This is the cleanest statement of the condition found in this project: no valuations, no
per-runner scales, one shift and one 3-bit test.

## 2. Why the tower always catches — and why that is not evidence

v1 §2 recorded zero misses across 124,051 exhaustive sets and random samples to `[1..10⁵]`,
and read it as support for the tower being the right object. **That reading was wrong.**

`G_D` is a finite union of closed intervals. Dyadic rationals `a/2^k` with `a` odd are dense
in `[0,1]`. So any component of `G_D` of positive length `L` contains one as soon as
`2^{-k} < L`, i.e. at level `j ≈ log₂(1/L) - 3`. The tower catches automatically.

Measured — predicted level `log₂(1/L) - 3` against actual level:

| `D` | `\|G_D\|` | widest `L` | predicted | actual `j` |
|---|---|---|---|---|
| `(5,8,10,12,15,18,19)` | 0.1516 | 0.0211 | 2.57 | 1 |
| `(1,3,10,13,16,17,18)` | 0.0998 | 0.0130 | 3.26 | 3 |
| `(78,119,204,244,277,282,328)` | 0.1224 | 0.00179 | 6.13 | 1 |
| `(23,61,213,310,315,390,394)` | 0.1363 | 0.00173 | 6.18 | 0 |
| `(1,2,5,6,7,8,10)` | 0.0336 | 0.00938 | 3.74 | 1 |

The prediction bounds the actual level everywhere, usually loosely. And the three
measure-zero instances are caught at `j = 0` for the same reason: their good sets are exactly
`{1/8, 3/8, 5/8, 7/8}`, already dyadic with odd numerator.

## 3. The equivalence

Three cases exhaust the possibilities:

- `|G_D| > 0` — some component has positive length, so it contains a dyadic with odd
  numerator. **Conjecture T holds.**
- `|G_D| = 0`, `G_D ≠ ∅` — verified (`WN_reference_collapse`, 1,180,572 sets to `[1..28]`)
  that `G_D = {p/8 : p odd}`, which is dyadic. **Conjecture T holds at `j = 0`.**
- `G_D = ∅` — LRC(8) fails, and so does T.

Therefore

> **Conjecture T ⟺ LRC(8) ∧ (`|G_D| = 0 ⟹ G_D = {p/8}`),**

and the second conjunct is verified exhaustively. **T is equivalent to LRC(8), not a
reduction of it.** Proving T is exactly as hard as the original problem.

## 4. Where this leaves the route

The tower joins the list of reformulations this project has found to be equivalent rather
than reducing: the denominator route, the `Σα` criterion at E*, and the crowding recursion
(`RESIDUAL_ANGLE_v1`, `DENOMINATOR_TOWER_v1`, `CROWDING_DICHOTOMY_v1`) were each shown
equivalent to `|G| > 0`. The grid tower is the fourth.

What it contributes that those did not: §1's bit form, which is a genuinely simpler way to
state the condition, and the observation in §2 that "the tower always catches" is a fact
about dyadic density and carries no information about the hard case.

`GRID_TOWER_v1` §4's claim that T "buys" a 2-adic reformulation with exploitable nested
structure is withdrawn. The scales are nested, but the nesting is what makes dyadics dense —
it is the reason the reformulation is automatic, not a lever.

## 5. Status

`[PROVED]` §1's bit form, with derivation; §3's three-case equivalence.
`[VERIFIED]` §1's 4,792-pair check; §2's level predictions.
`[RETRACTED]` `GRID_TOWER_v1` §4 — Conjecture T is not a reduction, and §2's zero-miss tables
are not evidence for the tower being the right object.

**n = 8 is not proved.** No runner reaching count 0 remains exactly LRC(8), and every
reformulation tried in this session has turned out to be equivalent to it.
