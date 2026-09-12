# The grid-refinement tower — LRC(8) as a 2-adic band condition

2026-09-12. n = 8, individual isolation. Derived inside the AP/grid variation frame.
Uses no divisibility criterion, no union bound, no denominator route.

## 1. Why a tower

The reference (AP / complete residue system mod 8) gives every runner four witness times
`t = p/8`, `p` odd — two mirror pairs, the `φ(8)` law (`WHICH_GRIDS_ISOLATE_v1` §1).

A runner loses **all four at once** exactly when one of its differences is `≡ 0 mod 8`: for
`a` odd, `‖da/8‖ < 1/8 ⟺ 8 | d`. Variation then moves it onto a **finer grid** — the
behaviour measured in `TRANSIT_MAP_FULL_v2` §1, where a runner displaced to the half-grid
point (`δ ≡ 4 mod 8`, landing on the 4-sublattice) recovered to a count of exactly 36.

So the refinements form a tower of grids `8, 16, 32, 64, …`, i.e. `m = 8·2^j`, and a runner
with count 0 would have to be blocked at **every** level.

## 2. The tower always catches  `[VERIFIED]`

`level(D)` = least `j` with a witness at `t = a/(8·2^j)`, `a` odd.

| population | sets | caught | not caught | level distribution |
|---|---|---|---|---|
| `[1..14]` exhaustive | 3,431 | 3,431 | **0** | `0:1716 1:1517 2:150 3:47 4:1` |
| `[1..16]` exhaustive | 11,432 | 11,432 | **0** | `0:3432 1:2546 2:4640 3:782 4:32` |
| `[1..18]` exhaustive | 31,788 | 31,788 | **0** | `0:11439 1:7015 2:11457 3:1835 4:42` |
| `[1..20]` exhaustive | 77,400 | 77,400 | **0** | `0:31816 1:16523 2:25908 3:3095 4:58` |
| random `[1..100]` | 1,488 | 1,488 | **0** | up to `j=4` |
| random `[1..1000]` | 1,484 | 1,484 | **0** | up to `j=7` |
| random `[1..100000]` | 1,493 | 1,493 | **0** | up to `j=11` |

**Zero misses anywhere.** Witnesses need only the grid refinements — no other modulus is
required. E* `(2,6,7,8,10,13,14)`, which needed modulus 15 in the earlier programme, is
caught at `j = 1`, i.e. `t = 1/16`.

## 3. The 2-adic form  `[PROVED]`

Write `d_i = 2^{v_i} u_i` with `u_i` odd. At level `j`, `m = 2^{j+3}`; put `k_i = j + 3 − v_i`.
For odd `a`,

    d_i · a  mod 2^{j+3}  =  2^{v_i} · ( u_i a  mod 2^{k_i} )

so with `w_i = u_i a mod 2^{k_i}`,

    min(r_i, m − r_i) = 2^{v_i} · min(w_i, 2^{k_i} − w_i)

and the loneliness requirement `min(r_i, m−r_i) ≥ m/8 = 2^j` becomes
`min(w_i, 2^{k_i} − w_i) ≥ 2^{k_i − 3}`. Hence

> **Runner `i` is lonely at `t = a/(8·2^j)` (a odd) iff for every `i`:**
> - `k_i ≥ 1`, and
> - `k_i ≤ 2`, or `2^{k_i−3} ≤ u_i a mod 2^{k_i} ≤ 7·2^{k_i−3}`.

`k_i ≤ 0` means `2^{j+3} | d_i`, giving `r_i = 0` — failure. `k_i ∈ {1,2}` makes the band
condition vacuous (`2^{k_i−3} < 1 ≤ w_i`). Only `k_i ≥ 3` constrains.

Consequently **level `j` is available only if `j ≥ max_i v_i − 2`**, and then the question is
whether some odd `a` drives every `u_i a` into the middle-three-quarters band at its own
scale `2^{k_i}`.

Verified against direct evaluation: **0 disagreements over 3,960 `(D, j)` pairs**, `D` drawn
from `[1..12]` to `[1..5000]`.

## 4. What this buys

LRC(8) becomes a statement with no number theory outside the 2-adics:

> **Conjecture T.** For every admissible `D` there is a level `j` and an odd `a` such that
> every `u_i a mod 2^{k_i}` lies in the middle band.

Conjecture T implies LRC(8). It is *stronger* (it restricts witness times to grid
refinements), and §2 found no counterexample in 124,051 exhaustive sets plus random samples
to `[1..10⁵]`.

The band is three quarters of the residues at each scale, and there are seven conditions —
so a naive count gives `7 × 1/4 = 7/4 > 1` and fails, exactly as every earlier counting
argument on this problem has. The difference is that the scales `2^{k_i}` are **nested**, not
independent: `a` is one odd 2-adic number read at seven different precisions. That structure
is what a proof would have to use, and it is not available in the general-modulus setting.

## 5. Status

`[PROVED]` §3's reformulation, with derivation; the `k_i ≤ 0` and `k_i ≤ 2` cases.
`[PROVED]` §1's claim that a runner loses all four reference witnesses iff `8 | d` for some `d`.
`[VERIFIED]` §2's seven populations, 0 misses; §3's 3,960-pair check, 0 disagreements.
`[CONJECTURE]` §4's Conjecture T. Not proved.

**n = 8 is not proved.** I could not prove that no runner reaches count 0; that is LRC(8)
itself. What this note does is replace it with a strictly 2-adic statement about nested
scales, verified but open.
