# `(1,2,3,4,5,6,x−1,x)` — pushing the last two out together

2026-09-13. n = 8, individual isolation, threshold 1/8. Companion to `R8_INTEGER_LAW_v1`, which
pushed **one** runner out. Here r7 and r8 move out **as a pair**, staying 1 apart, r1…r6 fixed.
Integers only — the grid structure is an integer phenomenon.

Verified for every integer `x` from 8 to 160.

---

## 1. At every grid point it is the AP exactly  `[VERIFIED — 20 of 20]`

The configuration is a grid iff `8 | x` (residues of `x−1, x` are then `7, 0`, completing
`1..6`). At all twenty such x in range — 8, 16, 24, …, 160:

> **every runner's first isolation is `t = 1/8`, all eight at once, every tally 1, nobody
> delayed.** Identical to the AP on moment, coverage and service.

`(1,2,3,4,5,6,159,160)` — the configuration asked for — is one of these. Its residues are
`1,2,3,4,5,6,7,0`, it is a grid, and every runner is first lonely at `1/8`.

**But not on duration.** The same configuration:

| runner | 1 | 2 | 3 | 4 | 5 | 6 | 159 | 160 |
|---|---|---|---|---|---|---|---|---|
| count | 38 | 80 | 108 | 108 | 78 | 32 | 122 | 120 |
| longest window | 0.0039 | 0.0039 | 0.0040 | 0.0040 | 0.0040 | 0.0041 | 0.0016 | 0.0015 |

Against the AP's counts `4,8,8,6,6,8,8,4` and longest windows up to `1/48 = 0.0208`. Same moment,
same service, **many more and far shorter windows**. Moment and duration disagree completely.

## 2. The contrast with pushing one runner out  `[VERIFIED]`

| family | at a grid point |
|---|---|
| `(1,…,7, x)` | coverage `1/8`, nobody delayed, **r8 takes `k = x/8` turns** while the pack takes one |
| `(1,…,6, x−1, x)` | coverage `1/8`, nobody delayed, **every tally 1** |

**`d_min` is the whole difference.** Pushing one runner out grows its `d_min` to `x − 7`, so it
is free from `t = 1/(8(x−7))` and collects turns while the pack waits for `1/8`. Pushing a
**pair** out keeps them 1 apart, so both keep `d_min = 1`, neither gets a head start, and the
surplus disappears. The pack's `δ` is 1 in both cases, so coverage is `1/8` in both.

## 3. Off the grid points  `[VERIFIED — exact, x = 8..160]`

The delayed set is determined entirely by `x mod 8`:

| `x mod 8` | residues of `(x−1, x)` | delayed | configurations |
|---|---|---|---|
| 0 | `(7, 0)` | **none — grid** | 20 |
| 1 | `(0, 1)` | r1, r8 | 19 |
| 2 | `(1, 2)` | r1, r2, r7, r8 | 19 |
| 3 | `(2, 3)` | r2, r3, r7, r8 | 19 |
| 4 | `(3, 4)` | r3, r4, r7, r8 | 19 |
| 5 | `(4, 5)` | r4, r5, r7, r8 | 19 |
| 6 | `(5, 6)` | r5, r6, r7, r8 | 19 |
| 7 | `(6, 7)` | r6, r7 | 19 |

**Each of r7 and r8 collides with the base runner sharing its residue, and each collision delays
that pair.** The base occupies residues `1..6` only, so residues 0 and 7 are unclaimed: at
`x ≡ 1` the r7 residue is 0 and goes uncontested, at `x ≡ 7` the r8 residue is 7 does likewise —
which is why those two rows delay two runners and the rest delay four.

The count is always even, consistent with the palindrome parity (`CONCLUSIONS_2026_09_12` §2(8)).

## 4. Status and scope

`[VERIFIED — exact]` §1's 20 grid points; §3's table over all 153 integers in range.

**Scope.** One family, r1…r6 fixed at `1..6`, the pair at `(x−1, x)`, integer `x ∈ [8,160]`.
Nothing above 160, no non-integer x, and no other pair spacing — the pair is always exactly 1
apart. A pair at spacing 2 or 3 is untested and would change both runners' `d_min`.

**Not established.** The off-grid coverage values, which §3 does not give a closed form for —
`R8_INTEGER_LAW_v1` R3 has one for the single-runner family and there is no analogue here.
Whether pushing three runners out together continues the pattern.

**n = 8 is not proved here, and is not the target here.**
