# Attempt on the measure lemma — enumeration to span 38, and why the lemma fails as stated

2026-09-12. The lemma is `PROOF_CANDIDATE_v3.md` §4, the single open step. **It is not proved
here, and the evidence now runs against its uniform form.**

## 1. Enumeration extended to span 38  `[VERIFIED — exhaustive]`

All 7-element primitive difference sets in a box — every 8-set of that span from one runner's
view. Float screen (keep float-count ≤ 8) then exact `Fraction` verification of survivors.

| `N` | primitive sets | screened | exact min count |
|---|---|---|---|
| 24 | 345,304 | 2,025 | 2 |
| 28 | 1,180,572 | 2,303 | 2 |
| **38** | **12,569,075** | 2,837 | **2** |

Never 0, never 1. Minimisers at `N = 38`:

    (1,2,3,4,5,7,8)   (1,2,3,4,5,7,16)   (1,2,3,4,5,7,32)
    (1,3,4,5,6,7,8)   (1,3,4,5,6,7,16)   (1,3,4,5,6,7,32)

Screen control: re-running `N = 24` through the screened pipeline reproduces the exact run
identically. A float screen can only under-count (single-point components vanish), so it errs
toward keeping candidates.

## 2. A correction to `PROOF_CANDIDATE_v3` §3

v3 asserted that low floors occur **only** at small span. That is false. `(1,4,5,6,7,11,32)`
has `d_max = 32` and count **2**, outside the span-28 enumeration; and the minimisers above
include `d_max = 16` and `32`. Count-2 sets are not confined to small `d_max`.

The doubling family is bounded, however:

| `j` | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|---|---|---|---|---|
| `d_max = 8·2^j` | 8 | 16 | 32 | 64 | 128 | 256 | 512 | 1024 | 2048 | 4096 |
| count, base `(1,2,3,4,5,7)` | 2 | 2 | 2 | 4 | 6 | 8 | 16 | 32 | 60 | 118 |
| `\|G_D\|` | .0286 | .0286 | .0286 | .0208 | .0208 | .0227 | .0217 | .0212 | .0215 | .0215 |

Count 2 stops at `d_max = 32`; beyond that the count grows roughly linearly while the measure
stays near 0.021. P4 is near-exact at scale — at `j = 9` the bound is 117.37 against a count
of 118.

## 3. Why the lemma fails in its uniform form  `[VERIFIED]`

The lemma wanted `|G_D| ≥ c` for non-tight `D`, giving `count > 2` once `d_max > 3/(2c)`.
The constant is **not stable**:

| box | min non-zero `\|G_D\|` | minimiser | implied threshold `3/(2c)` |
|---|---|---|---|
| `[1..12]` | 1/176 = 0.0056818 | `(1,3,4,5,6,7,11)` | 264 |
| `[1..14]` | 1/176 | same | 264 |
| `[1..16]` | 1/176 | same | 264 |
| `[1..18]` | **1/360 = 0.0027778** | `(1,2,3,4,5,7,18)` | **540** |
| `[1..20]` | 1/360 | same | 540 |

It drops when the box widens, and the implied threshold doubles with it. A uniform `c > 0`
is not supported by this, and even at `c = 1/360` the finite remainder would be span ≤ 540 —
`C(540,7) ≈ 10¹⁵` sets, out of reach of enumeration.

So **P4 plus a uniform measure bound cannot close n = 8**, on two counts: the bound is not
uniform on the evidence, and the residual box would be unenumerable even if it were.

## 4. What survives

- The enumeration: floor 2 over 12,569,075 primitive difference sets to span 38.
- P3 and P4 themselves, proved and stress-tested (`P3_P4_AUDIT_v1`), and near-exact at large
  `d_max`.
- The observation that count 2 requires small `d_max` **relative to the measure** — the
  count-2 sets found all have `d_max ≤ 32`, and P4 forces `d_max ≤ 3/(2|G_D|)` for any of
  them. That is a real constraint on where a counterexample could sit; it is not a bound.

## 5. What is needed instead

The quantity that must be bounded is not `|G_D|` alone but the product:

> `d_max · |G_D| > 3/2`.

A run computing `min_D (4 d_max/3)|G_D|` across boxes is in progress; if that minimum stays
below 2 as boxes widen, P4 cannot exclude count 2 at any span and this route is closed.

## 6. Status

`[VERIFIED — exhaustive]` §1's three boxes, to 12,569,075 sets.
`[VERIFIED]` §2's doubling table; §3's five boxes.
`[RETRACTED]` `PROOF_CANDIDATE_v3` §3's claim that low counts occur only at small span.
`[NOT PROVED]` the measure lemma. Its uniform form is unsupported by §3.

n = 8 is **not proved**.
