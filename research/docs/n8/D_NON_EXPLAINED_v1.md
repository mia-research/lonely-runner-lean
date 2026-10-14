# `D_non` — what it is, and the sufficient condition it yields

2026-09-13. n = 8, individual isolation, threshold 1/8.

---

## 1. What `D_non` is

For runner `i` with `m = d_min(i)`, its seven differences split by divisibility:

    D_div = { d : m │ d }        D_non = { d : m ∤ d }

The blocking test is the same for both — `dist(d/m, 8ℤ) < 1` — but the **values `d/m` can take**
are not.

**In `s = d/m` space the forbidden region is a union of intervals of width 2:**

    (7, 9)  ∪  (15, 17)  ∪  (23, 25)  ∪  …

- `D_div` gives **integer** `s`. The only integer inside `(7,9)` is **8**. So an integer `s` blocks
  only by *being* a multiple of 8 — a set of isolated points.
- `D_non` gives **fractional** `s`. It can land anywhere in the interval. `7.5` is `0.5` from 8,
  and no integer can ever be `0.5` from a multiple of 8.

**Divisibility makes the test discrete; non-divisibility makes it continuous.** That is the whole
distinction.

Worked, r1 of `(1,3,5,9,12,14,16,18)`, `m = 2`:

| `d` | 2 | 4 | 8 | 11 | 13 | **15** | **17** |
|---|---|---|---|---|---|---|---|
| `s = d/2` | 1 | 2 | 4 | 5.5 | 6.5 | **7.5** | **8.5** |
| `dist(s, 8ℤ)` | 1 | 2 | 4 | 2.5 | 1.5 | **0.5** | **0.5** |
| blocks | no | no | no | no | no | **yes** | **yes** |
| part | div | div | div | non | non | **non** | **non** |

The three `D_div` values are 1, 2, 4 — they would have to reach 8 to block, and they do not. The
two that block are half-integers sitting inside a gap integers cannot occupy.

## 2. The sufficient condition this gives  `[PROVED — arithmetic]`

Blocking requires `dist(s, 8ℤ) < 1` with `s ≥ 1`, so the smallest blocking value is `s > 7`.
Therefore

> **If a runner's largest difference is at most 7 times its smallest — `d_max ≤ 7·d_min` — nothing
> can block it, and its moment is exactly `1/(8·d_min)`.** ∎

No residues, no grid, no integrality. Just the ratio of the extreme differences.

Check: **9,810 of 9,810** runner-instances satisfying the condition attain the bound.

| speeds drawn from | fraction satisfying `d_max ≤ 7 d_min` | of those, attain |
|---|---|---|
| `[1,10)` | **0.833** | 1.0000 |
| `[1,12)` | 0.597 | 1.0000 |
| `[1,24)` | 0.344 | 1.0000 |
| `[1,80)` | 0.308 | 1.0000 |

## 3. A correction to the rates I quoted

I predicted `D_div` blocks at `1/8` and `D_non` at `1/4`, from the widths `1/8` and `2/8` of the
forbidden region. Measured over 336,000 differences: **0.070 and 0.103.** Both well below, and the
ratio is 1.47 rather than 2.

The reason is §2: `s` is not spread uniformly over the reals. It is concentrated at small values,
and a large share of runners never have any `s` exceeding 7 at all — so they cannot block
regardless of divisibility. The width argument is correct about the *region*; it is wrong as a
rate, because the sample does not reach the region.

## 4. Where this leaves the open problem

| | |
|---|---|
| `d_max ≤ 7·d_min` | **proved** — no blocking, moment `= 1/(8·d_min)` |
| `d_max > 7·d_min`, `D_non = ∅` | **proved** — residues decide (`GRID_REFERENCE_REACH_v1`) |
| `d_max > 7·d_min`, `D_non ≠ ∅` | **open** — `s` fractional and able to reach the band interior |

The open case now has two conditions on it, both checkable at a glance. A configuration is hard
for a runner only when it is **spread** (some difference more than seven times the smallest) **and
incommensurate** (that difference not a multiple of the smallest).

## 5. Status

`[PROVED — arithmetic]` §1's dichotomy; §2's sufficient condition.
`[VERIFIED — 9,810 of 9,810]` §2.
`[CORRECTED]` §3 — the `1/8` and `1/4` rates I quoted.

**n = 8 is not proved here.**
