# Mapping Case B — the level a runner needs, as a function of two parameters

2026-09-12. n = 8, individual isolation. Exploration, not a proof attempt.
Follows `FRAMEWORK_REASONING_v1.md`, which proved Case A and left Case B open.

Earlier notes sampled this region and reported statistics. This one maps it: for every
primitive 7-set in `[1..20]` it records the grid level actually required, against the two
parameters that determine what is possible.

## 1. The two parameters

**`v_max = max_i v₂(d_i)`.** Level `j` uses grid `m = 2^{j+3}`; any `d_i` divisible by `m`
gives `d_i a ≡ 0` and kills that level outright. So

> **level `j` is available only if `j ≥ v_max − 2`.**

`v_max ≤ 2` is exactly Case A (no difference `≡ 0 mod 8`), where `j = 0` works.

**`#odd` = number of odd differences.** At level `j` a difference with valuation `v` is read
in a window of width `k = j+3−v`; odd differences have the widest window and so the tightest
band condition. They push the level up.

**Excess** `= (actual level) − max(v_max − 2, 0)`: how far past the forced minimum a runner
must go.

## 2. The map  `[VERIFIED — exhaustive, [1..20], 77,400 primitive sets]`

| `v_max` | `#odd` | sets | max excess | mean excess | status |
|---|---|---|---|---|---|
| 0 | 7 | 120 | 0 | 0.00 | **PROVED** — Case A, all four `p/8` |
| 1 | 3–6 | 6,270 | 0 | 0.00 | **PROVED** — Case A |
| 2 | 1–6 | 25,381 | 0 | 0.00 | **PROVED** — Case A |
| 3 | 1 | 560 | 0 | 0.00 | **PROVED** — `m = 16` parity lemma |
| 3 | 2 | 3,150 | 0 | 0.00 | **PROVED** — parity lemma |
| 3 | 3 | 6,720 | 0 | 0.00 | **PROVED** — parity lemma |
| 3 | 4 | 5,880 | 2 | 0.20 | open |
| 3 | 5 | 2,016 | **3** | 0.54 | open |
| 3 | 6 | 210 | 2 | 0.97 | open |
| 4 | 1 | 1,260 | 2 | 0.08 | open |
| 4 | 2 | 5,670 | 2 | 0.07 | open |
| 4 | 3 | 10,080 | 2 | 0.07 | open |
| 4 | 4 | 7,560 | 2 | 0.12 | open |
| 4 | 5 | 2,268 | 2 | 0.24 | open |
| 4 | 6 | 210 | 1 | 0.42 | open |

**Proved cells: 42,201 of 77,400 = 54.5%.**

## 3. What the map shows

**The `m = 16` parity lemma is exactly the `v_max = 3, #odd ≤ 3` block.** Its side condition
"no difference divisible by 16" *is* `v_max ≤ 3`, which is why the whole `v_max = 4` row falls
outside it — not a contradiction, a boundary.

**Excess is driven by odd differences.** Within `v_max = 3`: mean excess 0.00 at `#odd ≤ 3`,
then 0.20, 0.54, 0.97 at 4, 5, 6. Profiling the `v_max = 3` sets: those with excess 0 average
3.19 odd differences, those with excess > 0 average 4.57.

**Excess is bounded and shrinks as `v_max` grows.** Over random wide-range sets:

| `v_max` | 3 | 4 | 5 | 6 | 7 | 8 | 9–13 |
|---|---|---|---|---|---|---|---|
| max excess | 2 | 1 | 1 | 0 | 0 | 0 | 0 |
| fraction at excess 0 | 93% | 92% | 99% | 100% | 100% | 100% | 100% |

So for `v_max ≥ 6` the level is **exactly** `v_max − 2` in every case observed: a runner is
lonely at grid `m = 2^{v_max+1}`, one step past the largest power of two dividing any of its
differences. The difficulty is confined to `v_max ∈ {3,4}`.

**The worst cells are small.** Only **two** sets in the whole box need excess 3:

    (1, 5, 6, 7, 8, 11, 13)   v_max=3, #odd=5, level 4
    (2, 7, 8, 9, 11, 13, 15)  v_max=3, #odd=5, level 4

The first is one of the known tight instances.

## 4. Where this leaves Case B

Case B is not one problem. It is two small cells:

- **`v_max = 3, #odd ≥ 4`** — 8,106 sets, excess up to 3. The parity lemma covers `#odd ≤ 3`
  at this valuation; the complement is what remains.
- **`v_max = 4`** — 27,048 sets, excess up to 2. No lemma reaches this row at all, because the
  parity lemma's side condition excludes it.

Everything with `v_max ≥ 5` was excess 0 or 1 in sampling and excess 0 from `v_max ≥ 6`. That
is not proved and the sampling there is thin (144 sets at `v_max = 6`, 7 at `v_max = 9`).

## 5. Status

`[PROVED]` Case A cells (`v_max ≤ 2`); the `v_max = 3, #odd ≤ 3` cells (parity lemma);
the constraint `j ≥ v_max − 2`.
`[VERIFIED — exhaustive]` §2's table over `[1..20]`.
`[VERIFIED — sampled]` §3's wide-range excess table; the `v_max ≥ 5` rows are thin.
`[OPEN]` the four open cells, 45.5% of the box.

**n = 8 is not proved.** This note maps where the remaining difficulty sits; it removes none
of it.
