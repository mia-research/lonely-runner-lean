# The procedure at orders other than `n = 8`

2026-09-13. Scripts `experiments/nN/exhaustive_nN_v1.py`,
`experiments/nN/opening_closing_nN_v1.py` (outputs `.out` beside each).

**RING-FENCE.** General-`n` line. The `n = 8` paper's artefact `LRC/Construction8/` is
untouched, digest `578022e0296ce565ec601655747d1e5cdc614a9efa2cced6540162e698f43b9d`.

`docs/n8/MANUSCRIPT_v4.md` §9 says the §7.3 figures "are measurements at `n = 8` and say
nothing about other orders". This says something about other orders.

---

## 0. The decision is exact, not sampled

This is **not** the reach measurement of `PHI_REACH_SCALE_v3.md`, which samples instants.
Here the question "does the procedure return for this runner" is **decided**.

An in-the-way zone of reading `s` is the **open** interval `((nk−1)/(ns), (nk+1)/(ns))`, so
the procedure returns exactly when the open zones fail to cover the **closed** window
`[1/n, (n−1)/n]`. The complement of finitely many open intervals inside a closed interval
has its endpoints among the zone endpoints and the window endpoints, so testing exactly
those candidates is complete. No grid, no sampling, no tolerance; `Fraction` throughout.

Zones are never merged. Two zones that touch leave their shared endpoint **clear**, and that
endpoint is a candidate like any other.

**The family differs from the paper's.** The `v_8 ≤ 40` record pins a runner at `0`
(Rosenfeld's formulation). Here the speeds are `n` **distinct positive** integers with gcd
`1` — the framework's own setting, no runner held still. The two are related by the standard
reduction but are not the same enumeration, so counts are not comparable line for line.

---

## 1. Result

| `n` | speeds in | arrangements × runners | failures | worst `u` returned | window ends at |
|---|---|---|---|---|---|
| 5 | `[1,34]` | 1,358,005 | **0** | `77/120 ≈ 0.642` | `0.800` |
| 6 | `[1,26]` | 1,370,916 | **0** | `25/33 ≈ 0.758` | `0.833` |
| 7 | `[1,21]` | 813,113 | **0** | `33/56 ≈ 0.589` | `0.857` |
| 8 | `[1,18]` | 349,992 | **0** | `33/56 ≈ 0.589` | `0.875` |
| 9 | `[1,16]` | 102,960 | **0** | `37/81 ≈ 0.457` | `0.889` |
| 10 | `[1,15]` | 30,030 | **0** | `41/90 ≈ 0.456` | `0.900` |

**4,025,986 runner-instances, zero failures, six orders.** `[EMPIRICAL — exhaustive over
the stated families, exact arithmetic]`

**No trend is claimed in the last two columns.** The speed bound `V` falls as `n` rises, to
keep the enumeration finite, so the families are not comparable across rows: a narrower
speed range is not the same test. The worst-`u` column is reported because it is what the
sweep measured, not as evidence of anything about `n`.

### What this does and does not add

It adds that the procedure's return is not an `n = 8` phenomenon: it holds exhaustively at
five other orders, decided rather than sampled.

It does **not** touch part 7, which is a statement about *every* arrangement at *every*
bound. Nothing above covers speeds outside the stated ranges, and the ranges are small. A
bounded family verified is a bounded family verified.

---

## 2. §7.2's last line, at other orders

> "the first instant of loneliness, when it exists, is always an **opening**
> `(8k+1)/(8d)` for one of the runner's own differences — never a closing."

Stated at `n = 8` and without proof. The right endpoint `(nk+1)/(ns)` of a zone is an
**opening** — a blocker clears there. The left endpoint `(nk−1)/(ns)` is a **closing** — a
blocker arrives. Both are clear, since zones are open; the claim is about which kind comes
first.

| `n` | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
|---|---|---|---|---|---|---|---|
| instances | 129,255 | 162,282 | 136,080 | 102,952 | 45,045 | 10,010 | 4,004 |
| **closings first** | **0** | **0** | **0** | **0** | **0** | **0** | **0** |

**The claim holds at every order tested.** `[EMPIRICAL]`

And it holds *uniformly*, which the `n = 8` statement did not make visible: the window start
`u = 1/n` is itself an opening — it is the right endpoint of the `k = 0` zone of the reading
`s = 1`, the **nearest runner's own difference**. So the case that looked like a third
outcome is the claim's own case.

### A correction recorded, because it nearly went the other way

The first version of this test classified a point that is **both** one zone's right endpoint
and another's left endpoint as a *closing*. That is wrong — a blocker does clear there — and
it manufactured a nonzero closing column: 914 cases at `n = 8`, 2,916 at `n = 5`. Reported
as they stood, those would have been a defect claim against the manuscript. They were an
artefact of the tie-break order in the script. Under the correct rule the column is zero
everywhere. The script now carries the ordering as a comment marked load-bearing.
