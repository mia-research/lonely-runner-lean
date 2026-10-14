# The spine's shut-structure — the residual is eleven finite cases

2026-09-15. n = 8, threshold 1/8. Companion to `C1_STATUS_v2` §1–§2; it takes that file's residual
— a reading in which all four spine points are shut — and reduces it to a finite list.

**What this is and is not.** §1 and §2 are proved and are elementary. §3 is a finite computation.
Together they change the *shape* of what is open, and they prove nothing about it. The open lemma
is §4, it is the one `C1_MIXED_CONSTRUCTION_v1` §3 already names, and it is exactly as open as it
was.

Notation as elsewhere: `d_j` the seven differences at the subject, `d_min` the least, `s_j =
d_j/d_min` the reading, the spine the four instants `u = p/8` with `p ∈ {1,3,5,7}`. A reading
**shuts** a spine point when it fails the threshold there.

---

## 1. The shut-pattern depends on one number  `[PROVED]`

For `s` real, let `f = f(s)` be the **signed** distance from `s` to the nearest multiple of 8, so
`s = 8k + f` with `k ∈ ℤ` and `|f| ≤ 4`.

> **Lemma 1.** `s` shuts `u = p/8` **iff** `dist(f p, 8ℤ) < 1`, that is, iff
>
>     f  ∈  ⋃_m ( (8m−1)/p , (8m+1)/p )     ∩  [−4, 4].
>
> In particular which spine points `s` shuts depends on `f` alone, not on `s`.

*Proof.* `‖s·p/8‖ = dist(sp, 8ℤ)/8`, and `sp = 8kp + fp` with `8kp ∈ 8ℤ`, so
`dist(sp, 8ℤ) = dist(fp, 8ℤ)`. The reading shuts `p` iff `‖s p/8‖ < 1/8`, i.e. iff
`dist(fp, 8ℤ) < 1`, which is the stated union. ∎

Written out:

| `p` | shut on `f ∈` | total length | density |
|---|---|---|---|
| 1 | `(−1, 1)` | 2 | **1/4** |
| 3 | `(−3, −7/3) ∪ (−1/3, 1/3) ∪ (7/3, 3)` | 2 | **1/4** |
| 5 | `(−17/5, −3) ∪ (−9/5, −7/5) ∪ (−1/5, 1/5) ∪ (7/5, 9/5) ∪ (3, 17/5)` | 2 | **1/4** |
| 7 | `(−25/7, −23/7) ∪ (−17/7, −15/7) ∪ (−9/7, −1) ∪ (−1/7, 1/7) ∪ (1, 9/7) ∪ (15/7, 17/7) ∪ (23/7, 25/7)` | 2 | **1/4** |

> **Corollary 1.1.** Every spine point has shut-density exactly `1/4` in `f`, for all four `p`.

*Proof.* Over one period `8/p` of `fp` the shut window has width `2/p`, and `[−4,4]` holds exactly
`p` such periods, giving total length `p · 2/p = 2` out of 8. ∎

Two things follow immediately. First, `7 × 1/4 = 7/4 > 1`, which is why no argument that counts the
seven readings one at a time can ever close this — the arithmetic does not leave room, whatever the
readings are. Second, the `p = 7` row contains `(−1/7, 1/7)`, and that interval lies inside all four
rows: it is `C1_STATUS_v2` §2's one-reading condition, recovered here as a line of the table.

**Two checks this file's script enforces**, because a hand run of it got both wrong. Each region
must be symmetric in `f → −f`, since `dist(fp, 8ℤ)` is even in `f`; the first attempt enumerated
`m` upward from `−1`, silently dropped the negative branches for `p = 5` and `p = 7`, and the
asymmetry is what exposed it. And each total must be exactly 2 by Corollary 1.1.

## 2. Nine shut-patterns, and six that cannot happen  `[PROVED — finite]`

Cutting `[−4,4]` at the 26 endpoints of §1 gives cells on which the shut-pattern is constant.
Collecting them:

| pattern | total `f`-length | density |
|---|---|---|
| none | 62/35 | 31/140 |
| `[5]` | 48/35 | 6/35 |
| `[1]` | 4/3 | 1/6 |
| `[7]` | 136/105 | 17/105 |
| `[3]` | 8/7 | 1/7 |
| **`[1,3,5,7]`** | **2/7** | **1/28** |
| `[1,3]` | 4/15 | 1/30 |
| `[5,7]` | 8/35 | 1/35 |
| `[3,7]` | 4/21 | 1/42 |
| `[1,3,5]` | 4/35 | 1/70 |

Ten patterns, nine of them non-empty; the lengths sum to 8, as they must.

> **Lemma 2.** Six subsets of `{1,3,5,7}` are **not** the shut-pattern of any reading:
> `[1,5]`, `[1,7]`, `[3,5]`, `[1,3,7]`, `[1,5,7]`, `[3,5,7]`.

A reading that shuts `p = 1` and `p = 5` must also shut `p = 3`; one that shuts 1 and 7 must shut
3 and 5 as well, and so on. The absent patterns are a constraint on what the residual can look
like, and they are the reason §3's list is as short as it is.

## 3. Eleven minimal cases  `[PROVED — finite]`

A collection of readings shuts the whole spine when every `p ∈ {1,3,5,7}` is shut by at least one
of them. Call the collection **minimal** when no proper sub-collection does.

> **Lemma 3.** There are exactly **eleven** minimal collections, and none uses more than **four**
> readings.

| size | collections |
|---|---|
| 1 | `[1,3,5,7]` |
| 2 | `[7] + [1,3,5]`;  `[5,7] + [1,3]`;  `[5,7] + [1,3,5]`;  `[3,7] + [1,3,5]` |
| 3 | `[7] + [5] + [1,3]`;  `[5,7] + [3] + [1]`;  `[5,7] + [3,7] + [1]`;  `[5] + [3,7] + [1]`;  `[5] + [3,7] + [1,3]` |
| 4 | `[7] + [5] + [3] + [1]` |

Enumeration over the nine non-empty patterns of §2, at **every** size from 1 to 4. Stopping at the
first size that yields anything misses the size-4 case, four singletons, which is minimal because no
pair or triple of them shuts all four — an earlier run of this did stop early and did miss it.

## 4. The census, and what is actually open

12,800 runner-instances, four spans, exact rationals:

| | |
|---|---|
| residual — all four spine points shut | 3,601 = **28.1%** |
| minimum readings needed: 1 | **56.0%** |
| 2 | 9.0% |
| 3 | 20.9% |
| 4 | 14.0% |

All eleven minimal cases occur. The largest by a distance is the size-1 case at 56.0%, whose entry
condition is exact: `dist(s, 8ℤ) < 1/7`.

*(These are true minima. `C1_STATUS_v2` §2 first reported 41.1 / 10.0 / 23.4 / 25.5, which was a
**greedy** count — for each spine point it took the first reading shutting it — and over-stated the
number needed. Withdrawn there and here.)*

> **Lemma 4 — as first written here, and WITHDRAWN.** "In each of the eleven cases, some spine
> point `p` and some direction admit a move `u = p/8 ± δ` inside `[1/8, 7/8]` at which every reading
> clears."

**That statement is circular and is withdrawn.** Every `u ∈ [1/8, 7/8]` is `1/8 + δ` for some
`δ ≥ 0`, so it asserts only that the subject is lonely somewhere in the window — which is C1
itself. It reduces nothing. The eleven cases of §3 are real; this way of stating what they leave
open was not.

### What the construction actually tests

`C1_MIXED_CONSTRUCTION_v2`'s move is a **first-fit**. From a spine point `u_0 = p/8` and a
direction, each reading that is already clear permits a displacement before it drops below the
threshold, and each shut reading demands one:

    ROOM  =  min over clear readings of  (distance to its near threshold) / s_j
    NEED  =  max over shut  readings of  (distance to its near threshold) / s_j

and the construction reports success iff `NEED ≤ ROOM`.

> **Lemma 4′ `[REFUTED]`.** In each of the eleven cases, some `(p, direction)` has `NEED ≤ ROOM`.

**Counterexample.** Speeds `(12, 14, 96, 111, 128, 160, 161, 163)`, subject **r6** (speed 160).
Readings `1, 3, 32, 49, 64, 146, 148`; `d_min = 1`. Two readings — 32 and 64 — have `f = 0`, so
each shuts all four spine points on its own, and the case is `[1,3,5,7]` of §3. At every one of the
eight attempts `NEED = 1/256` and `ROOM ≤ 3/1184 < 1/256`. **The first-fit fails eight times out of
eight.**

**The runner is lonely anyway,** at `u = 153/1184`, where the seven distances are
`153/1184, 459/1184, 5/37, 393/1184, 10/37, 79/592, 1/8` — all `≥ 1/8`.

**Why the test misses it.** `ROOM = 3/1184` is where reading 148 leaves through the *far* threshold
`7/8`. It does not stay gone. Walking up from `u = 1/8` in units of `1/1184`, the phase of 148 runs
`1/2, 5/8, 3/4, 7/8, 0, 1/8` — it exits at `δ = 3/1184` and **re-enters at `δ = 5/1184`**, by which
point 32 and 64 have cleared as well. The construction stops at the first exit and never looks.

### The open item, stated without circularity

> **`[OPEN]`.** A condition on the readings, checkable from them, which is **sufficient** for the
> subject to be lonely somewhere in the window, and which **always holds**.

`NEED ≤ ROOM` is checkable and sufficient but does not always hold — 97.0–97.4% by
`C1_MIXED_CONSTRUCTION_v2`'s measurement, and the counterexample above is one of the remaining
cases. `C1_MIXED_CONSTRUCTION_v1` §4 already identified the failure mode by inspection: readings at
distance **exactly 0** from a multiple of 8. Both shutters above sit there.

What §1–§3 contribute is that any such condition now has eleven cases to satisfy rather than an
unstructured population, and that the `f`-value of each reading is the only thing the spine sees.
What is *not* contributed is the condition.

**What is measured.** On the size-1 case of §3, the first-fit succeeds in **1,806 of 1,806**
instances — across six of the eight `(p, direction)` attempts, `p=1` upward most common at 37.9%,
no single choice sufficing, and the bound `δ ≤ 1/(8s)` failing in 25%. The counterexample above is
a size-1 case by pattern but has *two* readings at `f = 0`, which is why it escapes that row.

## 5. Status

`[PROVED]` Lemma 1 and Corollary 1.1; Lemma 2 and Lemma 3, both finite enumerations with their
self-tests in the script.
`[VERIFIED]` §4's census, 12,800 runner-instances; the 1,806/1,806 first-fit successes on the
size-1 case.
`[REFUTED]` Lemma 4′ — the first-fit does not always fit; explicit counterexample at §4.
`[WITHDRAWN]` Lemma 4 as first written in this file — circular.
**`[OPEN]`** a checkable sufficient condition that always holds, and with it C1.

**Scope.** `n = 8` throughout. Lemma 1 generalises verbatim with 8 replaced by `n` and
`{1,3,5,7}` by the residues coprime to `n`; §2 and §3 are re-computations, not re-proofs, and have
not been run for other `n`.

**n = 8 is not proved here.** §1–§3 reorganise the open case; they do not reduce it.

---

Artifact: `experiments/n8/spine_patterns_v1.py` — regions, patterns, minimal collections and the
census, with the symmetry, total-length and enumerate-every-size checks as assertions.
