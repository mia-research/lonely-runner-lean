# Retraction — `mmin` is not a difficulty measure, and Conjecture M was about the wrong quantity

2026-09-12. Corrects `PROOF_CANDIDATE_v2.md` §3 and `CONJECTURE_M_REFUTED_v1.md`'s framing.

## 1. What happened

`PROOF_CANDIDATE_v2` reduced the remaining gap to **Conjecture M**: an absolute bound on
`mmin`, the least modulus at which a runner has a witness. `CONJECTURE_M_REFUTED_v1` then
refuted it with

    V = (0, 49920, 60375, 76415, 86086, 86184, 156251, 220174)

whose runner 1 has no witness at any denominator `m ≤ 43`.

The refutation is correct. **The conjecture was not worth making**, because `mmin` does not
measure difficulty. For that same runner:

| quantity | value |
|---|---|
| `mmin` | 44 |
| isolation event count | **130,740** |
| `|G_D|` | 0.133456 |
| `(3/4)⁷` | 0.133484 |
| widest component | `3.41 × 10⁻⁶` = `3/(4·max D)` exactly |

Its measure is the generic value to four figures and it has 65,370 mirror pairs of
witnesses. It is one of the *easiest* possible runners. `mmin = 44` records only that its
smallest-denominator witness is `5/44` — a statement about where the thin components sit,
not about how many there are.

This is `K_STATISTIC_RETRACTION_v1` repeating: a proxy adopted as a difficulty measure
without checking that it tracks difficulty.

## 2. The right invariant, and it was already proved

`WN_count_parity_2026_09_12` Step 2: `‖d(−t)‖ = ‖dt‖`, so `G_D` is symmetric under
`t → 1−t`. Components pair up; a self-symmetric component is centred at `t = 0` (never in
`G`) or `t = 1/2` (in `G` iff every `d` is odd). Hence

> **the isolation count is odd ⟺ every constraint is odd**,

so with any even constraint the count is even, and `count ≥ 1` and `count ≥ 2` are the same
statement. Confirmed on the counterexample: `G` symmetric, 130,740 components = 65,370 mirror
pairs.

**The count is the invariant. `mmin` is not.** Conjecture M bounded a quantity that is free
to be large in the easiest cases, so bounding it was never going to bear on LRC(8).

## 3. Adversarial search on the right objective

Hill-climb to **minimise** the per-runner event count, `V` from `[1..40]`:

    worst found: min count = 2   at V = (3, 8, 15, 16, 18, 19, 20, 31)
    per-runner counts    [16, 12, 2, 10, 16, 12, 12, 14]
    per-runner measures  [0.117, 0.129, 0.045, 0.162, 0.181, 0.167, 0.135, 0.094]

It converges to 2 and stops — the floor from `WN_floor_search_2026_09_12`, now also under
targeted minimisation rather than enumeration. Note the count-2 runner has measure 0.045:
**low count does not mean thin.** Count and measure are separate axes.

## 4. Deviation from the reference is determined

`AP = (1,…,8)`, slide `r8` away, track runner 1:

| `r8` | 8 | 9 | 10 | 12 | 16 | 24 | 40 | 80 | 160 | 320 | 640 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| count | 4 | 6 | 8 | 8 | 10 | 10 | 10 | 14 | 24 | 36 | 66 |
| measure | 0 | .056 | .074 | .082 | .054 | .049 | .057 | .064 | .062 | .065 | .065 |

Monotone growth in the count; measure stabilises near 0.064.

Per-runner counts across one step off the reference:

    AP  (1,2,3,4,5,6,7,8)  ->  [4, 8, 8, 6, 6, 8, 8, 4]
    off (1,2,3,4,5,6,7,9)  ->  [6, 6, 8, 8, 6, 8, 8, 2]

**The runner that moves drops from 4 to 2; every other runner gains or holds.** In palindrome
terms, 4 events is 2 mirror pairs and 2 events is 1 mirror pair: deviating costs the moved
runner one pair and buys pairs for the rest. The AP extremes sit at `φ(8) = 4`, and one step
off is the floor of 2.

## 5. The target, restated

Replacing Conjecture M:

> **Can a runner lose its last mirror pair?**

`count = 0` is the only remaining possibility below the observed floor — `count = 1` is
excluded by §2 whenever any constraint is even, and by `WN_count_parity` Step 3 the all-odd
case has count `≥ 9` on the ranges searched. So LRC(8) is exactly: no runner reaches zero
pairs.

This is not a reduction — it is LRC(8) restated in the invariant that actually tracks the
difficulty, rather than in one that does not.

## 6. Status

`[RETRACTED]` `mmin` as a difficulty measure; `PROOF_CANDIDATE_v2` §3's reduction to
Conjecture M. The refutation in `CONJECTURE_M_REFUTED_v1` §2 and its structural obstruction
in §5 both stand as stated — the counterexample is real and the component bound
`3/(4·max D)` is proved — but the conjecture they address was misdirected.

`[PROVED]` §2's parity law (already in `WN_count_parity`).
`[VERIFIED]` §3's search, §4's transit, §1's table.

n = 8 is **not proved**.
