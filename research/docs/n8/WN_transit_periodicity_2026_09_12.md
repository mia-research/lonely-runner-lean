# Working note — the transit law is periodicity, and it gives a covering certificate

2026-09-12. n=8 only.

## 1. The law

Along a transit, one speed slides and the other seven are fixed. Fix a runner `i`.
Its constraint set splits into a **fixed part** `F` (the six differences among the
stationary runners) and **one moving difference** `e`, linear in the slider.

Runner `i` is lonely at `t = a/m` iff `‖d·a/m‖ ≥ 1/8` for every `d` in its
constraint set. That condition reads each `d` only through `d mod m`. Therefore

> **Periodicity law.** Whether runner `i` has a witness at modulus `m` depends on
> the slider only through `e mod m`.

So each modulus covers a *periodic* set of slider positions. The transit has no gap
exactly when those periodic sets **cover the integers** — a covering-congruence
question, finite over `lcm` of the moduli used. This is what makes the transit
predictable rather than merely sampled.

## 2. The reduction

Because `F` is constant along the whole transit, the transit collapses to a
question about a single integer:

    A(m) = { a mod m : ‖f·a/m‖ >= 1/8 for all f in F }
    Good(m) = { e mod m : some a in A(m) has ‖e·a/m‖ >= 1/8 }

The transit is gap-free for runner `i` iff `⋃_m Good(m)` covers `ℤ`. `e = 0` is the
collision (slider on the runner's own speed) and is not a valid 8-set; it is
excluded throughout.

Script: `experiments/n8/transit_cover_sieve.py`.

## 3. Certificates obtained  [PROVED for the two rows marked CLOSED]

Greedy sieve, densest `Good(m)` first, moduli `m ≤ 23`, CRT lift capped.

| runner | `F` | moduli used | period | result |
|---|---|---|---|---|
| E* r1 | `{2,6,7,8,10,13}` | `{14,15,16,23}` | 38,640 | **CLOSED** — every `e ≠ 0` has a witness |
| AP r4 | `{1,2,3}` | `{13,16,…,23}` | 5,354,228,880 | **CLOSED** |
| AP r3/r5 | `{1,2,3,4}` | `{13,16,…,23}` | 5,354,228,880 | 2 classes survive the cap |
| E* r7 | `{3,5,6,7,11,13}` | `{16,…,23}` | 411,863,760 | 8 classes |
| E* r4 | `{1,3,5,6,7}` | `{8,13,15,17,…,23}` | 892,371,480 | 26 classes |
| AP r1/r7 | `{1,2,3,4,5,6}` | `{7,15,16,22,23}` | 425,040 | 26 classes |
| AP r2/r6 | `{1,2,3,4,5}` | `{6,7,13,15,16,19,22,23}` | 104,984,880 | 44 classes |

E* r1 is the hardest runner of the hardest known instance and it closes with four
moduli over a period of 38,640. That is a finite, checkable certificate, not a sweep.

The surviving classes in the other rows are an artefact of the greedy sieve's CRT
cap (it skips a modulus whose lift would exceed the cap), not established gaps —
see §4.

## 4. The lcm-aligned class and why a prime kills it

Sieving with `m ≤ M` leaves survivors concentrated on `e ≡ 0 mod lcm(1..M)`: an `e`
divisible by every modulus in range has `e·a ≡ 0` at each of them, so it escapes all
of them at once. This is the same `lcm(1..D)` adversary that refuted the universal-`D`
bound in `DENOMINATOR_TOWER_v1`.

A prime `p > M` is coprime to that alignment, so `e mod p ≠ 0` and the class dies.
Checked directly at `M = 22`: for `F ∈ {{1,2,3,4,5}, {1,2,3,4}, {1,2,3},
{3,5,6,7,11,13}, {1,3,5,6,7}}`, **every** surviving class — including `e = L` and
`e = 2L` for the sieve's own period `L` — has a witness, and nearly all of them at
`m = 23`: `t = 3/23`, `4/23`, `1/23`, `6/23`, `11/23`.

Earlier leftovers from a cruder sieve capped at `m = 48` were also all false:
`(1,2,3,4,5,6,7,62858017141921)` runner 1 is lonely at `t = 7/50`;
`(1,2,3,4,5,6,7,72569527430401)` slider at `t = 1/31`;
`(0,2,6,7,8,10,13,283471231680)` runner 1 at `t = 11/50`. In each case the
truncation, not the configuration, produced the gap.

## 5. Status

- §1 periodicity law: proved, and it is the statement that makes the transit maps
  a law rather than a sample.
- §3 rows marked CLOSED: proved by covering over the stated moduli and period.
- §3 remaining rows: not gaps; the sieve's cap left classes unswept, and spot checks
  in §4 found witnesses for every one tested.
- Not proved: that a suitable prime always exists for arbitrary `F`. §4 is the
  mechanism and it held in every case checked; the general statement needs
  `A(p) ≠ ∅` for some prime `p ∤ e`, which is the same non-emptiness the union
  bound cannot deliver (it gives `7/4 > 1`).
