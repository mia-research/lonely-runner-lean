# Conclusions — n = 8 via the AP/grid reference frame

2026-09-12. Supersedes the conclusions in `HANDOVER_2026_09_12.md`. Conflicts between earlier
notes are resolved here; this file is the one to read.

n = 8 is **not proved**.

---

## 0. Standing conventions

**Speeds are distinct positive integers. No runner is given speed 0.**

Translation is free — shifting every speed by `c` leaves all differences and therefore all
isolation unchanged (verified: `(0,…,7)` and `(1,…,8)` give identical counts
`[4,8,8,6,6,8,8,4]`, and likewise for every set tested). But writing a translated set with a
`0` in it invites reading a free translation as an **adjoined stationary runner**, which is a
different configuration with `n` one larger and threshold `1/(n+1)`. Write `(1,…,8)`, never
`(0,…,7)`.

**BSM is the method of preference.** The Boundary Set Method evaluates boundary points and
open cells **separately**, because a single constraint's bad set is the *open* interval between
its boundaries — an endpoint can be lonely while the cell interior is not (`d = 4`, `t = 7/32`,
where `‖7/8‖ = 1/8` exactly). Midpoint-only testing cannot see this. Implementations:
`experiments/n8/bsm_transit.py` (exact `Fraction`) and `experiments/n8/bsm_fast.py` (integer
arithmetic, ~1000× faster). They agree with each other and with the independent interval-merge
construction: **0 disagreements over 495 sets, 0 cell anomalies.**

**A related trap, for max-min-gap work.** The minimum gap is concave on each order-cell, so its
maximum can be **interior**. Candidate times are `m/Δ` with `Δ` a *signed difference of signed
differences* — not merely `k/d` for `d` a difference. Using the narrower set reports the AP
itself as failing global isolation.

## 1. The reference

**Definition.** A **grid** is a set of `n` distinct speeds whose reduced residues form a
complete system mod `n`, where **`n` is the number of runners**. An AP is the case with all
deviations zero. In coordinates `u_i = π(i) + n q_i`, `π` is the complete residue system and
the shape is entirely `q`.

**The modulus is `n`, and it is forced.** `n` runners make `n` gaps summing to 1; if every gap
is `≥ 1/n` then every gap is exactly `1/n`, or the sum exceeds 1. So the positions must be the
uniform `n`-grid. This is arithmetic, not a convention.

**Being drawn from an AP of length `m` does not confer modulus `m`.** `(1,2,3,8)` is drawn
from the AP `1..8`; it has four runners, its residues are complete mod 4 and not mod 8, and it
globally isolates at `t = 1/4`. The AP `1..14` needs mod 14 because it *has* fourteen runners.

**Worked grids.** `(1,2,3,8)`, `n = 4`, isolates at `t = 1/4`. `(2,4,6,104)`, `n = 4`, isolates
at `t = 1/4`. `(1,…,8)`, `n = 8`, isolates at `t = 1/8`.

**Spread is irrelevant to global isolation.** It lives entirely in `q`, which the residue
criterion cannot see.

**Global isolation is not LRC.** A grid puts every runner lonely at the *same* instant; LRC
needs each runner lonely at *some* instant. The grid is the reference, not the target.

## 2. Proved

1. A grid is globally isolated at exactly `φ(n)` instants `t = p/(ng)`, `gcd(p,n)=1`.
2. Those instants lie in every runner's good set simultaneously — the **spine**. A runner holds
   all of them or none, since `n | dp ⟺ n | d` for `gcd(p,n)=1`.
3. The eighth-lattice is strictly nested: `t = k/8` needs `dk ≢ 0 mod 8`, so `k=4` (all `d`
   odd) ⟹ `k=2,6` (no `d ≡ 0 mod 4`) ⟹ `k` odd (no `d ≡ 0 mod 8`). The spine is the weakest
   requirement and the last to go.
4. `max S = 8` ⟺ the configuration is a grid, where `S(t)` is the number of runners lonely at
   `t`.
5. `max S ≥` the number of spine holders.
6. `k ≤ 6`, where `k = 8 − #distinct residues`. `k = 7` forces `8 | gcd`, contradicting
   primitivity.
7. With `m` distinct residues, a box `[1..N]` offers about `m(N/8+1)` slots, so small `m`
   forces large `N`: high grid distance requires large spread.
8. Count 1 is impossible whenever any constraint is even (palindrome/parity).
9. Every component of `G_D` has length `≤ 3/(4·max D)`, hence `count ≥ (4·max D/3)·|G_D|`.

## 3. The central identity

**`base min = 4 + (fewest extras)`** — exact over all 6,305 grid shapes `q ∈ {0,1,2}⁸`, no
exceptions.

Every grid gives every runner the spine; shapes differ only in **reserve** (a runner's windows
other than the spine). The tight AP is the unique worst grid because its two end runners have
**zero reserve** — their entire good set is the spine.

Reserve profiles: tight AP `0,4,4,2,2,4,4,0`; alternating `8,12,8,2,2,8,12,8`; two clusters
`6,14,12,8,8,12,14,6`; wide linear `10,14,10,14,12,10,18,10`.

## 4. What a deviation does

- It removes the spine from **exactly the runners it puts into residue collision** — all `φ(8)`
  instants at once, since the spine is all-or-nothing.
- The **reserve is left alone**: for 3,657 runners that kept the spine across a move, reserve
  went up 30.4%, unchanged 40.8%, down 28.8%; mean 5.84 → 5.87.
- A runner that loses the spine lands on a finer 2-power lattice: levels `{1:1474, 2:2056,
  3:1404, 4:202}` over 5,136 floor-of-2 runners, and **zero at level 0**, which (2) forces.
- Moving a runner **toward the centre** of the pack costs more than moving it the same distance
  away — all eight runners, no exceptions.
- Holding the deviation multiset fixed and varying only **which residue each attaches to**
  swings the floor up to **4×**.

## 5. Where the difficulty is

**Exactly one residue collision.** Min count by number of runners sharing a runner's residue,
exhaustive over `[1..24]`:

| shares with | 0 others | 1 other | 2 others | 3 others |
|---|---|---|---|---|
| instances | 4,044,814 | 3,778,096 | 791,910 | 23,436 |
| **min count** | 4 | **2** | 4 | 8 |

**Grid distance.** Danger band `k = 1..4`:

| `k` | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|---|
| min count | 4 | **2** | **2** | **2** | **2** | 4 | 8 | impossible |
| `max S` | 8 | 6 | 4–6 | 3–6 | 4,6 | 4–6 | 4,6 | — |

**Both flanks are safe, for different reasons.** `k = 0` by the spine (proved). `k ≥ 5` by the
spread that high `k` forces (7). Near-collision by explosion: as two runners approach, the
count grows like `1/ε` — 300 at `ε = 1/100` — with the rate converging to 3.

## 6. Scale behaviour

- The **measure** of a runner's good set is generic (≈ 0.1302) between rationals and jumps at
  every commensurate point, with the AP the deepest jump (to 0). Leaving the AP is a jump, not
  a slide.
- The **count** at a varied speed `p/q` grows close to linearly in `q`.
- From an integer base, non-integer positions are uniformly safer; min count by denominator
  `1,2,3,4,6,8,12,24` is `2,10,12,13,25,25,37,71`.
- A window is the intersection of a fixed component with a sliding bad interval: **one endpoint
  fixed, the other sliding until it clamps.**

## 7. Why the framework does not yet close

If some configuration had a runner at count 0, any path from the reference has a **first** move
breaking the invariant. So "the invariant survives every move" is logically identical to "no
configuration has count 0". The framework re-indexes the problem by move rather than by
configuration; it does not reduce it.

This is the structural obstacle any argument of this shape must pass, and it is not a defect of
the idea.

## 8. Floors

No count below 2 was found in any population: 12,569,075 difference sets to span 38; exhaustive
half-integer displacement at every `k`; all grid shapes; non-grid bases; all transits both
directions; annealed search. Count 1 is impossible by (8), so 2 and 1 are the same floor.

**Nothing above bounds any count below.**

## 9. Open

1. The popcorn structure of the measure — jump magnitude as a function of denominator.
2. Window trajectories where the varying constraint is not the largest, or several move.
3. A measure-based statement of the floor. Every count result lives on reduced integer
   configurations and has no analogue at irrational speeds, where count-per-period is undefined
   but the measure is generic.
4. `k = 6` by a second generator; it was constructed, not enumerated.
