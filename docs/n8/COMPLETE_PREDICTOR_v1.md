# The complete predictor for n = 8

2026-09-13. n = 8, individual isolation, threshold 1/8. Speeds: any eight **distinct reals**.

Consolidates the session. Everything in §2 is proved arithmetic valid for all real speeds;
§3 is the one algorithmic piece; §4 lists what is verified but unproved.

---

## 1. The predictor

Sort the speeds. For runner `i`:

```
  m   :=  min( v_i − v_{i−1},  v_{i+1} − v_i )         its two adjacent gaps
  t₀  :=  1 / (8m)                                      the earliest possible moment

  for each other difference d = |v_i − v_j|:
      if  d mod 8m  lies within m of 0   →  BLOCKED by d

  not blocked  →  t* = t₀ exactly
  blocked      →  t* > t₀ ; iterate:
                    t ← max over blocked d of the next opening (8k+1)/(8d) > t
                    re-test; repeat until clear
```

Cost: `O(n)` per step. One step answers about half of a random configuration outright.

## 2. What is proved

**(T1) `m` is local and exact.** Speeds are sorted, so the nearest speed to `v_i` *is* one of its
two neighbours. Hence `m = min(v_i − v_{i−1}, v_{i+1} − v_i)`, needing only those two. ∎

**(T2) The bound.** For `t < 1/(8m)`: `mt < 1/8`, so `‖mt‖ = mt < 1/8` and runner `i` is not
lonely. Hence `t* ≥ 1/(8m)`, and **nothing precedes it**. ∎

**(T3) The band test.** Lonely at `t₀` means `‖d/(8m)‖ ≥ 1/8` for every other `d`. Multiplying by
`8m`: the distance from `d` to the nearest multiple of `8m` is at least `m`. So

> **blocked ⟺ `d mod 8m` lies within `m` of `0`**, in `ℝ/(8m)ℤ`.

For integer speeds this is an ordinary residue condition with a **band** of `2m−1` forbidden
residues: `{0,…,m−1} ∪ {7m+1,…,8m−1}`. ∎

**(T4) `m = 1` recovers the grid rule.** The band is the single residue `{0}` mod 8 — a runner
keeps `t₀ = 1/8` iff no difference is `≡ 0 mod 8`, i.e. iff it shares no residue. Every grid
result of this series is this case. ∎

**(T5) The spine witness.** For integer `s = d/m`, take `u = p/8` with `gcd(p,8) = 1`. Then
`‖s·p/8‖ ≥ 1/8` unless `s ≡ 0 mod 8`. So **when unblocked, `t₀` itself is the witness** and
`t* = 1/(8m)` exactly. The clean case is constructive, not merely asserted. ∎

**(T6) Ratio condition.** Blocking needs `d/m > 7`. Hence

> `d_max ≤ 7·d_min` ⟹ **no blocking**, and `t* = 1/(8m)`.

No residues, no grid, no integrality. ∎  (Verified 9,810 of 9,810.)

**(T7) Grid theorem.** If `V` is a grid with gcd `g`, and every runner has a neighbour at distance
exactly `g`, then `s = d/g ∈ ℤ` and blocking would require two runners to share a residue mod 8 —
impossible in a grid. So **every moment is `1/(8g)`**. ∎  (Verified 485 of 485.)

**(T8) Reach beyond grids.** (T7) needs only `m │ d` for that runner, not gridness. For integer
speeds any runner with a neighbour one step away has `m = 1`, so residues decide. ∎
(Verified 7,152 of 7,152, of which 7,112 were **not** grids.)

**(T9) Translation invariance.** Isolation depends only on differences, so adding a constant to
every speed changes nothing. Positivity is a presentation convention. ∎

## 3. The one algorithmic piece

When blocked, the iteration of §1 finds `t*` exactly. It is monotone and cannot overshoot: a
blocked constraint must clear before loneliness is possible, so each jump target is itself a lower
bound.

**9,600 of 9,600** agree with exhaustive search. Step counts: 55% in one step, 89% in three,
100% by eleven. **No step bound is proved.**

## 4. Verified but unproved

| | evidence |
|---|---|
| the iteration terminates in ≤ 11 steps | 9,600 instances, max 11 |
| `t*` lies in `[1/(8m), 7/(8m)]` | 21,600 instances, no exception |
| exactly three zero-slack profiles with `s ≤ 20` | 177,100 profiles searched |

The third is the most suggestive. The tight profiles are

    s = (1,2,3,4,5,6,7)      the AP
    s = (1,2,3,4,5,7,12)
    s = (1,4,5,6,7,11,13)

all achieving the threshold **exactly** (min gap `= 1/8`), all lonely only at `1/8, 3/8, 5/8, 7/8`
— the same four instants, the φ(8) spine. Two of the three are not APs and not dilates.

**No profile in 177,100 had zero good points.**

## 5. Two obstructions worth knowing before attempting a proof

**Measure arguments cannot work.** The AP's good set inside `[1/8, 7/8]` is four isolated points,
measure **zero**. So no bound of the form "the bad sets are too small to cover" can succeed at any
strength — the quantity it would bound below is zero in the extremal case. A proof must be
**pointwise**: construct a witness.

**Grid density does not transfer.** Grids are dense (take gcd `1/q`), and moments do converge under
approximation. But every fine approximating grid has `g → 0` while `d_min` stays put, so (T7)'s
hypothesis fails for all of them; and the moment is discontinuous at the AP — `1/8` from below,
`1/2` from above.

## 6. Scope

n = 8 throughout. The band is written with `8 = n`; whether it reads `nm` for other `n` is
untested, and (T1)–(T3), (T5), (T6), (T9) use `n` only through the threshold `1/n`, so they should
carry. n = 6 and n = 7 have verified Lean ground truth to check against.

Irrational speeds are covered by proof, not by sweep: (T2) and (T3) are stated on `ℝ/(8m)ℤ`. The
floating-point sweep (32,000 instances) was a code check.

**n = 8 is not proved here.** It is proved in the literature (Rosenfeld 2025) by a 27-prime
computation. What this gives is a predictor for *when* each runner is lonely, analytic except for
the step count of §3.
