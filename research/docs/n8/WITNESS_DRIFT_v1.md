# Where the isolation points go — the disturbance is strictly local

2026-09-12. Script `experiments/n8/ok_witness_drift_v1.py`. Exact `Fraction`, BSM good sets.
Answers the owner's correction to `TRANSIT_MAP_v1`: that map recorded the **measure** of each
runner's isolation set, and once a runner is off the grid its witnesses are no longer at the
usual place. This records the **location**.

**No stationary runner anywhere.** Bases are eight genuine runners. The per-runner difference
sets `{|v_j − v_i|}` are translation into runner `i`'s own frame — free, not adjoining
(`feedback_count_the_runners_given_2026_09_12`).

---

## 1. Only the moving runner leaves the grid  `[VERIFIED — exact]`

`V = (s, 2,3,4,5,6,7,8)`, `s: 1 → 2`. Distance from each runner's nearest witness to the
nearest grid time `a/8`, in original time units:

| `s` | 1 | 13/12 | 7/6 | 5/4 | **4/3** | 3/2 | 5/3 | 11/6 | 23/12 |
|---|---|---|---|---|---|---|---|---|---|
| **r1** | 0 | .01054 | .02134 | .03241 | **.04375** | .03409 | .01923 | .00500 | .00856 |
| r2…r8 | 0 | **0** | **0** | **0** | **0** | **0** | **0** | **0** | **0** |

Runner 1's drift rises to a maximum at `s = 4/3` and falls back. **Every other runner keeps
its witnesses exactly on grid times throughout.**

## 2. Which grid time each runner uses  `[VERIFIED — exact]`

Smallest odd `a` with `t = a/8` a witness, searched over the whole period (`a < 8q`):

| `s` | r1 | r2 | r3…r8 |
|---|---|---|---|
| 1 (the AP) | 1 | 1 | 1 |
| 13/12 … 5/3 | **none** | **3** | 1 |
| 11/6 | **none** | **7** | 1 |
| 23/12 | **none** | **13** | 1 |

> **The disturbance is strictly local.** The moving runner leaves the grid entirely — *no*
> `a/8` works for it at any `a`. Its neighbour is pushed to a **later** grid time. Every other
> runner is untouched, still isolating at `t = 1/8`.

## 3. The displacement law for the neighbour  `[PROVED + VERIFIED exact]`

Let `D = 1/|2 − s|`. Runner 2's integer differences to runners 3…8 are `1,…,6`, and at any
odd `a`, `‖k·a/8‖ ≥ 1/8` for `k = 1..6` because `8 ∤ ka`. So only the constraint against the
approaching runner binds: `‖(2−s)·a/8‖ ≥ 1/8` ⟺ `a/D mod 8 ∈ [1,7]`. For `a < D` the ratio is
below 1 and fails; `a = D` is the first that works. Hence

> **`a = D` if `D` is odd, `a = D + 1` if `D` is even.**

Measured, exact agreement in all nine cases:

| `1/\|2−s\|` | 2 | 3 | 4 | 6 | 8 | 12 | 16 | 24 | 40 |
|---|---|---|---|---|---|---|---|---|---|
| `a` used | 3 | 3 | 5 | 7 | 9 | 13 | 17 | 25 | 41 |

So the displaced neighbour's witness **recedes as the reciprocal of the gap**: at `t = a/8`
with `a ≈ 1/|2−s|`, it sits about `1/(8|2−s|)` out in time. That is why
`TRANSIT_MAP_v1` §1 found the *fraction* of the period unchanged near collision while the
period itself stretched — the witness is still there, just proportionally further along.

## 4. What this changes

`TRANSIT_MAP_v1` said the transit is flat in measure. That stands, but it was the wrong
quantity to have led with. The structural fact is:

- moving one runner off a grid point costs **that runner** its grid witnesses entirely,
- costs **its nearest neighbour** a factor `1/|gap|` in how far out it must look,
- and costs **the other six runners nothing at all**.

So a perturbation does not degrade the configuration globally; it degrades exactly two
runners, by amounts that are explicit.

## 5. Ledger

`[VERIFIED — exact]` §1's drift table; §2's grid-index table.
`[PROVED]` §3's displacement law, with its derivation; `[VERIFIED — exact]` in all nine
measured cases.
`[SCOPE]` one base (the AP) and one transit (`r1: 1 → 2`). The locality claim of §2 is not
established for other bases; §3's derivation uses only that r2's other differences are
`1..6`, so it generalises to any runner whose integer differences avoid multiples of 8.

`n = 8` is **not proved.**
