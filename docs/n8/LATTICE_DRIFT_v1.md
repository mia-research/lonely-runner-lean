# Isolation times drift off the eighth-lattice — measured, with the law separated from the arithmetic

2026-09-12. n = 8, individual isolation, threshold 1/8. Base AP `(1,…,8)`, runner 1 displaced
by `ε`. Tests the prediction that isolation times move off the exact `p/8` locations once a
speed leaves the grid.

Artifact: `experiments/n8/ok_lattice_drift_v1.py`.

**Individual, not global.** Each runner's constraint set is its own `n−1 = 7` differences.
Global isolation would use all `C(8,2) = 28` pairs and would give all eight runners the
identical good set; at the AP they have four distinct good sets with counts `4,8,8,6,6,8,8,4`.
Verified separately: at `(1,2,3,4,5,6,7,9)`, `t = 55/384` is in runner 1's output with its own
minimum gap `9/64 ≥ 1/8` while the worst pair in the pack is `1/384` apart.

---

## 1. The prediction holds  `[VERIFIED — exact]`

Windows are counted as **on the lattice** if the closed window contains a point `m/8`.

| | AP `(1,…,8)` | | `r1 = 1.01` | |
|---|---|---|---|---|
| runner | windows | on lattice | windows | on lattice |
| 1 | 4 | **4 (all)** | 289 | **127** |
| 2 | 8 | 4 | 608 | 300 |
| 3 | 8 | 4 | 628 | 300 |
| 4 | 6 | 4 | 550 | 300 |
| 5 | 6 | 4 | 482 | 400 |
| 6 | 8 | 4 | 618 | 300 |
| 7 | 8 | 4 | 688 | 300 |
| 8 | 4 | **4 (all)** | 662 | 300 |

At the AP the end runners are entirely on the lattice — their whole good set is the four spine
instants, which is the zero-reserve property. Interior runners hold the same four plus two to
four off-lattice windows, and those off-lattice windows are exactly the **reserve**.

At `r1 = 1.01` the moved runner keeps only 127 of 289 windows on the lattice; **162 have moved
off it**. Its nearest-to-`5/8` window sits at `625/998`, displaced by `0.001253` — it does not
contain `5/8` at all.

## 2. The displacement grows linearly  `[VERIFIED — exact, ε = 1/100]`

Tracking the window nearest `t = k + 5/8`:

| k | 0 | 1 | 2 | 3 | 4 | … | 15 |
|---|---|---|---|---|---|---|---|
| displacement | 0.001253 | 0.003257 | 0.005261 | 0.007265 | 0.009269 | | 0.031313 |

Increment exactly `1/499` at every step, constant over 16 consecutive periods.

## 3. The rate is an identity, not a finding  `[arithmetic]`

`1/499` looked like a law. It is not.

With `r1 = 1 + ε` the constraint to r6 is `d = 5 − ε`. Windows pinned to `d` recur every five
`d`-periods, spacing `5/d`. Against the unit lattice,

    5/d − 1  =  (5 − d)/d  =  ε/d

identically, for every `ε`. Checked: `ε = 1/100 → 1/499`, `1/50 → 1/249`, `1/20 → 1/99`,
`1/10 → 1/49`, `3/100 → 3/497`. No experiment is needed for any of it.

**This is recorded because it nearly went in as a result.** The measured `1/499` and the
identity `ε/d` agree because they are the same statement.

## 4. What is not forced: ownership, and its handover  `[VERIFIED — exact]`

The unforced content is **which** constraint owns the window nearest a given lattice point. The
displacement sequence is linear only while ownership is stable, and ownership changes:

| ε | k = 0 | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|---|
| **1/100** | `499/100` | `499/100` | `499/100` | `499/100` | `499/100` | `499/100` |
| **1/20** | `99/20` | `99/20` | `99/20` | `99/20` | **`39/20`** | **`139/20`** |
| **1/10** | `49/10` | `49/10` | **`69/10`** | `69/10` | `69/10` | **`49/10`** |

The handover comes sooner for larger `ε`: at `ε = 1/10` by `k = 2`, at `1/20` by `k = 4`, and
not within 16 steps at `1/100`. At the handover the displacement jumps and changes sign
(`+0.0366 → +0.0545 → −0.0998` at `ε = 1/20`), so the linear drift of §2 describes a stable
ownership run and nothing more.

This is the nucleation of `WB_window_trajectories` §2 — a window growing until it clamps, then a
new one appearing in a different component — seen on the **time** axis rather than the speed
axis, and for the **moved** runner rather than a stationary one.

## 5. A retraction of my own, before it was written down

An earlier pass of this test reported `ε/d` as a drift law with `d` the binding constraint,
generalised from `ε = 1/100`. Testing `ε ∈ {1/20, 1/10, 3/100}` and movers r4 and r8 returned
**"increment not constant"** in every case. The law as stated was one instance plus an unstated
assumption — that a single constraint owns the window throughout — which §4 shows is false.

The tracker was the fragile part, not the phenomenon. `[RETRACTED — before publication]`

## 6. Status and scope

`[VERIFIED — exact]` §1's occupancy table; §2's displacement sequence at `ε = 1/100`;
§4's ownership table.
`[arithmetic]` §3's identity.
`[RETRACTED]` §5.

**Scope.** One base (the AP), one moved runner in §§2–4 (r1), `ε ∈ {1/100, 1/50, 3/100, 1/20,
1/10}`, and the single lattice family `p ≡ 5 mod 8`. Movers r4 and r8 were tested only for
constancy of the increment, not for the ownership structure. Other lattice families, other
bases, and multi-runner displacement are untested.

**Not established.** Why ownership hands over where it does; whether the handover point is
predictable from `ε` and the constraint set; whether §1's occupancy counts (127, 300, 400) have
a closed form. Nothing here bounds any count or duration below.

**n = 8 is not proved here, and is not the target here.**
