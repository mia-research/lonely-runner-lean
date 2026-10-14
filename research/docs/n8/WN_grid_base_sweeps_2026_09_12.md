# Working note — sweeping the last runner from a grid base

2026-09-12. n = 8, individual isolation. Companion to
`WN_offap_displacement_map_2026_09_12.md`, which disturbed the AP. This one starts from a
**grid** — any complete residue system mod 8 (`WHICH_GRIDS_ISOLATE_v1` §1) — and sweeps the
last runner upward. BSM in integer arithmetic, exact.

## 1. The sweep

Base `(1,2,3,4,5,6,7,x)`. The residues are a complete system mod 8 exactly when `x ≡ 0 mod 8`,
so the sweep passes through grids at `x = 8, 16, 24, 32, 40` and is off-grid between them.
65 positions in steps of `1/2`.

| `x` | 8 | 8.5 | 9 | 10 | 11 | 12 | 14 | 16 | 24 | 32 | 40 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| grid? | **yes** | | | | | | | **yes** | **yes** | **yes** | **yes** |
| cycle | 1 | 2 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
| min count | 4 | 10 | **2** | 4 | 6 | 6 | 4 | 8 | 8 | 8 | 8 |

Minimum over the whole sweep: **2, at `x = 9`** — one step past the first grid point. Only
four positions fall to 4 or below: `x = 8, 9, 10, 14`.

## 2. Half-integers are *high* here — correcting the earlier reading

In the AP-displacement map every minimiser sat on a half-integer, and I described the
adversary as "choosing halves". That was the wrong generalisation. Here the half-integers
give the **highest** counts in the sweep (10, 10, 10, 12, 14, …, rising), not the lowest.

The reason: at `x = 17/2`, scaling by 2 gives `(2,4,6,8,10,12,14,17)`, with reduced speeds up
to 17 — *larger* than the AP's 8. In the AP sweeps halves kept the reduced configuration
small; here they enlarge it.

> The rule is **small reduced configurations are dangerous**. Halves achieved that in one
> setting and the opposite in another.

## 2a. Fine sweep between grid points  `[VERIFIED — 193 positions, resolution 1/24]`

§1 stepped in halves, which barely samples the interior. Sweeping `x` from grid point 8 to
grid point 16 at resolution `1/24` — every position strictly between is off-grid:

| denominator of `x` | 1 | 2 | 3 | 4 | 6 | 8 | 12 | 24 |
|---|---|---|---|---|---|---|---|---|
| positions | 9 | 8 | 16 | 16 | 16 | 32 | 32 | 64 |
| **min count** | **2** | 10 | 12 | 13 | 25 | 25 | 37 | 71 |

The minimum over the whole interval is **2, attained only at `x = 9`**, an integer. Every
position with count `≤ 4` is an integer: `x = 8, 9, 10, 14`. The minimum rises monotonically
with the denominator of `x`.

**Non-integer speeds are uniformly safer here**, and this reconciles §2 with the
AP-displacement result. The operative quantity is the size of the configuration *after
reduction by the gcd*:

- moving **all** runners onto a common finer lattice (AP case, `k = 8` on halves) leaves the
  reduced configuration the same size — so counts stay low;
- moving **one** runner off the lattice the other seven occupy (here) multiplies the reduced
  configuration by that runner's denominator `q` — so counts scale up with `q`.

That is why halves were the adversary's choice in one experiment and the safest option in the
other. Neither "halves" nor "small denominators" is the rule; **a small reduced configuration
is the rule**, and the two experiments reach it by opposite means.

## 3. The worst position is one grid step past the grid point

| base | grid step | `x = G−s` | `G` | `G+s` | `G+2s` | `G+3s` |
|---|---|---|---|---|---|---|
| `(1,…,7,x)` | 1 | – | 4 | **2** | 4 | 6 |
| `(2,4,…,14,x)` | 2 | – | 4 | **2** | 4 | 6 |
| `(1,3,…,13,x)` | 2 | – | 4 | **2** | 4 | 6 |

Identical in all three, because the three bases are **affine copies of one another** — and all
three worst cases reduce to the same integer configuration:

    (1,2,3,4,5,6,7,9)      -> (0,1,2,3,4,5,6,8)   counts [6,6,8,8,6,8,8,2]
    (2,4,6,8,10,12,14,18)  -> (0,1,2,3,4,5,6,8)   identical
    (1,3,5,7,9,11,13,17)   -> (0,1,2,3,4,5,6,8)   identical

That is the **`VACANCY_FRAME_v1` minimiser** — the 9-grid with position 7 vacant — which that
note found to be the unique worst configuration at every grid size `M ≤ 16`, by a completely
different route. Three lines of work now land on this one set:

- exhaustive vacancy enumeration (`VACANCY_FRAME_v1`)
- disturbing the AP, exhaustive over half-integers at `k = 8` (`WN_offap_displacement_map` §4a)
- sweeping the last runner from a grid base (here)

## 4. Spread grids are safer

Bases whose runners are not tightly clustered never reach 2:

| base | minimum over the sweep |
|---|---|
| `(1,2,3,4,5,6,15,x)` | 4 at `x = 17` |
| `(1,2,3,4,5,14,15,x)` | **6** at `x = 17` |
| `(1,2,3,12,13,14,15,x)` | 4 at `x = 17` |

So the floor of 2 is a property of the *tight* grid, not of grids generally. Spreading the
base raises the floor, and all three spread bases bottom out at the same relative position
`x = 17` rather than one step past a grid point.

## 5. Reading

Sweeping away from a grid does not degrade isolation progressively. There is one sharp dip,
immediately adjacent to the grid point, and everything further away is safer — the counts
grow roughly linearly with `x` thereafter (r8's own count runs 4, 2, 4, 8, 6, … 22, 28 across
the sweep).

The dangerous configuration is not far from the reference and not irregular. It is the
reference with **one runner displaced by a single grid step**.

## 6. Status

`[VERIFIED — exact]` §1's 65 positions; §2a's 193-position fine sweep; §3's affine
equivalences and the three-base table; §4's three spread bases.
`[CORRECTED]` the "adversary chooses halves" reading in
`WN_offap_displacement_map_2026_09_12` §4 — see §2. The minimisers there are halves, but the
operative property is the size of the reduced configuration, not the denominator.

**n = 8 is not proved.**
