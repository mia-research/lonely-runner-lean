# Pushing a block out — predicted in advance, confirmed exactly

2026-09-13. n = 8, individual isolation, threshold 1/8. Integers only; the grid structure is an
integer phenomenon. Predictions were written down before the test.

Companions: `R8_INTEGER_LAW_v1` (one runner pushed out), `R7_R8_PAIR_LAW_v1` (two).

---

## 1. The predictions, written first

For `(1,2,3,4,5, x−2, x−1, x)` — the last **three** pushed out as a block:

- **grid iff `8 | x`** (base holds residues `1..5`, the block must hold `{6,7,0}`);
- **at a grid point it is the AP exactly** — every moment `1/8`, coverage `1/8`, every tally 1,
  nobody delayed — because the block members are 1 apart so every `d_min = 1`;
- **off a grid point** the delayed count is set by how many block residues collide with base
  residues `1..5`, giving `0, 2, 4, 6, 6, 6, 4, 2` for `x mod 8 = 0…7`.

And separately: if the three are pushed out **spread** instead of adjacent —
`(1,2,3,4,5,14,23,32)`, still a grid — their `d_min` becomes 9, so they should be improved to
`1/72` and bank extra turns, as the lone r8 did.

## 2. Results  `[VERIFIED — exact]`

| prediction | result |
|---|---|
| grid points behave exactly like the AP | **20 of 20** |
| delayed count `0,2,4,6,6,6,4,2` by `x mod 8` | **153 of 153** |

| `x mod 8` | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|---|
| predicted | 0 | 2 | 4 | 6 | 6 | 6 | 4 | 2 |
| **observed** | **0** | **2** | **4** | **6** | **6** | **6** | **4** | **2** |

The spread grid `(1,2,3,4,5,14,23,32)`:

| runner | 1 | 2 | 3 | 4 | 5 | 14 | 23 | 32 |
|---|---|---|---|---|---|---|---|---|
| `d_min` | 1 | 1 | 1 | 1 | 1 | **9** | **9** | **9** |
| moment | 1/8 | 1/8 | 1/8 | 1/8 | 1/8 | **1/72** | **1/72** | **1/72** |
| tally | 1 | 1 | 1 | 1 | 1 | **3** | **3** | **4** |

Coverage `1/8`. Improved to `1/(8·9)` exactly, and banking 3, 3, 4 turns — predicted in direction,
not in value.

## 3. The rule across all three families

| family | block spacing | at a grid point |
|---|---|---|
| `(1,…,7, x)` | — (single) | `d_min(r8) = x−7`, moment `1/(8(x−7))`, **tally `x/8`** |
| `(1,…,6, x−1, x)` | 1 | all `d_min = 1`, all moments `1/8`, **all tallies 1** |
| `(1,…,5, x−2, x−1, x)` | 1 | all `d_min = 1`, all moments `1/8`, **all tallies 1** |
| `(1,…,5, 14, 23, 32)` | 9 | block `d_min = 9`, moments `1/72`, **tallies 3,3,4** |

> **Two quantities settle everything, and they are independent.**
>
> **`d_min`** — the runner's nearest neighbour **in speed** — fixes its moment, `1/(8·d_min)`,
> and how many turns it banks before the pack is served.
>
> **residues mod 8** — nearest **in residue** — fix whether `t = 1/8` is available at all, and
> which runners collide.

How far a block is pushed out is irrelevant to both. What matters is the **spacing inside the
block** (which sets `d_min`) and the **residues it occupies** (which set the collisions). Pushing
`(x−2,x−1,x)` to x = 16 or x = 160 gives identical behaviour; pushing the same three runners to
`14, 23, 32` instead changes everything, though it is no further out.

**Coverage is `1/8` in every grid case**, because the base runners always retain `d_min = 1` and
are never improved. Only the pushed-out runners gain.

## 4. Status and scope

`[VERIFIED — exact]` §2, all rows.
`[PREDICTED THEN CONFIRMED]` §1's three claims for the adjacent block, and the direction of the
spread-block claim.

**Scope.** Integer x in `[8,160]`; one base per family; block spacings 1 and 9 only. The tallies
`3,3,4` in the spread case were not predicted and have no stated form. No four-runner block.

**Not established.** A closed form for off-grid coverage in the two- and three-block families —
`R8_INTEGER_LAW_v1` R3 has one only for the single-runner family. Why the spread block's tallies
are `3,3,4` rather than equal.

**n = 8 is not proved here, and is not the target here.**
