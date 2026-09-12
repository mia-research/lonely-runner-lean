# Red team — what the mapping missed, and the permutation test

2026-09-12. n = 8, individual isolation. Re-examination of the mapping series for untested
assumptions, plus the test it turned out to be missing.

## 1. Checked: is the spine really the bottom?

`SPINE_AND_RESERVE_v1` called the four instants `p/8` (`p` odd) the spine and treated all
other windows as unstructured reserve. But the eighth-lattice has **seven** non-zero points,
and each has its own condition: `t = k/8` is a witness iff `dk ≢ 0 mod 8` for every `d`, so

- `k` odd → needs no `d ≡ 0 mod 8` (4 instants)
- `k = 2, 6` → needs no `d ≡ 0 mod 4` (2 instants)
- `k = 4` → needs every `d` odd (1 instant, the parity law)

**The tower is strictly nested**: `d ≡ 0 mod 8` implies `d ≡ 0 mod 4`, so
half ⟹ quarters ⟹ odd-eighths. The odd-eighths are the *weakest* requirement and therefore
the last to go — a runner losing them has lost the entire eighth-lattice. Verified: in the
`(1..8) → r2 at 9` transition the crashed runner holds no `k/8` at all, for any `k`.

So the spine framing stands, and now for a stated reason rather than by assumption.

## 2. Checked: where does a crashed runner land?

Its windows are not arbitrary. For the crashed runner in that transition, `D = (2,3,4,5,6,7,8)`:

    windows  [1/16, 7/64]  and  [57/64, 15/16]

A mirror pair, and both contain **sixteenths** — the refinement tower of `GRID_TOWER_v1`.

**But that single example does not generalise, and I initially wrote that it did.** Scanning
all 604,224 runner-instances of primitive 8-sets in `[0..18]`, the 2,184 sitting at the floor
of 2 land at these tower levels:

| level `j` | 1 (16ths) | 2 (32nds) | 3 (64ths) | 4 (128ths) |
|---|---|---|---|---|
| runners | 674 | **768** | 716 | 26 |

The majority land **deeper** than sixteenths, and the mode is level 2. So the connection to
the tower holds — a crashed runner is caught by some 2-power refinement, and reserve is
largely those finer lattices — but the level is not fixed at 1. My one worked example was
level 1 and I generalised from it before checking the population.

## 3. Missed: what permutations do  `[VERIFIED — new]`

Every test in the series varied *speeds*. In the coordinates `u_i = π(i) + 8 q_i` that is the
deviation part `q`. The **permutation** part — which residue each deviation attaches to — was
never varied independently, though `WHICH_GRIDS_ISOLATE_v1` §2 names it as half the structure.

It matters, and not marginally. Holding the deviation **multiset** fixed and varying only the
assignment:

| deviation multiset | distinct assignments | min-count range |
|---|---|---|
| one 1, seven 0 | 8 | 4 → 8 |
| two 1s | 28 | 4 → 8 |
| four 1s | 70 | 4 → 10 |
| one 1 and one 2 | 56 | 4 → 10 |
| two 1s and one 2 | 168 | 4 → 14 |
| mixed 1s and 2s | 560 | **4 → 16** |

> **The same deviations, reassigned, swing the floor by up to 4×.**

Worst and best for the single deviation of 1:

    worst  q = (0,0,0,0,0,1,0,0)  ->  (0,1,2,3,4,6,7,13)   count 4
    best   q = (0,0,0,0,0,0,0,1)  ->  (0,1,2,3,4,5,6,15)   count 8

The 1 attached to a **middle** residue is worse than the same 1 attached to the **end**
residue — the same asymmetry as the directional law in `WN_bsm_full_sweeps` §2, now visible
without moving any speed at all.

And the worst assignment of the mixed multiset is

    q = (2,0,1,2,0,1,2,0)  ->  (1,4,7,10,13,16,19,22)   count 4

which is an AP of common difference 3, reducing to `(0,1,2,3,4,5,6,7)` — **the worst
assignment reconstitutes the tight AP**. The permutation does not move away from the
reference; it rebuilds it out of scattered deviations.

## 4. Still untested

- `q` entries beyond `{0,1,2}` in the shape enumeration.
- Moves starting from **non-grid** bases (`k = 1..4`); every base in the series was a grid.
- How `k` itself changes under a move, and whether that predicts the count change.
- The fate of the **reserve** under a move — §1–2 track only the spine.
- A runner colliding with **two** others simultaneously.

## 5. Status

`[PROVED]` §1's nesting (`d ≡ 0 mod 8 ⟹ d ≡ 0 mod 4`) and the per-`k` conditions.
`[VERIFIED — exact]` §1's transition check; §2's window locations; §3's six multisets,
exhaustive over assignments.
`[RECORDED]` §4's five untested directions.

**n = 8 is not proved.**
