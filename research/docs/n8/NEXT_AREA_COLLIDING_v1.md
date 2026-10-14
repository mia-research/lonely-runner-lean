# Status of "how isolation is achieved and by which runners", and the next area

## 1. Direct answer: half-resolved, with a sharp boundary

**Resolved — completely, for every arrangement, at the grid instants.**

| | |
|---|---|
| the neighbour is a function of the offsets alone | `[PROVED]` `GridNeighbour.gridPos_congr` |
| whole-lap deformation moves it never | `[PROVED]` `laps_invisible`, `neighbour_laps_invisible` |
| residue deformation moves it by `±p` | `[PROVED]` algebra, `[EMPIRICAL]` 12,800/12,800 |
| offsets sharing a factor with 8 can never bind | `[PROVED]` `slot_gcd`, `even_offset_caged` |
| exact perturbation budget per offset | `[PROVED]` `min(d,8−d)−1` at `p=1` |

That covers the **49.7%** of subjects with a unique residue, who are lonely at `t = 1/(8g)` with
zero cascade moves.

**Not resolved for the other 50.3%** — the *colliding* subjects, who fail every grid instant. There
the neighbour is 10.4% residue-determined against a 1.9% null, and depth sits on the forced floor
for both `π` and `q`. This is §2.3's open item.

## 2. The next area is therefore the colliding subjects — and there is a lead

Colliding disparities are **19.2%** of a colliding subject's pack, but:

```
  P(ever blocks | colliding)      0.5778      vs  0.3237 non-colliding
  share of SETTER events          0.3128      vs  baseline 0.1921
  share of the FINAL setter       0.2727      vs  baseline 0.1921
```

**The signal survives controlling for size**, which was the obvious confound — `d = 8bg` forces
colliding disparities to be large. Compared at the same size rank within the subject's own pack:

```
  rank      1     2     3     4     5     6        pooled
  ratio   2.64  2.05  1.77  1.57  1.39  1.38        1.93
```

Above 1 at every rank, and strongest for the *smallest* colliding disparities. So it is a residue
effect, not a size effect. `[EMPIRICAL]`, 6,370 colliding subjects with depth ≥ 1.

## 3. The mechanism is exact, not statistical

A cascade scale is `D = c·g/(8N+1)`, so a blocker `a·g` has reading `s = a(8N+1)/c` and blocks when
`|s − 8M| < 1`. If the reading is *exactly* `8M` then `8 ∣ a(8N+1)`, and `8N+1` is odd, so:

> **`ExactBlock.exact_block_is_colliding` — an exact block is always a colliding disparity.**

`experiments/n8/ExactBlock_v1.lean`, 3 theorems, zero `sorry`, axioms `[propext, Quot.sound]` (no
choice). Measured: **81.3%** of colliding blocking events are exact; non-colliding blocks are exact
**0 of 12,152** — and that zero is the theorem, not the sample.

An exact block means `d·t = M` exactly: the blocker is *coincident* with the subject, the maximal
violation. And it makes the next move closed-form — `k = M`, so `t' = (M + 1/8)/d`, with no choice
to make.

## 4. The concrete next question

Colliding disparities drive 31.3% of setter events, and do so by exact coincidence 81.3% of the
time, where the next scale is forced. So:

> **Is the cascade's trajectory on a colliding subject determined by its exact-coincidence events?**

Testable as stated: replay each colliding subject's cascade, mark which moves were exact, and ask
whether the exact moves alone reconstruct the final scale. If they do, the colliding region has a
closed-form skeleton with the near-misses as corrections. If they do not, that is a clean negative
and the 81.3% is a description rather than a mechanism.

Two guards for that test, both from failures already recorded this session:
1. **Compute the forced floor before interpreting any agreement rate** — the depth figures looked
   like weak positives at 0.40 until the floor came back 0.3758.
2. **Control the confound before believing the signal** — §2's 1.93× is only meaningful because the
   size control was run first; unconditioned it was 31.3% vs 19.2% and could have been entirely size.

## 5. What is not claimed

No proof at order 8. §3 characterises *how* colliding disparities act; it does not bound depth, and
`NEIGHBOUR_DEFORMATION_v2` §6 measured depth as determined by neither `π` nor `q`. §2's percentages
are sampler frequencies (speeds `1..89`, 2,500 arrangements). Nothing here touches the firewall
question left open in `BS_TRANSFER_v1` §4.

```bash
cd LonelyRunner && lake env lean ../experiments/n8/ExactBlock_v1.lean
python3 experiments/n8/colliding_setters_v1.py     # setter and final-setter shares
python3 experiments/n8/colliding_setters_v2.py     # the size control
python3 experiments/n8/colliding_mechanism_v1.py   # 81.3% exact vs 0 of 12,152
```
