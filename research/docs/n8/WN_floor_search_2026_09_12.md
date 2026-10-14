# Working note — floor search result (resolves `WN_grid_distance_2026_09_12` §5)

2026-09-12. Script `experiments/n8/ok_worst_config_v1.py` + inline adversarial runs.
Exact `Fraction`, BSM good sets. Completes the search that was still running when
`WN_grid_distance_2026_09_12.md` was written; that note's §5 listed it as pending.

---

## Result

Smallest isolation event count found for any runner:

| population | configs | lowest count |
|---|---|---|
| exhaustive `[1..22]`, primitive | 319,605 | **2** |
| near-AP adversaries (AP with 1–3 speeds randomised to `[1..60]`) | 48,745 | **2** |
| random `[1..500]`, primitive | 29,894 | **36** |

Configurations attaining 2 in `[1..22]`: `(1,2,3,4,5,6,7,9)`, `(1,2,3,4,5,6,8,9)` (two
runners at 2), `(1,2,3,4,5,6,8,16)`, `(1,2,3,4,5,6,8,17)`. The near-AP adversary attaining 2
is `(1,3,4,5,6,7,8,17)` with counts `[2,8,10,10,10,12,6,10]`.

Zero never occurs in any population — a zero would be an LRC(8) counterexample.

## The third row

The random `[1..500]` minimum is **36**, not 2: `(278,336,347,351,369,374,393,395)` with counts
`[114,60,46,36,40,36,58,54]`. Low counts are a small-speed, near-AP phenomenon; configurations
drawn at random from a wide box are an order of magnitude clear of the floor.

## Status of the pending items from `WN_grid_distance_2026_09_12` §5

- *Wider floor search* — done. Floor of 2 now covers exhaustive `[1..16]`, `[1..20]`,
  `[1..22]`, plus 48,745 targeted near-AP adversaries. Still a box statement, not a bound.
- *Can a runner have exactly 1 event* — still **not found and not excluded**. Nothing below 2
  appeared in any of the three populations.
- *Stability of the `k = 0` and `k = 5` floors of 4* — not addressed here.

`n = 8` is **not proved.**
