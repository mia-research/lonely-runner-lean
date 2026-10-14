# The d_min rule — does it survive three movers, and a non-AP base?

2026-09-13. n = 8, individual isolation, threshold 1/8. Tests the two open items left by
`TWO_MOVER_PREDICTION_v1` §6.

Rule under test: a runner's first isolation is at `t* = 1/(8 · d_min)`, `d_min` its smallest
speed difference. The **bound** `t* ≥ 1/(8 · d_min)` is forced for every runner in every
configuration — the runner starts at gap 0 from its nearest neighbour. Only **attainment** is at
issue.

Artifact: `experiments/n8/ok_dmin_rule_test_v1.py`.

---

## 1. Three movers: the rule survives exactly  `[VERIFIED — 5,380 of 5,380]`

AP base, three runners displaced together, step 0.25, five triples
`(1,2,3) (1,4,7) (2,4,6) (3,4,5) (1,2,8)`, ordering kept strict.

| | cases | attain `1/(8·d_min)` | rate |
|---|---|---|---|
| disturbed by **no** mover | 5,380 | 5,380 | **1.0000** |
| disturbed by at least one | 6,660 | 3,626 | 0.5444 |

Identical in form to the two-mover result (42,092 of 42,092 and 0.4812). Adding a third mover
changes nothing about the undisturbed runners.

## 2. Non-AP bases: it holds on regular bases and breaks on irregular ones  `[VERIFIED]`

One mover, step 0.1, each runner transited across its neighbour interval.

| base | `d_min` per runner | undisturbed | disturbed |
|---|---|---|---|
| AP `1..8` | `1,1,1,1,1,1,1,1` | **1.0000** | 0.4812 |
| AP step 2 `1,3,…,15` | `2,2,2,2,2,2,2,2` | **1.0000** | 0.4409 |
| spread grid `1..7,16` | `1,1,1,1,1,1,1,9` | 0.9991 | 0.4387 |
| random `2,5,9,14,20,27,35,44` | `3,3,4,5,6,7,8,9` | **0.7206** | 0.4315 |
| primes `3,5,7,11,13,17,19,23` | `2,2,2,2,2,2,2,4` | **0.6764** | 0.4305 |

**The rule is not general.** It breaks on the two irregular bases even for runners no mover
touches.

## 3. Why — and the exact condition  `[PROVED — arithmetic]`

At `t = 1/(8 · d_min)` the nearest neighbour sits exactly on the threshold. **Any other
difference can still block it.** For difference `d`, the runner needs `‖d · t‖ ≥ 1/8`, so

> **the bound is attained iff `‖ d / (8 · d_min) ‖ ≥ 1/8` for every other difference `d`.**

Worked through the bases:

| base | runner | `d_min` | bound | actual | blocked by |
|---|---|---|---|---|---|
| AP | every one | 1 | `1/8` | `1/8` | — |
| primes | r1 | 2 | `1/16` | `9/112` | difference **16** |
| primes | r3 | 2 | `1/16` | `9/128` | difference **16** |
| primes | r7 | 2 | `1/16` | `3/32` | difference **16** |
| random | r1 | 3 | `1/24` | `17/264` | difference **25** |
| random | r2 | 3 | `1/24` | `17/312` | difference **22** |
| random | r3 | 4 | `1/32` | `9/280` | difference **35** |

For the primes base, `d = 16` against `d_min = 2` gives `d/d_min = 8 ≡ 0 mod 8`, so
`‖16/16‖ = 0` and the runner is blocked at its own bound.

**Why the AP never blocks.** Its differences are `1,…,7` and `d_min = 1`, so `t = 1/8` and every
other difference gives `‖d/8‖ = min(d, 8−d)/8 ≥ 1/8`, because no `d` in `1..7` is `≡ 0 mod 8`.
The same holds for the AP of step 2, where `d/d_min` again runs over `1..7`. This is the
eighth-lattice nesting of `CONCLUSIONS_2026_09_12` §2(3) reappearing: the spine survives exactly
when no difference is divisible by 8.

So the rule's reach is not "AP versus non-AP". It is **whether the runner's differences, divided
by its own `d_min`, avoid multiples of 8** — which the AP and its dilates satisfy by
construction, and an irregular set does not.

## 4. What this settles

- **Three movers:** no change; the rule is exact on undisturbed runners.
- **Non-AP base:** the rule fails, and the failure has a stated criterion rather than being a
  scope caveat. The assumption doing the work was never "`d_min = 1`" — it was that every other
  difference clears the threshold at `t = 1/(8·d_min)`.
- **Disturbed runners stay unpredicted** at 0.43–0.54 across every base and every mover count.
  That number is remarkably stable and nothing here explains it.

## 5. Status and scope

`[VERIFIED — exact]` §1's two rates; §2's five bases; §3's blocking table.
`[PROVED — arithmetic]` the bound, and §3's attainment criterion.

**Scope.** Three-mover test is five triples at step 0.25 on the AP base only. Non-AP test is four
bases, one mover, step 0.1. No test of three movers on a non-AP base, and none of four or more
movers.

**Not established.** Why the disturbed-runner attainment rate sits near one half in every
population tested. Whether the §3 criterion, which is checkable in `O(n)` per runner, predicts
attainment for *disturbed* runners too — it is stated here only for the undisturbed case.

**n = 8 is not proved here, and is not the target here.**
