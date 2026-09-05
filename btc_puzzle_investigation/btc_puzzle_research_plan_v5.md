# BTC Puzzle — Research Plan v5 (curve-only frontier)

Date: 2026-07-08. Narrows v4 after a decision reached with the user.

## Decision: the integer-selection avenue is a dead end. Test the curve only.

Two independent reasons close every test that asks *how the key integers were
chosen*:

1. **Not enough real data.** Only 82 solved keys exist, sparse (milestones
   #65,70,…,130 + small ones), not a dense consecutive run. That is far below
   what any generator-recovery needs (e.g. MT19937 wants ≥624 consecutive full
   words). No statistic on 82 points has the power to pin a selection process.
2. **Manual selection leaves nothing to find.** If the creator picked keys by
   hand (or from an unknown/one-off process), there is no algorithmic structure
   to recover even in principle — the premise of a PRNG/lattice attack fails.

So the following are **closed** (done + nulled, or structurally hopeless):
- Test E (cross-key PRNG state) — nulled for linear/LCG class; MT unprovable on
  82 sparse keys.
- Test F bias-probe — GLV degenerates to `(d,0)` for `d<2^128`; 81/82 keys are
  below it. Vacuous at these magnitudes, not fixable by more data.
- The whole `(n,k,D)` / `D_terms` / weak-seed / `prng_*` family — all
  integer-selection tests, already nulled in prior sessions.

The 100k synthetic set stays useful only as a **same-method null** (uniform-in-
range, verified: `generate_dataset.py:69` `lo+_r.randrange(span)`) for curve
tests — not as a target.

## Why curve-only is the worthwhile frontier

Curve-structure tests probe intrinsic properties of secp256k1 (point
distribution, group-operation mixing, graph structure). They do **not** depend on
the puzzle keys at all, so they have **unlimited data** — generate as many points
as compute allows — and any positive result would be a real cryptographic finding
that scales, not an artifact of 82 samples.

## The curve-only battery

| # | test | status | data source |
|---|---|---|---|
| A | ladder / double-and-add bit leakage | **NULL** (uniform-Rprev control) | generated |
| C | isogeny / twist (prime order ⇒ no descent) | **NULL** | curve constants |
| B | sum-product energy of point coordinates | running (null so far) | 100k / generated points |
| K | DP-coordinate uniformity (`X mod m`, increments) vs matched random `rG` | TODO | kangaroo run / generated |
| D | near / multi-collision information in kangaroo walks | TODO | instrumented pool run |
| G | DP-table percolation / density threshold | TODO | instrumented pool run |
| H | ladder / Cayley graph classical hitting time vs expander/glued-tree | TODO | small-scale graph |
| J | jump-size selection MCMC mixing (constant-factor only) | TODO | pool run |
| I | Coppersmith threshold (partial-info back-end) | support only | small-N |

All verdicts by exact integer statistic + matched null + scaling
(`power_scaling.py` discipline). A curve test that shows structure scales to the
real problem; a null is a clean, bounded curve fact.

## Next
Run the curve-structure battery. K, D, G, J all harvest from **one instrumented
kangaroo/pool run** — build that instrumentation once, pull all four. H is a
standalone small-scale graph experiment. Record each in `struct_test_results.md`.
