# MT19937 GF(2) Reduction — Results v1 (2026-07-13)

**Question (lateral, per user).** Not "recover the MT state" (data-gated) but:
*do the solved puzzle keys linearly CONSTRAIN an unsolved key at all, and by how
many bits?* Any reduction of the search space for k is a win.

**Instrument.** `mt19937_gf2_reduction_v1.py`. Symbolic MT19937: every output bit
carried as an exact GF(2) bitmask over the 19968 state unknowns (MT output is
linear in the state). Pipeline model = the MT hypothesis: `key_i =
getrandbits(i-1) | (1<<(i-1))`, strict index order (on-chain funding tx confirms
order). Build the GF(2) row space from solved keys 1..K; for a held-out target,
count how many of its bits lie in that span (= bits determined = search reduction).

**Validation.** Symbolic `getrandbits` reproduces CPython `random.getrandbits`
bit-for-bit for keys 1..40 (seed 20260713). Two positive controls fire:
- **low-entropy seed** (state = function of 64 bits): rank saturates at 63; targets
  #71/#100/#160 fully determined (70/99/159 bits, 2^70–2^159×). Instrument detects
  total cross-constraint.
- **twist-crossing** (solved 1..190, past the horizon): target #191 → 115 bits
  determined, #200 → 130 bits. Post-twist mixing does create reduction.

## Main result (full-entropy seed, the real hypothesis)
| solved keys | observed bits | GF(2) rank | reduction on any unsolved key ≤#160 |
|---|---|---|---|
| 1..70  | 2415  | 2415 (full) | **0 bits** |
| 1..130 | 8385  | 8385 (full) | **0 bits** |
| 1..160 | 12720 | 12720 (full)| **0 bits** |

Rank equals observed bits exactly at every K → the observed outputs are perfectly
linearly **independent**, and every held-out key (71, 75, 80, 100, 130, 135, 160)
gets **0 bits determined**.

## Why — the structural reason (not just "not enough data")
MT twists at stream start, then every 624 words. The **entire puzzle range (≤#160)
lives inside the first post-twist block** (cumulative getrandbits words to #160
≈ 400 < 624). Within one twist block the 624 words are distinct invertible linear
combos of the seeded state, so reading distinct words yields independent bits and
**no key shares unknowns with any other**. The *second* twist — which folds the
observed block's span back into new words and is the first point where solved keys
could constrain a later one — is reached only at ~**puzzle #185**, beyond the whole
puzzle range.

**Conclusion.** Under the stock-CPython MT19937 hypothesis with a full-entropy
seed, solving *every* puzzle up to #160 yields **exactly 0 bits** of linear
reduction on any remaining key. This is not a data-budget shortfall you could fix
with more solved keys inside the range — it is structural: the puzzle range ends
before the MT twist horizon, so the keys are linearly decoupled by construction.

The only regimes with nonzero reduction (both delineated by the controls):
- a **low-entropy seed** (≤ a few words) → total determination — already excluded
  by prior small-seed searches (reset battery, null);
- **contiguous keys past ~#185** → real reduction (115+ bits) — but the puzzles
  stop at #160.

## What this does NOT close
- The hypothesis that the generator is *stock MT19937 in this exact pipeline* is
  assumed, not proven (it is the leading model: BM complexity ≈L/2 excludes LFSR;
  named LCGs width-excluded; MWC recipes ruled out). A different width convention
  (e.g. `randrange` rejection sampling) shifts word alignment but not the
  twist-horizon conclusion (still ~400 words to #160).
- Non-linear or re-seeded generators are out of scope of a GF(2) instrument.
