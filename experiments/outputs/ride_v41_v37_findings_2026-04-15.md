# ride_v41 — MIAI v37 benchmark findings

**Date:** 2026-04-15
**Script:** `ride_v41_miai_v37_benchmark.py`
**Targets tested:**
- rung0_synth_256B  (256 bytes deterministic-random)
- rung0_synth_1024B (1,024 bytes deterministic-random)
- rung1_text_lrc_synchronized_states_summary.txt_784B (784 bytes text)

3 runs per target.

## Headline

**v37 fails to find a hash-match on 0/3 targets across 9/9 runs.**

v37 is deterministic; `step_count_N = -1` ("not found") replicated exactly across all 3 runs per target, as expected for a deterministic architecture.

## Numeric summary

| target | bytes | digits | traversal length L | N | log2(M) | hash match |
|---|---:|---:|---:|---:|---:|---|
| rung0_synth_256B | 256 | 616 | (not recorded individually) | — | 2,004 | ✗ |
| rung0_synth_1024B | 1,024 | 2,466 | — | — | 8,140 | ✗ |
| rung1_text_…_784B | 784 | 1,888 | — | — | 6,220 | ✗ |

`log2(M)` is the v50 Lehmer-rank lower bound — bits required to address an arbitrary permutation of the multiset.

## Diagnostic (toy 171B text input)

A separate small-scale probe was run to understand *why* no match occurred. Target: 171 bytes of repeated English text → 412 decimal digits.

- multiset of `patched_source` matches target multiset exactly ✓ (K-source + delta layer is correct)
- `build_traversal` produces 272 swaps
- After applying all 272 swaps, **the state is not `sorted(patched_source)`** — the traversal terminates at a partial-sort attractor, not the full sort
- Final state first 20 digits: all zeros. Target digits first 20: `1 8 2 1 8 3 8 1 3 3 2 7 3 0 7 4 8 5 1 2`
- Final-vs-target digit-wise mismatch: 380/412 (92%)

## Mechanism

Inspecting `ride_v37_tsp_directed.py:151-166`:

```python
order = sorted(range(n), key=displacement, reverse=True)
for pos in order:
    src_idx = current_perm[pos]
    dest = src_to_dest[src_idx]
    if pos == dest:
        continue
    target_pos = dest
    other_src = current_perm[target_pos]
    current_perm[pos], current_perm[target_pos] = current_perm[target_pos], current_perm[pos]
    ...
```

`order` is computed **once** from the *initial* displacement values. Each position in `order` is visited in one pass. If a swap at step *k* displaces an element that was already in its correct destination at some later position `pos'`, that re-displacement is **never revisited** — `pos'` was already traversed or is not in `order` with the updated displacement.

Consequence: v37's deterministic path has length O(N) at most, and it does not terminate at the fully-sorted state. The set of states visited is a specific O(N)-length sequence through permutation space.

## Implication for the (θ, k) architecture

The number of permutations of a multiset is `M = N! / ∏ freq_i!`. For the toy 171B input, `log2(M) ≈ 1,220`, so M ≈ 2^1220. v37's path visits ≤ N ≈ 412 states. The fraction of permutation space reachable is `N/M ≈ 2^9 / 2^1220 ≈ 2^-1211` — vanishingly small.

**The Calgary paper4 reported success is therefore a coincidence**: paper4's byte permutation happens to lie on v37's deterministic sort-toward-canonical path. There is no general reachability property. For arbitrary targets — including small synthetic bytes and small text slices — the target does not lie on the path, and no step count `N` matches the hash.

This is a different failure mode from the v30 ~87% wall:
- v30: searches a large seed space; each seed yields a permutation essentially uniformly, hash-match probability 1/M.
- v37: no search — a single deterministic path of length ≤ N. Hash-match probability is approximately N/M, which is worse than random seed search when N < M (which it always is for N > ~20).

## Status against source-of-truth §11 finding 13

Finding 13 states: *"Bounded step-count architecture works at small real-file scale. MIAI v37/v38 achieve bit-perfect round-trip on Calgary paper4 (~13KB) with N ≈ 32,000 TSP-directed steps."*

This finding should be amended: **v37 achieves bit-perfect round-trip on Calgary paper4 specifically. The architecture does not generalise — it has no reachability property beyond its specific deterministic path, and the path reaches a vanishing fraction of permutation space.** Calgary paper4 is a pre-selected demonstration target, not evidence of a scalable architecture.

## Open question raised

**Q11.** What property of Calgary paper4's byte ordering places it on v37's deterministic path? Is it (a) a coincidence specific to paper4, (b) a property of English text with this particular byte-to-digit encoding, or (c) an artefact of the traversal having a short cycle that revisits many common permutations?

Testing: run v37 on multiple text fixtures of similar size. If the hash-match rate across a text corpus is ≥1/corpus_size, there is structure to explain. If it is 0, paper4 was a coincidence.

## Implication for next-session planning

Option (A) "extend v37 directly" is now **falsified as a scalable architecture**. The path is too short and too narrow.

Option (B) "hybridise: v37 as starting ordering, θ-space search on top" is **still alive but requires rethinking**. The natural reframing: v37's deterministic path isn't a base to build on; it's a path whose length needs to *grow* to have a chance of reaching arbitrary targets. Candidate extensions:

- **Multi-pass traversal:** loop the traversal until the state is actually sorted, giving a path of length O(N log N) or more. Still doesn't address arbitrary targets; still O(poly(N)) of 2^log2(M).
- **θ-parameterised starting permutation:** instead of starting from K-canonical sorted, start from a permutation σ(θ) and search over θ such that v37's path from σ(θ) hits the target. This embeds v37 inside a seed-space search — which lands back in v30's failure mode unless θ-space has structure aligned to target structure.
- **Abandon v37-style pathing entirely:** the Lehmer-rank bound says any seed-driven generator with |seed| < log2(M) cannot address arbitrary files. The only escapes are (i) restrict the target class, or (ii) transmit a residual. Both are departures from the current framing.

## Files

- Script: `ride_v41_miai_v37_benchmark.py`
- JSONL: `experiments/outputs/ride_v41_v37_benchmark_20260415T123046.jsonl`
- This file: `experiments/outputs/ride_v41_v37_findings_2026-04-15.md`

## Recommended next action

Update `analysis/encoding/ride_state_2026-04-13.md` §11 finding 13 with a dated amendment noting the above, and add Q11 to Open Questions. Do not proceed to rungs 2/3 with v37 as-is — the rung 1 result already falsifies the scaling claim.
