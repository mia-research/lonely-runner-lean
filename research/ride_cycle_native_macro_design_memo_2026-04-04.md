# RIDE Cycle-Native Macro Design Memo

**Date:** 2026-04-04
**Status:** Working memo before the next encoder/decoder pass

## Objective

Preserve the correct architecture before building the next RIDE prototype:

- treat the entire file or archive as one object
- derive the actual K source first
- let the encoder do the hard route-finding work
- let the decoder replay a shared deterministic route cheaply
- replace explicit permutation payloads with a compact cycle-native recipe

## Non-Negotiables

### 1. Whole file, not chunks

The file is one number, one target, one reconstruction problem.

What we are **not** doing:

- slicing the corpus into 1 KB pieces
- building separate local permutation maps
- sending per-block reorder data

### 2. This is generative reconstruction, not Shannon compression

The packet is a recipe that materialises the file. "Compression ratio" is only a benchmark for comparison. The theory frame here is Kolmogorov-style description length, not entropy coding.

### 3. Start from the actual K constant

The starting object must be the actual K source or actual-K manifold representative for the whole file, not a synthetic sorted base or synthetic balanced base.

Relevant probes:

- `ride_v11_actual_kconstant.py`
- `ride_v12_kmanifold_probe.py`

### 4. Encoder/decoder asymmetry is allowed

The encoder may do expensive analysis to find the route. The decoder should not rediscover the route. It should replay a known deterministic family from a compact address and verify with the hash.

Target packet shape remains conceptually:

- `K coords`
- `hash`
- `deterministic perturbation address / step count`
- tiny delta layer only if strictly necessary

## What The Experiments Established

### Actual-K manifold is real and close

`ride_v12_kmanifold_probe.py` showed that the actual K manifold database is the right base object, and that whole-file targets can lie very close to it in multiset terms.

For `cantrbry.zip`, the nearest actual-K source covered almost the entire digit multiset. The remaining frequency mismatch was small compared with the full file size. This means the hard part is overwhelmingly the ordering layer, not the K-source layer.

### The naive whole-file orbit model has the right packet shape but the wrong family

`ride_v16_whole_file_orbit_steps.py` used:

- actual K source
- whole-file delta patch
- a single shared perturbation orbit
- `steps` as the address

This is the correct **shape** of the recipe, but the tested orbit family was wrong. Searching around the exact mile did not hit the real JPEG or Canterbury archive.

### The real reduction lives on the cycle manifold

`ride_v18_cycle_rsn.py` is the most important current result.

It showed that real whole-file permutations collapse into a tiny number of huge stressed cycles:

- `palelei_reconstructed.jpeg`: mile `156,687`, only `13` non-trivial cycles
- `cantrbry.zip`: mile `1,590,652`, only `16` non-trivial cycles

The encoder can derive an exact route quickly from that structure, and replay verifies bit-perfectly. This is the real RSN/TSP-style reduction for the ordering layer.

### Hash-only shared pivot families are not enough

`ride_v19_pivot_cycle_orbit.py` tried to make the decoder recover the route family from `K + hash` alone.

It failed on the real files because the shared pivots did not line up with the encoder-side stressed-cycle pivots:

- JPEG pivot overlap: `1 / 13`
- Canterbury pivot overlap: `0 / 16`

Conclusion: the useful route family is not recoverable from hash-derived pivots alone.

### Contiguous macros are the wrong language

Two macro systems were tested and falsified on real files:

- `ride_v20_macro_micro_rsn.py`: equal-length block swaps
- `ride_v21_block_move_rsn.py`: cut-and-insert contiguous block moves

Both produced:

- `0` useful macro ops on the JPEG
- `0` useful macro ops on Canterbury

The encoder fell all the way back to single swaps. That means the structure is not living in contiguous segments.

## What This Means

The ordering problem is **not**:

- arbitrary permutation search
- contiguous block editing
- hash-seeded random orbit walking

The ordering problem **is**:

- a small set of very large stressed cycles
- with strong encoder-visible structure
- that still lacks the right compact shared macro language

So the next layer must be cycle-native.

## The Next Macro Language To Build

The next prototype should work directly on the exact stressed cycles from `ride_v18_cycle_rsn.py`.

Promising macro candidates:

### 1. Cycle-Arc Extraction

Treat a stressed cycle as a circular object. Encode a move that extracts a long arc from the cycle and reattaches it at a deterministic pivot.

Why it may help:

- one macro can resolve many non-local displacements
- description can be compact if the pivot rule is shared
- it matches the cycle geometry better than contiguous block moves

### 2. Pivot-Star Chunk Move

Choose a deterministic cycle pivot, then express the route as moves of chunks toward or away from that pivot.

Why it may help:

- the encoder already identifies stressed pivots
- many misplacements may be describable relative to a shared anchor
- the decoder can replay if the pivot rule is part of the family

### 3. Cycle Segment Grammar

Treat each stressed cycle as a sequence of reusable segment productions rather than a flat list of swaps.

Why it may help:

- cycles may admit a compact grammar even when contiguous blocks fail
- the recipe becomes "how to generate the cycle correction" rather than "list every correction"

## Guardrails For The Next Build

The next implementation should **not**:

- fall back to explicit permutation maps
- slice the file into subproblems
- reintroduce sorted or balanced synthetic bases as the main source object
- confuse exact mile analysis with the final address format

The next implementation **should**:

- begin from actual-K manifold materialisation
- keep the whole-file target intact
- use encoder-side stressed-cycle analysis as the source of truth
- compile those cycles into a decoder-known macro family
- make the address mean "replay this shared cycle-native family for step `n`" or equivalent

## Immediate Build Plan

### Phase 1. Extract cycle-native primitives

From the exact cycle plans in `ride_v18_cycle_rsn.py`, measure:

- arc spans
- pivot recurrence
- segment reuse
- cycle-local regularities that survive across files

### Phase 2. Define one shared family

Pick one cycle-native family only. Do not mix multiple fallback encodings in the first pass.

Candidate first family:

- pivot-star arc family with deterministic pivot selection and arc ordering

### Phase 3. Compile exact routes into that family

The encoder should take the exact cycle plan and attempt to express it purely in the shared macro family. If this fails, the failure should be measured, not hidden by falling back to a full permutation payload.

### Phase 4. Decoder replay

The decoder must reconstruct the same family from shared information and replay the compact address directly, then verify with the hash.

## Success Criterion

The next pass is successful if:

- the route is still whole-file and exact
- the decoder replays from shared family logic, not an explicit permutation map
- at least some real files show non-trivial macro usage on the cycle manifold

That would be the first real evidence that the route itself is becoming recipe-sized.
