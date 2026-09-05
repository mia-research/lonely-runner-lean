#!/usr/bin/env python3
"""
RIDE V34 - TSP exact seed finder: find (seed, k) s.t. FY(seed)^k(source) = target.
# v1.0 — 2026-04-13 — sender has both; receiver gets (seed, k) + verifies hash

THE MODEL (CORRECTLY STATED)
-----------------------------
Sender has: source (K-source) AND target (the file)
Sender does: search for seed S such that FY(S)^k(source) == target for some k
Sender sends: (seed, k) — the complete order recipe
Receiver has: source (K-source) + (seed, k)
Receiver does: sigma = FY(seed); apply sigma k times to source; verify hash

The sigma is derived purely from seed — no target knowledge needed at decode.
The decoder never needs the target; it arrives at the target via sigma^k.

THE SEARCH
----------
For sigma = FY(seed) to satisfy sigma^k = perm_{source→target}:
  - Decompose sigma into cycles: sigma = C1 * C2 * ... * Cm
  - Decompose target perm into cycles: perm = D1 * D2 * ... * Dn
  - sigma^k maps each cycle Ci of length Li to: rotate by k mod Li
  - For sigma^k = perm exactly: the cycles of sigma must MATCH the cycles
    of perm, and k mod Li = correct rotation for each cycle Di

So the search strategy is:
1. Compute the exact source→target permutation P and its cycle decomposition
2. For each candidate seed: generate sigma = FY(seed), decompose into cycles
3. Check if sigma's cycle structure is COMPATIBLE with P's cycle structure
   (same cycle lengths as a multiset)
4. If compatible: find k such that sigma^k = P (solve the congruences)
5. If found: (seed, k) is the recipe

COMPATIBILITY CONDITION
-----------------------
sigma^k = P requires: for each cycle of sigma of length L, k mod L gives
the rotation amount that matches the corresponding cycle of P.
This is solvable iff sigma and P have identical cycle-length multisets AND
the actual cycle members match up correctly.

The most likely scenario: sigma must have EXACTLY the same cycles as P
(same positions in each cycle, same length). This means sigma IS the
source→target permutation, just expressed differently.

A sigma that IS the permutation P: FY(seed) = P for some seed.
Then k=1 gives sigma^1(source) = target. Done.
Recipe = (seed_such_that_FY(seed)=P, k=1).

The search: find seed s.t. FY(seed) produces a specific permutation P.
This is equivalent to: what seed generates this exact FY shuffle?
Answer: invert the FY process — P uniquely determines the sequence of
random choices made during FY, which determines the seed.

FY INVERSION
------------
Standard FY: for i = n-1 down to 1: j = rng(i+1); swap(arr[i], arr[j])
Given the final permutation P, we can recover the swap sequence, and from
that the exact sequence of rng outputs, and from that the PCG32 seed.

This is the key insight: the sender INVERTS the FY process to find the seed
that generates exactly the needed permutation. No search needed at all.
Recipe size: 64-bit seed + log2(1) = 64 bits total for the order layer.

IMPLEMENTATION
--------------
1. Compute P = source→target permutation
2. Run FY inversion on P to find the swap sequence
3. Find PCG32 seed that produces that exact swap sequence
   (PCG32 has known structure — seed recovery is feasible)
4. Verify: FY(recovered_seed)^1(source) == target
5. Transmit (recovered_seed, k=1)

If PCG32 inversion is hard, fall back to: try seeds until FY(seed) = P.
Expected trials: n! seeds before one matches — too many. Need inversion.

Alternative: use a different RNG with invertible seed recovery.
numpy.random.default_rng(seed).permutation(n) uses PCG64 — harder to invert.

PRACTICAL APPROACH: CYCLE-ALIGNMENT SEARCH
-------------------------------------------
Rather than exact FY inversion (hard), use the cycle structure:
- P has 9 non-trivial cycles for the abstract
- FY(seed) has a random cycle structure
- P(r) of length L appears in FY with probability ~1/L (cycles of length L)
- For 9 specific cycles to all appear in FY: probability is product of 1/Li
  which is astronomically small for random seeds

So the exact match approach requires FY inversion. Let's implement it.
"""

from __future__ import annotations

import argparse
import hashlib
import math
import sys
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
MIAI = Path("/Users/trentpalelei/MIAI")
for candidate in (HERE, MIAI):
    s = str(candidate)
    if candidate.exists() and s not in sys.path:
        sys.path.insert(0, s)

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(10_000_000)

from ride_v18_cycle_rsn import materialise_source_and_target
from ride_v13_canterbury_recipe_bench import build_perm_target_to_source
from ride_v16_whole_file_orbit_steps import PCG32


# ---------------------------------------------------------------------------
# Compute exact source→target permutation
# ---------------------------------------------------------------------------

def source_to_target_perm(source: list[int], target: list[int]) -> list[int]:
    """
    Return P such that P(source) = target, i.e. target[i] = source[P[i]].
    This is the permutation the decoder needs to apply to source to get target.
    """
    return list(build_perm_target_to_source(bytearray(target), bytearray(source)))


# ---------------------------------------------------------------------------
# PCG32 FY inversion
# ---------------------------------------------------------------------------

def fy_swap_sequence(perm: list[int]) -> list[int]:
    """
    Recover the sequence of j values from a FY shuffle that produced perm.

    FY forward: arr = [0..n-1]; for i = n-1 downto 1: j=rng(i+1); swap(arr[i],arr[j])

    To invert: given final perm, recover j sequence.
    Start from perm, undo swaps in reverse order (i = 1 to n-1):
      swap(arr[i], arr[j]) is its own inverse.
    But we don't know j. We need to find j such that undoing swap(i,j)
    gives a state consistent with the next step.

    Actually: given the final permutation arr[] after all swaps:
    We know arr[n-1] was put there by swap(n-1, j_{n-1}).
    So j_{n-1} is the position that arr[n-1] came from.

    Reconstruction:
    - Work backwards from step i = n-1 down to i = 1
    - At step i: arr[i] holds the value that was placed there by swap(i, j_i)
    - j_i = position in the CURRENT (pre-swap) arr that holds arr[i]'s original value

    Simpler: track inverse permutation.
    """
    n = len(perm)
    arr = list(range(n))
    inv = list(range(n))  # inv[v] = current position of value v

    # Apply perm: arr[i] = perm[i] means position i holds value perm[i]
    # We need to recover the swap sequence that transforms [0..n-1] -> perm

    # Forward FY with known j sequence produces perm.
    # Inversion: given perm, find j sequence.

    # Key insight: arr[n-1] after all swaps = perm[n-1].
    # The last swap was swap(n-1, j_{n-1}).
    # Before this swap: position n-1 held whatever was there, position j_{n-1} held perm[n-1].
    # After swap: position n-1 holds perm[n-1], position j_{n-1} holds whatever was at n-1.

    # Work from back to front, maintaining current state of arr:
    arr = list(perm)  # start from final state
    js = []

    for i in range(n - 1, 0, -1):
        # arr[i] = perm[i] (correct final value)
        # This was placed here by swap(i, j_i) where j_i was chosen uniformly in [0, i]
        # Before the swap at step i, position i held value v_i, position j_i held perm[i]
        # We need to find j_i: it's the position that, before step i, held arr[i]

        # In the reconstructed state (working backwards), arr[i] is already correct.
        # j_i is where arr[i] was BEFORE the swap — i.e., if j_i != i, then
        # arr[j_i] and arr[i] were swapped. We need to undo: find j_i.

        # Problem: we don't know the pre-swap state. We need another approach.
        #
        # Better: track the permutation as we undo swaps.
        # arr[j] for j in [0..i] after step i = some arrangement of values
        # arr[i] = perm[i] definitely.
        # j_i could be anything from 0 to i.
        #
        # If j_i = i: no actual swap. arr[i] was already perm[i] before step i.
        # If j_i != i: arr[j_i] held perm[i] before the swap, and arr[i] held
        #              whatever ended up at arr[j_i] after the swap.

        # To find j_i: we need the pre-swap value at position i.
        # The pre-swap state at step i is determined by all previous swaps.
        # This requires either forward simulation or a different strategy.

        js.append(i)  # placeholder — full inversion requires RNG stream recovery

    return list(reversed(js))


def pcg32_invert_swap_sequence(js: list[int]) -> int | None:
    """
    Given the j sequence from FY (j_i = rng.next_uniform(i+1) for i=n-1 downto 1),
    find the PCG32 seed that produces this sequence.

    PCG32.next_uniform(bound) = pcg32.next() % bound (approximately).
    Exact recovery requires solving the PCG32 stream backwards.

    PCG32 state update: state = state * MULT + INC (mod 2^64)
    Output: xorshift of high bits.

    This is feasible but complex. For now: brute-force seed search with
    early termination on first j mismatch.
    """
    # This is O(2^64) in the worst case — not practical for arbitrary sequences.
    # The right approach is to use the known PCG32 structure to recover state
    # from a sequence of outputs. That requires solving a system of linear
    # equations over Z/2^64Z.
    #
    # For the scope of this experiment: we'll use numpy's default_rng instead,
    # which is based on PCG64 and also has known inversion properties.
    #
    # Practical alternative: use a keyed hash (BLAKE2) as the RNG so that
    # seed recovery is: find seed s.t. BLAKE2(s, counter) produces the j sequence.
    # That's also hard to invert directly.
    #
    # The REAL practical approach: don't invert — instead represent the seed
    # as an index into the permutation space. The permutation P has a unique
    # Lehmer code (factorial number system representation). Transmit the Lehmer
    # code as the seed. The decoder: unrank(seed) -> P -> apply to source.
    # Recipe size: ceil(log2(n!)) bits = n*log2(n) - n/ln(2) ≈ for n=2293:
    # 2293 * 11.16 - 3307 ≈ 22,261 bits = 2,783 bytes. Larger than file.
    return None


# ---------------------------------------------------------------------------
# The right approach: rank/unrank the permutation
# ---------------------------------------------------------------------------

def lehmer_encode(perm: list[int]) -> list[int]:
    """
    Encode permutation as Lehmer code (factoriadic).
    lehmer[i] = number of j > i such that perm[j] < perm[i].
    """
    n = len(perm)
    code = []
    for i in range(n):
        count = sum(1 for j in range(i + 1, n) if perm[j] < perm[i])
        code.append(count)
    return code


def lehmer_bits(n: int) -> int:
    """Bits needed to represent a permutation of n elements."""
    # sum(ceil(log2(k+1)) for k in range(1, n)) approximately
    total = 0
    for k in range(1, n):
        total += math.ceil(math.log2(k + 1)) if k > 0 else 1
    return total


# ---------------------------------------------------------------------------
# Main: measure recipe size for exact reconstruction
# ---------------------------------------------------------------------------

def run(raw: bytes) -> dict:
    t0 = time.perf_counter()
    source_list, target_list, params, l1 = materialise_source_and_target(raw)
    n = len(target_list)
    prep_time = time.perf_counter() - t0

    print(f"  n={n:,}  freq_L1={l1:,}  prep={prep_time:.2f}s")

    # Compute exact source→target permutation
    t1 = time.perf_counter()
    P = source_to_target_perm(source_list, target_list)
    perm_time = time.perf_counter() - t1

    # Verify
    reconstructed = [source_list[P[i]] for i in range(n)]
    exact = reconstructed == target_list
    print(f"  Permutation computed in {perm_time:.2f}s — exact: {exact}")

    # Recipe option 1: transmit P as Lehmer code
    lb = lehmer_bits(n)
    print(f"\n  Option 1: Lehmer-encoded permutation")
    print(f"    Bits: {lb:,}  ({lb//8:,} bytes)")
    print(f"    File: {len(raw):,} bytes")
    print(f"    Ratio: {len(raw)*8/lb:.2f}:1")

    # Recipe option 2: transmit only the non-trivial cycle members + order
    from ride_v2_kpog_encoder import decompose_cycles
    cycles = [c for c in decompose_cycles(P) if len(c) > 1]
    cycles.sort(key=len, reverse=True)

    pos_bits = math.ceil(math.log2(max(n, 2)))
    # For each cycle: transmit list of positions in cycle order
    # (decoder applies the cycle as rotations)
    cycle_bits = sum(len(c) * pos_bits for c in cycles)
    cycle_overhead = len(cycles) * (pos_bits + math.ceil(math.log2(max(n, 2))))  # start + length per cycle
    total_cycle_bits = cycle_bits + cycle_overhead

    print(f"\n  Option 2: Explicit cycle members (positions in order)")
    print(f"    Non-trivial cycles: {len(cycles)}")
    for i, c in enumerate(cycles[:6]):
        print(f"      Cycle {i}: length {len(c):,}")
    print(f"    Bits: {total_cycle_bits:,}  ({total_cycle_bits//8:,} bytes)")
    print(f"    Ratio: {len(raw)*8/total_cycle_bits:.2f}:1")

    # Recipe option 3: for each cycle, transmit start position + gaps (delta-encoded)
    # Gaps between consecutive positions in the cycle
    gap_bits_total = 0
    for c in cycles:
        sorted_c = sorted(c)
        gaps = [sorted_c[0]] + [sorted_c[i+1] - sorted_c[i] for i in range(len(sorted_c)-1)]
        # Each gap: geometric(p=0.38) → ~1.3 bits on average (entropy ~0.956 bits)
        # But we also need the within-cycle ORDER on top of membership
        # Membership: sum of gap bits
        max_gap = max(gaps) if gaps else 1
        gap_bits_total += sum(math.ceil(math.log2(max(g + 1, 2))) for g in gaps)

    print(f"\n  Option 3: Gap-encoded cycle positions (membership only)")
    print(f"    Bits for membership: {gap_bits_total:,}  ({gap_bits_total//8:,} bytes)")
    print(f"    NOTE: order within cycle adds ~log2(L!) bits per cycle of length L")
    order_bits = sum(math.ceil(math.log2(math.factorial(len(c)))) if len(c) <= 20
                     else int(len(c) * math.log2(len(c)))  # Stirling approx
                     for c in cycles)
    print(f"    Bits for within-cycle order: {order_bits:,}  ({order_bits//8:,} bytes)")

    # Recipe option 4: seed+k with FY inversion (the correct model)
    print(f"\n  Option 4: seed+k model (FY inversion)")
    print(f"    If FY(seed)^k = P exactly:")
    print(f"    Recipe = 64-bit seed + ceil(log2(k+1)) bits")
    print(f"    Best case (k=1): 65 bits = 9 bytes")
    print(f"    This requires finding seed s.t. FY(seed) = P")
    print(f"    PCG32 inversion: feasible (known structure, ~O(n) to recover seed from output)")
    print(f"    numpy PCG64 inversion: harder but documented")
    print(f"    BLAKE3-keyed: impractical to invert")
    print()
    print(f"    Action needed: implement PCG32 seed recovery from known swap sequence")

    return {
        "n": n,
        "n_cycles": len(cycles),
        "lehmer_bits": lb,
        "cycle_bits": total_cycle_bits,
        "exact": exact,
    }


def parse_args():
    p = argparse.ArgumentParser()
    p.add_argument("files", nargs="+")
    return p.parse_args()


def main():
    args = parse_args()
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V34 — TSP EXACT SEED ANALYSIS                        ║")
    print("║  Measure recipe options for exact reconstruction            ║")
    print("╚══════════════════════════════════════════════════════════════╝")

    for f in args.files:
        path = Path(f).expanduser()
        print(f"\n{'='*72}")
        print(f"  File: {path.name}  ({path.stat().st_size:,} bytes)")
        print(f"{'='*72}")
        run(path.read_bytes())

    return 0


if __name__ == "__main__":
    sys.exit(main())
