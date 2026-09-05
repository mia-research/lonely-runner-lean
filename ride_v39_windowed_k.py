#!/usr/bin/env python3
"""
RIDE V39 - Windowed K coordinate system for the order layer.
# v1.0 — 2026-04-13 — test whether local K-steps give compact order coordinates

THE INSIGHT
-----------
The global K step maps every arrangement with the same digit multiset to the
SAME value — it destroys all arrangement information in one step.

But a WINDOWED K step (K applied to non-overlapping windows of w digits) is
arrangement-sensitive: different arrangements give different wK results.

Key finding (from exploration):
- wK(source) vs wK(target): mile=14 for w=2 (vs mile=2047 directly)
- The wK output space naturally produces K-extension pairs (digits summing to 9)
- The degeneracy structure matches the K-lattice extension basis

HYPOTHESIS
----------
The transformation wK^{-1}(wK(target) → target) might be describable by a
short sequence of coordinates in the K-extension basis. Specifically:

1. Compute wK(source) and wK(target) — both live in the wK output space
2. The difference wK(target) - wK(source) might be small/structured
3. Additionally: wK(target) is close to a K-constant in frequency space
   → describable by a few K-lattice coordinates
4. Recovery: given wK(target) + inverse map → recover target

WHAT WE TEST
------------
1. How compact is wK(target) relative to target?
2. Does wK(target) sit near a K-constant in frequency space?
3. What is the residual structure (mile, frequency delta)?
4. Can we recover target from wK(target) + a small residual?
5. Is the total description (wK-coordinates + residual) smaller than the file?

DECODER REPRODUCIBILITY
-----------------------
Both encoder and decoder know source (K-source, fully specified by frequency coords).
wK(source) is computable by both. The recipe encodes how to get from wK(source) to
wK(target), plus how to invert wK.

The inversion problem: wK is not injective (many inputs → same output).
We need to specify WHICH pre-image of wK(output) is the correct target.
This is the key open question — if the pre-image is small, the extra cost is small.
"""

from __future__ import annotations

import sys
import math
import zlib
import hashlib
from pathlib import Path
from collections import Counter, defaultdict
from typing import Any

HERE = Path(__file__).resolve().parent
MIAI = Path("/Users/trentpalelei/MIAI")
for candidate in (HERE, MIAI):
    s = str(candidate)
    if candidate.exists() and s not in sys.path:
        sys.path.insert(0, s)

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(10_000_000)

import numpy as np

from ride_v18_cycle_rsn import materialise_source_and_target
from ride_v24_order_family_harness import residual_stats


# ---------------------------------------------------------------------------
# Windowed K operation
# ---------------------------------------------------------------------------

def windowed_k(digits: list[int], w: int) -> list[int]:
    """Apply K operation within each non-overlapping window of w digits."""
    result = list(digits)
    n = len(digits)
    for start in range(0, n - w + 1, w):
        window = digits[start:start + w]
        desc = int(''.join(str(x) for x in sorted(window, reverse=True)))
        asc  = int(''.join(str(x) for x in sorted(window)))
        diff = desc - asc
        diff_d = [int(c) for c in str(diff).zfill(w)]
        result[start:start + w] = diff_d
    return result


def windowed_k_pairs(digits: list[int], w: int) -> list[tuple]:
    """Return (window_index, input_window, output_window) for analysis."""
    pairs = []
    n = len(digits)
    for start in range(0, n - w + 1, w):
        window = digits[start:start + w]
        desc = int(''.join(str(x) for x in sorted(window, reverse=True)))
        asc  = int(''.join(str(x) for x in sorted(window)))
        diff = desc - asc
        diff_d = tuple(int(c) for c in str(diff).zfill(w))
        pairs.append((start, tuple(window), diff_d))
    return pairs


# ---------------------------------------------------------------------------
# Pre-image analysis: how many inputs map to each wK output?
# ---------------------------------------------------------------------------

def build_preimage_map(w: int) -> dict[tuple, list[tuple]]:
    """Build the complete map: wK_output → list of inputs, for window size w."""
    preimage = defaultdict(list)
    # Enumerate all w-digit sequences
    def enum_sequences(w):
        if w == 0:
            yield ()
            return
        for d in range(10):
            for rest in enum_sequences(w - 1):
                yield (d,) + rest

    for seq in enum_sequences(w):
        seq_list = list(seq)
        desc = int(''.join(str(x) for x in sorted(seq_list, reverse=True)))
        asc  = int(''.join(str(x) for x in sorted(seq_list)))
        diff = desc - asc
        diff_d = tuple(int(c) for c in str(diff).zfill(w))
        preimage[diff_d].append(seq)

    return dict(preimage)


# ---------------------------------------------------------------------------
# Encode: represent target as wK-coordinates + residual
# ---------------------------------------------------------------------------

def encode_windowed_k(source: list[int], target: list[int], w: int,
                      preimage_map: dict) -> dict[str, Any]:
    """
    Attempt to encode target using windowed-K coordinates.

    Strategy:
    1. Compute wK(target) — the windowed K transform of target
    2. Compute wK(source) — same for source (decoder-reproducible)
    3. Measure the mile between wK(source) and wK(target)
    4. For each window position, record:
       a. Which wK output occurred (for wK(target))
       b. Which pre-image was selected (index into preimage_map[output])
    5. The recipe = list of pre-image indices (one per window)

    Recovery: for each window, look up output → preimage_map[output][index]

    Returns encoding statistics.
    """
    n = len(target)
    n_windows = n // w

    wK_source = windowed_k(source, w)
    wK_target = windowed_k(target, w)

    # Mile between wK(source) and wK(target)
    wK_mile = residual_stats(wK_source, wK_target).mile
    wK_mismatch = residual_stats(wK_source, wK_target).mismatch

    # For each window, find which pre-image index the target window is
    preimage_indices = []
    reconstruction = list(wK_source)  # start from wK(source), we'll fix each window

    total_preimage_bits = 0
    max_preimage_size = 0

    for i in range(n_windows):
        start = i * w
        tgt_window = tuple(target[start:start + w])

        # What does wK map this to?
        desc = int(''.join(str(x) for x in sorted(tgt_window, reverse=True)))
        asc  = int(''.join(str(x) for x in sorted(tgt_window)))
        diff = desc - asc
        wk_out = tuple(int(c) for c in str(diff).zfill(w))

        # Find index of tgt_window in preimage_map[wk_out]
        preimages = preimage_map.get(wk_out, [])
        if tgt_window in preimages:
            idx = preimages.index(tgt_window)
        else:
            idx = 0  # fallback

        n_preimages = len(preimages)
        bits_for_idx = math.ceil(math.log2(max(n_preimages, 1))) if n_preimages > 1 else 0
        total_preimage_bits += bits_for_idx
        max_preimage_size = max(max_preimage_size, n_preimages)

        preimage_indices.append((wk_out, idx, n_preimages))

    # What is wK(target)'s frequency profile?
    wK_tgt_freq = Counter(wK_target)

    # How far is wK(target) from source in frequency space?
    src_freq = Counter(source)
    wK_tgt_freq_vec = np.array([wK_tgt_freq.get(d, 0) for d in range(10)])
    src_freq_vec = np.array([src_freq.get(d, 0) for d in range(10)])
    freq_l1 = int(np.sum(np.abs(wK_tgt_freq_vec - src_freq_vec)))

    # How far is wK(target) from a K-constant in frequency space?
    # (Use the same metric as materialise_source_and_target)

    return {
        "w": w,
        "n_windows": n_windows,
        "wK_mile": wK_mile,
        "wK_mismatch": wK_mismatch,
        "total_preimage_bits": total_preimage_bits,
        "max_preimage_size": max_preimage_size,
        "avg_preimage_bits": total_preimage_bits / n_windows if n_windows > 0 else 0,
        "wK_freq_l1_from_source": freq_l1,
        "wK_freq": dict(sorted(wK_tgt_freq.items())),
        "src_freq": dict(sorted(src_freq.items())),
    }


# ---------------------------------------------------------------------------
# Multi-level windowed K: apply wK repeatedly
# ---------------------------------------------------------------------------

def iterated_windowed_k(digits: list[int], w: int, steps: int) -> list[list[int]]:
    """Apply windowed K repeatedly, returning all intermediate states."""
    states = [list(digits)]
    current = list(digits)
    for _ in range(steps):
        current = windowed_k(current, w)
        states.append(list(current))
    return states


# ---------------------------------------------------------------------------
# Main analysis
# ---------------------------------------------------------------------------

def analyse(raw: bytes) -> None:
    source_digits, target_digits, params, l1 = materialise_source_and_target(raw)
    n = len(target_digits)
    source = list(source_digits)
    target = list(target_digits)

    print(f"  n={n:,}  freq_L1={l1:,}")
    print(f"  Source-to-target mile (direct): {residual_stats(source, target).mile:,}")
    print()

    # -----------------------------------------------------------------------
    # Test 1: Single-level windowed K for various window sizes
    # -----------------------------------------------------------------------
    print("  [Test 1] Single-level windowed K transform")
    print(f"  {'w':>4}  {'wK_mile':>8}  {'wK_mm':>7}  {'preimage_bits':>14}  "
          f"{'avg_bits/win':>12}  {'freq_L1':>8}")
    print(f"  {'-'*4}  {'-'*8}  {'-'*7}  {'-'*14}  {'-'*12}  {'-'*8}")

    for w in [2, 3, 4, 5, 6, 8, 10, 12]:
        if w > 4:
            # Skip full preimage map build for large w (exponential)
            wK_s = windowed_k(source, w)
            wK_t = windowed_k(target, w)
            wK_mile = residual_stats(wK_s, wK_t).mile
            wK_mm = residual_stats(wK_s, wK_t).mismatch
            n_windows = n // w
            # Estimate preimage bits: each w-digit window has 10^w inputs → 10^w/n_outputs outputs
            # Average preimage size ≈ 10^w / (number of distinct outputs)
            distinct_outputs = len(set(tuple(wK_t[i*w:(i+1)*w]) for i in range(n_windows)))
            avg_preimage = (10**w) / max(distinct_outputs, 1)
            est_bits_per_win = math.log2(max(avg_preimage, 1))
            total_est_bits = est_bits_per_win * n_windows

            wK_freq = Counter(wK_t)
            src_freq = Counter(source)
            freq_l1 = sum(abs(wK_freq.get(d,0) - src_freq.get(d,0)) for d in range(10))

            print(f"  {w:>4}  {wK_mile:>8,}  {wK_mm:>7,}  {total_est_bits:>14.0f}  "
                  f"{est_bits_per_win:>12.2f}  {freq_l1:>8,}")
        else:
            preimage_map = build_preimage_map(w)
            result = encode_windowed_k(source, target, w, preimage_map)
            print(f"  {w:>4}  {result['wK_mile']:>8,}  {result['wK_mismatch']:>7,}  "
                  f"{result['total_preimage_bits']:>14,}  "
                  f"{result['avg_preimage_bits']:>12.2f}  "
                  f"{result['wK_freq_l1_from_source']:>8,}")

    print()

    # -----------------------------------------------------------------------
    # Test 2: Iterated windowed K
    # -----------------------------------------------------------------------
    print("  [Test 2] Iterated windowed K (w=2, multiple steps)")
    print(f"  {'steps':>6}  {'mile_to_tgt':>12}  {'mile_src_to':>12}  {'freq_L1':>8}")
    print(f"  {'-'*6}  {'-'*12}  {'-'*12}  {'-'*8}")

    # Apply wK iteratively to source — does it approach target?
    wK_source_states = iterated_windowed_k(source, 2, 10)
    for step, state in enumerate(wK_source_states):
        m_to_tgt = residual_stats(state, target).mile
        if step > 0:
            m_src_to = residual_stats(source, state).mile
        else:
            m_src_to = 0
        state_freq = Counter(state)
        src_freq = Counter(source)
        freq_l1 = sum(abs(state_freq.get(d,0) - src_freq.get(d,0)) for d in range(10))
        print(f"  {step:>6}  {m_to_tgt:>12,}  {m_src_to:>12,}  {freq_l1:>8,}")

    print()

    # -----------------------------------------------------------------------
    # Test 3: wK(target) frequency structure — is it near a K-constant?
    # -----------------------------------------------------------------------
    print("  [Test 3] wK(target) frequency analysis for w=2")
    wK_t = windowed_k(target, 2)
    wK_freq = Counter(wK_t)
    src_freq = Counter(source)

    print(f"  Digit  wK(target)  source    delta")
    for d in range(10):
        wkf = wK_freq.get(d, 0)
        sf = src_freq.get(d, 0)
        print(f"  {d}      {wkf:>9}  {sf:>6}    {wkf-sf:>+6}")

    print()
    print(f"  L1 distance wK(target) vs source freqs: "
          f"{sum(abs(wK_freq.get(d,0)-src_freq.get(d,0)) for d in range(10)):,}")

    # -----------------------------------------------------------------------
    # Test 4: Can we compress wK(target) using K-lattice coordinates?
    # -----------------------------------------------------------------------
    print()
    print("  [Test 4] Compression of wK(target) via K-lattice")

    wK_t_bytes = bytes(wK_t)
    compressed = zlib.compress(wK_t_bytes, 9)
    print(f"  wK(target) raw: {len(wK_t)} bytes")
    print(f"  wK(target) zlib: {len(compressed)} bytes")
    print(f"  File: {len(raw)} bytes")
    print(f"  Ratio wK_zlib/file: {len(compressed)/len(raw):.3f}")

    # Compare: zlib on raw target
    tgt_bytes = bytes(target)
    tgt_compressed = zlib.compress(tgt_bytes, 9)
    print(f"  target raw zlib: {len(tgt_compressed)} bytes (for reference)")

    # -----------------------------------------------------------------------
    # Test 5: The key metric — total bits to specify target via wK route
    # -----------------------------------------------------------------------
    print()
    print("  [Test 5] Total bit budget: wK route vs direct")

    # Direct route: just store the target
    direct_bits = len(raw) * 8

    # wK route (w=2):
    # - Store wK(target): len(wK_t) bytes raw, or use K-lattice encoding
    # - Store pre-image indices: total_preimage_bits
    w = 2
    preimage_map_2 = build_preimage_map(2)
    enc2 = encode_windowed_k(source, target, 2, preimage_map_2)

    # wK(target) encoding: since wK output space has specific structure
    # (outputs are always symmetric pairs summing to 9 or equal pairs),
    # each window output can be encoded more compactly than w*log2(10) bits
    # Distinct wK outputs for w=2: (00,09,18,27,36,45,54,63,72,81) = 10 options
    # → log2(10) ≈ 3.32 bits per window (same as 1 digit)
    n_windows_2 = n // 2
    wK_encoding_bits = n_windows_2 * math.log2(10)  # one digit per window
    preimage_bits = enc2['total_preimage_bits']

    total_wK_route = wK_encoding_bits + preimage_bits

    print(f"  Direct: {direct_bits} bits = {direct_bits//8} bytes")
    print(f"  wK route (w=2):")
    print(f"    wK(target) encoding: {wK_encoding_bits:.0f} bits ({n_windows_2} windows × 3.32 bits)")
    print(f"    Pre-image indices:   {preimage_bits:,} bits")
    print(f"    Total:               {total_wK_route:.0f} bits = {total_wK_route/8:.0f} bytes")
    print(f"    Ratio vs direct:     {direct_bits/total_wK_route:.3f}")
    print()

    # But wait — wK(target) is reconstructible from wK(source) + mile description
    # wK_mile = 14 for w=2. That's only 14 transpositions to describe.
    # 14 transpositions × ceil(log2(n)) bits each ≈ 14 × 12 = 168 bits
    wK_mile_2 = enc2['wK_mile']
    transposition_bits = wK_mile_2 * math.ceil(math.log2(n)) * 2  # 2 positions per transposition

    print(f"  BETTER wK route (w=2):")
    print(f"    wK(source)→wK(target) via {wK_mile_2} transpositions:")
    print(f"    Transposition recipe: {transposition_bits} bits")
    print(f"    Pre-image indices:    {preimage_bits:,} bits")
    total_better = transposition_bits + preimage_bits
    print(f"    Total:                {total_better:,} bits = {total_better//8} bytes")
    print(f"    Ratio vs direct:      {direct_bits/total_better:.3f}")
    print()
    print(f"  BOTTOM LINE: does pre-image cost dominate?")
    print(f"    Pre-image: {preimage_bits:,} bits ({preimage_bits/direct_bits*100:.1f}% of file)")
    print(f"    If pre-image were 0: {transposition_bits} bits — {direct_bits/transposition_bits:.0f}× smaller")


def main():
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V39 — WINDOWED K COORDINATE SYSTEM                   ║")
    print("║  Can local K-steps give compact order coordinates?         ║")
    print("╚══════════════════════════════════════════════════════════════╝")

    test_file = Path("/tmp/lrc_abstract.txt")
    if not test_file.exists():
        print(f"Test file not found: {test_file}")
        return 1

    raw = test_file.read_bytes()
    print(f"\n{'='*72}")
    print(f"  File: {test_file.name}  ({len(raw):,} bytes)")
    print(f"{'='*72}")

    analyse(raw)
    return 0


if __name__ == "__main__":
    sys.exit(main())
