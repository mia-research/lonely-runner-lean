#!/usr/bin/env python3
"""
Batch chamber analysis for prime-power Tier 2 density program.

For each non-unit drop pair of Z_{p^k}, compute:
  - C_bad / (L/p)               : overall ratio (should be O_k(1))
  - |S_drop|                    : number of fully dangerous chambers
  - max C_bad(C_s) / (L/p^2)   : partial-chamber ratio (should be O_k(1))

This tests the empirical validity of Theorems D2 and D3 from
lrc_transport_density_program_v1.md.

Usage:
  python3 prime_power_batch_analysis.py --n 27
  python3 prime_power_batch_analysis.py --n 125 --max-pairs 30
  python3 prime_power_batch_analysis.py --n 343 --max-pairs 20 --verbose
"""

from __future__ import annotations

import argparse
import csv
import sys
from dataclasses import dataclass
from itertools import combinations
from math import gcd, lcm
from typing import Dict, List, Optional, Sequence, Set, Tuple


# ---------------------------------------------------------------------------
# Core primitives (copied from prime_power_transport_exact_stats.py,
# using the CORRECTED floor variable q_e(b) = floor(e*b/L))
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Interval:
    start: int
    end: int
    dangerous: bool

    @property
    def width(self) -> int:
        return self.end - self.start + 1


def factor_prime_power(n: int) -> Tuple[int, int]:
    """Return (p, k) such that n = p^k, or (n, 1) if n is prime."""
    temp = n
    q = 2
    while q * q <= temp:
        if temp % q == 0:
            p = q
            k = 0
            while temp % p == 0:
                temp //= p
                k += 1
            if temp != 1:
                raise ValueError(f"{n} is not a prime power")
            return p, k
        q += 1
    return n, 1  # n is prime


def bad_set(e: int, t: int, n: int) -> Set[int]:
    """
    bad(e, t, n) = Sol(e, -t, n) union Sol(e, -(t+1), n).
    Sol(e, c, n) = {r mod n : e*r ≡ c (mod n)}.
    """
    g = gcd(e, n)
    result: Set[int] = set()
    for c in (-t, -(t + 1)):
        c %= n
        if c % g != 0:
            continue
        mod = n // g
        inv = pow(e // g, -1, mod)
        r0 = (c // g) * inv % mod
        for kk in range(g):
            result.add((r0 + kk * mod) % n)
    return result


def build_active_set(n: int, drop_pair: Sequence[int]) -> List[int]:
    drop = set(drop_pair)
    active = [e for e in range(1, n) if e not in drop]
    if len(active) != n - 3:
        raise ValueError(f"drop pair {drop_pair} is not valid for n={n}")
    return active


def compute_l(active: Sequence[int], n: int) -> int:
    value = 1
    for e in list(active) + [n]:
        value = lcm(value, e)
    return value


def transition_points(
    active: Sequence[int], l_value: int, b_lo: int, b_hi: int
) -> List[int]:
    """
    Return sorted list of b-values where some floor q_e(b) = floor(e*b/L) changes.
    Includes b_lo and b_hi+1 as sentinels.
    """
    pts: Set[int] = {b_lo, b_hi + 1}
    for e in active:
        m0 = (e * b_lo) // l_value
        for m in range(m0 + 1, e):
            b = (m * l_value + e - 1) // e  # = ceil(m * L / e)
            if b_lo <= b <= b_hi:
                pts.add(b)
    return sorted(pts)


def interval_partition(
    active: Sequence[int], n: int, l_value: int, b_lo: int, b_hi: int
) -> List[Interval]:
    """
    Partition B_div into maximal constant-floor-state intervals.
    On each interval, coverage is constant, so dangerousness is constant.
    """
    pts = transition_points(active, l_value, b_lo, b_hi)
    intervals: List[Interval] = []
    for i in range(len(pts) - 1):
        start = pts[i]
        end = pts[i + 1] - 1
        if start > end:
            continue
        union_bad: Set[int] = set()
        for e in active:
            t = (e * start) // l_value  # q_e(start) = floor(e * start / L)
            union_bad |= bad_set(e, t, n)
            if len(union_bad) == n:
                break  # already transport-complete; no need to check more runners
        intervals.append(Interval(start=start, end=end, dangerous=(len(union_bad) == n)))
    return intervals


# ---------------------------------------------------------------------------
# Per-drop-pair analysis
# ---------------------------------------------------------------------------

def analyze_drop_pair(n: int, p: int, k: int, drop_pair: Sequence[int]) -> Dict:
    """
    Full chamber analysis for one drop pair.

    Returns a dict with:
      cbad_over_M       : C_bad / (L/p)
      s_drop_size       : |S_drop| = number of fully dangerous chambers
      s_drop            : list of fully dangerous chamber indices s
      partial_max_ratio : max C_bad(C_s) / (L/p^2) over partial chambers
      partial_ratios    : per-chamber partial ratios (for distribution)
      L_digits          : number of decimal digits in L
    """
    active = build_active_set(n, drop_pair)
    l_value = compute_l(active, n)
    m_value = l_value // p          # M = L/p
    b_lo = l_value // n + 1
    b_hi = ((n - 1) * l_value) // n - 1
    intervals = interval_partition(active, n, l_value, b_lo, b_hi)

    dangerous_total = sum(iv.width for iv in intervals if iv.dangerous)

    s_drop: List[int] = []
    partial_ratios: List[float] = []

    for s in range(1, p):
        c_lo = max(s * m_value, b_lo)
        c_hi = min((s + 1) * m_value - 1, b_hi)
        if c_hi < c_lo:
            continue
        c_total = c_hi - c_lo + 1
        c_dangerous = sum(
            min(iv.end, c_hi) - max(iv.start, c_lo) + 1
            for iv in intervals
            if iv.dangerous and iv.start <= c_hi and iv.end >= c_lo
        )
        if c_dangerous == c_total:
            s_drop.append(s)
        elif c_dangerous > 0:
            # C_bad(C_s) / (L/p^2) = C_bad(C_s) * p^2 / L
            ratio = c_dangerous * p / m_value   # = c_dangerous * p^2 / L
            partial_ratios.append(ratio)

    return {
        "drop": list(drop_pair),
        "L_digits": len(str(l_value)),
        "dangerous_total": dangerous_total,
        "cbad_over_M": dangerous_total / m_value,
        "s_drop_size": len(s_drop),
        "s_drop": s_drop,
        "partial_max_ratio": max(partial_ratios) if partial_ratios else 0.0,
        "partial_ratios": partial_ratios,
    }


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, required=True, help="Prime power n = p^k")
    parser.add_argument("--max-pairs", type=int, default=None,
                        help="Cap on number of drop pairs to process")
    parser.add_argument("--verbose", action="store_true",
                        help="Print per-pair progress to stderr")
    parser.add_argument("--outfile", type=str, default=None,
                        help="Write CSV to this file (default: stdout)")
    args = parser.parse_args()

    n = args.n
    p, k = factor_prime_power(n)
    nonunits = [e for e in range(1, n) if e % p == 0]
    all_pairs = list(combinations(nonunits, 2))

    total_available = len(all_pairs)
    if args.max_pairs:
        all_pairs = all_pairs[:args.max_pairs]

    print(
        f"# n={n}, p={p}, k={k}, "
        f"non-units={len(nonunits)}, "
        f"drop pairs={len(all_pairs)}/{total_available}",
        file=sys.stderr,
    )

    # Open output
    out_file = open(args.outfile, "w", newline="") if args.outfile else sys.stdout
    writer = csv.writer(out_file)
    writer.writerow([
        "drop_a", "drop_b",
        "cbad_over_M",       # C_bad / (L/p)
        "s_drop_size",       # |S_drop|
        "s_drop",            # which s values are fully dangerous
        "partial_max_ratio", # max C_bad(C_s)/(L/p^2) over partial chambers
        "partial_ratios",    # all partial ratios (semicolon-separated)
        "L_digits",          # size of L (sanity check)
    ])

    all_cbad: List[float] = []
    all_sdrop: List[int] = []
    all_partial: List[float] = []

    for i, drop in enumerate(all_pairs):
        result = analyze_drop_pair(n, p, k, drop)

        writer.writerow([
            drop[0], drop[1],
            f"{result['cbad_over_M']:.6f}",
            result["s_drop_size"],
            ";".join(map(str, result["s_drop"])),
            f"{result['partial_max_ratio']:.6f}",
            ";".join(f"{r:.4f}" for r in result["partial_ratios"]),
            result["L_digits"],
        ])
        if hasattr(out_file, "flush"):
            out_file.flush()

        all_cbad.append(result["cbad_over_M"])
        all_sdrop.append(result["s_drop_size"])
        all_partial.append(result["partial_max_ratio"])

        if args.verbose or (i + 1) % 10 == 0:
            print(
                f"  [{i+1}/{len(all_pairs)}] drop={drop}: "
                f"C_bad/M={result['cbad_over_M']:.4f}, "
                f"|S_drop|={result['s_drop_size']}, "
                f"partial_max/(L/p^2)={result['partial_max_ratio']:.4f}",
                file=sys.stderr,
            )

    if args.outfile:
        out_file.close()

    # Summary to stderr
    if all_cbad:
        print(f"\n# ===== Summary for n={n} (p={p}, k={k}) =====", file=sys.stderr)
        print(f"#   pairs analysed         = {len(all_pairs)}", file=sys.stderr)
        print(f"#   max  C_bad/(L/p)       = {max(all_cbad):.6f}", file=sys.stderr)
        print(f"#   mean C_bad/(L/p)       = {sum(all_cbad)/len(all_cbad):.6f}", file=sys.stderr)
        print(f"#   max  |S_drop|          = {max(all_sdrop)}", file=sys.stderr)
        print(f"#   max  partial/(L/p^2)   = {max(all_partial):.6f}", file=sys.stderr)
        print(f"#   mean partial/(L/p^2)   = {sum(all_partial)/len(all_partial):.6f}", file=sys.stderr)
        # Distribution of |S_drop|
        from collections import Counter
        sdrop_dist = Counter(all_sdrop)
        print(f"#   |S_drop| distribution  = {dict(sorted(sdrop_dist.items()))}", file=sys.stderr)


if __name__ == "__main__":
    main()
