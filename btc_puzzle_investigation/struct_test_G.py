#!/usr/bin/env python3
"""
struct_test_G.py  —  Plan v5 Test G: DP-table percolation / density threshold.

Percolation theory: traversability can flip SHARPLY at a critical density. Does the
kangaroo DP table behave that way -- is there a critical #DPs where collision
probability jumps -- or does it rise SMOOTHLY (classical birthday/crossing-time)?
Directly tunes dp_bits: a sharp knee means sit just past it.

Method: many solvable kangaroos at fixed W; record #DPs in the table at the moment
of collision. If there is a threshold, DPs-at-collision concentrates (coefficient of
variation CV -> 0). Birthday/crossing-time => broad, smooth (CV ~ O(1)). Swept over
dp_bits. Integer point ops; collision by exact point equality.

Usage: python3 struct_test_G.py
"""
import secrets, statistics
from puzzle_kangaroo import add, mul, G

def make_jumps(W):
    B = W.bit_length(); K = max(8, B // 2 + 2)
    jumps = [1 << i for i in range(K)]
    return K, jumps, [mul(s) for s in jumps]

def run_once(a, b, dp_bits, max_mult=80):
    """One solvable kangaroo. Return (#DPs in table at collision, steps) or (None,steps)."""
    W = b - a; B = W.bit_length()
    K, jumps, jumpG = make_jumps(W)
    dp_mask = (1 << dp_bits) - 1
    max_steps = max_mult * (1 << (B // 2)) + 5000
    d_true = a + secrets.randbelow(W); Q = mul(d_true)
    tame_e0 = (a + b) // 2
    T = mul(tame_e0); td = 0; Wp = Q; wd = 0
    table = {}; steps = 0
    while steps < max_steps:
        i = T[0] % K; T = add(T, jumpG[i]); td += jumps[i]
        if (T[0] & dp_mask) == 0:
            e = table.get(T)
            if e and e[0] == "W":
                return len(table), steps
            table[T] = ("T", td)
        i = Wp[0] % K; Wp = add(Wp, jumpG[i]); wd += jumps[i]
        if (Wp[0] & dp_mask) == 0:
            e = table.get(Wp)
            if e and e[0] == "T":
                return len(table), steps
            table[Wp] = ("W", wd)
        steps += 1
    return None, steps

def main():
    WBITS = 26
    a = 1 << 50; b = a + (1 << WBITS)
    base_dp = WBITS // 2 - 5
    M = 50
    print(f"# TEST G  DP-table percolation   W=2^{WBITS}, {M} instances/dp_bits")
    print("# DPs-at-collision: CV~O(1) => smooth (birthday/crossing). CV->0 => sharp threshold.\n")
    for dp in (base_dp - 2, base_dp, base_dp + 2):
        dps = []; solved = 0
        for _ in range(M):
            nd, steps = run_once(a, b, dp)
            if nd is not None:
                dps.append(nd); solved += 1
        if len(dps) >= 3:
            mean = statistics.mean(dps); sd = statistics.pstdev(dps)
            cv = sd / mean if mean else 0.0                       # noqa: float (reported diagnostic)
            dps_sorted = sorted(dps)
            # sharpness: largest jump in the normalized empirical CDF between consecutive points
            gaps = [(dps_sorted[i+1]-dps_sorted[i])/mean for i in range(len(dps_sorted)-1)]  # noqa: float
            print(f"  dp_bits={dp:2d}  solved {solved}/{M}  DPs@collision: "
                  f"mean={mean:8.1f}  median={statistics.median(dps):8.1f}  CV={cv:.3f}  "
                  f"min={min(dps)} max={max(dps)}")
        else:
            print(f"  dp_bits={dp:2d}  solved {solved}/{M}  (too few to summarize)")
    print("\n  read: CV ~ 0.4-1.0 across dp_bits => smooth birthday/crossing-time, NO percolation")
    print("        threshold (dp_bits is a smooth memory/latency tradeoff, tune freely).")
    print("        CV collapsing toward 0 at some dp_bits => a real density threshold there.")

if __name__ == "__main__":
    main()
