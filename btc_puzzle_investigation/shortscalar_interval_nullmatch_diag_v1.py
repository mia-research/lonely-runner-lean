#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
shortscalar_interval_nullmatch_diag_v1.py

Diagnostic prompted by Stage A (shortscalar_sum_stageA_v1, L=1e5): every R-CONTIG
arm landed in the LOW tail of the iid random-point null (E3 5-25x below null
median; D6 more uniform).  Hypothesis: the iid null does not share the arm's
FORCED equidistribution structure (a deterministic consecutive orbit has lower
discrepancy than iid), so the low tail is a null-mismatch, not curve leakage.

DECISIVE TEST: rank the band-confined arms against a RANDOM-LOCATION INTERVAL null
(random s0, same length L) -- which SHARES the equidistribution.  Also show where
random-location intervals fall vs the iid null (to confirm they are ALSO low).

  * band arm MID vs random-location null  => low-tail was generic equidistribution;
    no band/location-specific effect; the 1.9% coherent BOUND stands, cleanly.
  * band arm EXTREME vs random-location null => a band-specific effect to characterize.

Exact integer statistics; Rule 3 geometry.  Reuses the frozen Stage A machinery.
Usage: python3 shortscalar_interval_nullmatch_diag_v1.py [L] [Rctrl] [seed]
"""
import sys
import time
import random

from shortscalar_sum_stageA_v1 import (
    interval_codes, hist_of_codes, stats_from_hist, random_point, code_of, N_ORDER,
)

NAMES = ("E2", "E3", "E6", "D6")


def rank_p(sorted_null, v):
    lo, hi = 0, len(sorted_null)
    while lo < hi:
        mid = (lo + hi) // 2
        if sorted_null[mid] < v: lo = mid + 1
        else: hi = mid
    return len(sorted_null) - lo


def main():
    L = int(sys.argv[1]) if len(sys.argv) > 1 else 5000
    Rctrl = int(sys.argv[2]) if len(sys.argv) > 2 else 150
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 20260802
    KS = [40, 64, 96, 128, 160, 200]
    rng = random.Random(seed)

    print("=" * 78)
    print(f"NULL-MATCH DIAGNOSTIC  L={L}  Rctrl={Rctrl}  seed={seed}")
    print(f"  band arm vs RANDOM-LOCATION INTERVAL null (shares equidistribution)")
    print(f"  op count: (Rctrl + 6) intervals x 2L modexp = {(Rctrl+6)*2*L:,} modexp")
    print("=" * 78)
    t0 = time.perf_counter()

    # --- iid random-point null (small reference) ---------------------------
    pool = [code_of(random_point(rng)[0]) for _ in range(20000)]
    iid = {nm: [] for nm in NAMES}
    for _ in range(2000):
        H = hist_of_codes(rng.choices(pool, k=L))
        e = stats_from_hist(H, L)
        for nm, v in zip(NAMES, e): iid[nm].append(v)
    for nm in NAMES: iid[nm].sort()
    print(f"[iid null] 2000 realizations done ({time.perf_counter()-t0:.0f}s)")

    # --- random-location interval null (the CORRECT matched null) ----------
    tr = time.perf_counter()
    rloc = {nm: [] for nm in NAMES}
    for _ in range(Rctrl):
        s0 = rng.randrange(2, N_ORDER)
        H = hist_of_codes(interval_codes(s0, L))
        e = stats_from_hist(H, L)
        for nm, v in zip(NAMES, e): rloc[nm].append(v)
    for nm in NAMES: rloc[nm].sort()
    print(f"[randloc null] {Rctrl} random-location intervals done ({time.perf_counter()-tr:.0f}s)")

    # --- where do random-location intervals fall vs the iid null? ----------
    print("-" * 78)
    print("Q1: are random-location intervals ALSO low vs the iid null?  (median rank-p vs iid)")
    for nm in NAMES:
        med = rloc[nm][len(rloc[nm]) // 2]
        p = rank_p(iid[nm], med) / len(iid[nm])
        loc = "LOW-tail (equidistribution)" if p > 0.90 else ("HIGH-tail" if p < 0.10 else "mid")
        print(f"   {nm}: median randloc={med:>12}  iid-median={iid[nm][len(iid[nm])//2]:>12}"
              f"  rank-p vs iid={p:5.3f}  [{loc}]")

    # --- the decisive test: band arms vs the random-location null ----------
    print("-" * 78)
    print("Q2 (DECISIVE): band-confined arms vs the random-location-interval null (UNCORRECTED p):")
    R = len(rloc["E3"])
    extreme = []
    for k in KS:
        s0 = rng.randrange(1 << (k - 1), 1 << k)
        H = hist_of_codes(interval_codes(s0, L))
        e = stats_from_hist(H, L)
        row = []
        for nm, v in zip(NAMES, e):
            ng = rank_p(rloc[nm], v)
            p = ng / R
            tag = "HI>=99" if p <= 0.01 else ("LO<=01" if p >= 0.99 else "mid")
            row.append(f"{nm} p={p:5.3f}[{tag}]")
            if p <= 0.01 or p >= 0.99:
                extreme.append((k, nm, p))
        print(f"   k={k:>3}: " + "  ".join(row))

    print("=" * 78)
    if extreme:
        print(f"band arms EXTREME vs random-location null: {extreme}")
        print("=> a band/location-specific effect survives the equidistribution control -> characterize (do NOT name yet; 5-seed OOS).")
    else:
        print("All band arms land MID vs the random-location-interval null.")
        print("=> the low-tail-vs-iid was GENERIC equidistribution of a consecutive orbit,")
        print("   NOT a band/location-specific effect.  The iid null was the wrong null for a")
        print("   deterministic interval; the random-location interval is the correct gate.")
        print("   R-CONTIG at this L: BOUNDED, no location leakage (a bound, not a closure).")
    print(f"TOTAL WALL TIME: {time.perf_counter()-t0:.0f}s")


if __name__ == "__main__":
    main()
