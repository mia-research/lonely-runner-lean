#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
shortscalar_sum_stageA_v2.py  --  R-CONTIG firm bound against the CORRECT null.

Executes PREREG v4 amendment: primary gating null = RANDOM-LOCATION INTERVAL
(like-to-like; immune to the iid-null pool-imbalance / equidistribution artifacts
that invalidated Stage A v1).  Two-sided 99th screen + same-tail 5-seed OOS.
Numeric epsilon* from a C-PLANT power scan against this null.

Controls:
  C-GLV     phi-closed set -> E3=E6=0 exact (instrument).
  C-NEG     extra random-location intervals rank ~uniform vs the null (calibration;
            they ARE null draws -> exchangeable -> uniform).  Confirms no bug.
  C-PLANT   inject a cubic-class-0 excess into a random-location interval; report
            the smallest injected fraction whose E3 reaches the null 99th -> eps*.

Exact integer statistics; Rule 3 geometry.  Reuses frozen v1 machinery.
Usage: python3 shortscalar_sum_stageA_v2.py [L] [Rnull] [nseed] [seed]
"""
import sys
import time
import random

from shortscalar_sum_stageA_v1 import (
    interval_codes, hist_of_codes, stats_from_hist, random_point, code_of,
    chi3_class, N_ORDER, BETA, P_FIELD,
)

NAMES = ("E2", "E3", "E6", "D6")


def rank_upper(sorted_null, v):
    lo, hi = 0, len(sorted_null)
    while lo < hi:
        mid = (lo + hi) // 2
        if sorted_null[mid] < v: lo = mid + 1
        else: hi = mid
    return len(sorted_null) - lo            # #null >= v


def two_sided_tag(p):
    if p <= 0.005: return "HI"
    if p >= 0.995: return "LO"
    return "."


def plant_codes(base_codes, f, rng):
    """override each point's cubic class to 0 with prob f (keep chi2 bit b)."""
    out = []
    for cd in base_codes:
        b = cd // 3
        if rng.random() < f:
            out.append(3 * b + 0)
        else:
            out.append(cd)
    return out


def main():
    L = int(sys.argv[1]) if len(sys.argv) > 1 else 5000
    Rnull = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    nseed = int(sys.argv[3]) if len(sys.argv) > 3 else 5
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 20260802
    KS = [40, 64, 96, 128, 160, 200]
    rng = random.Random(seed)

    total_iv = Rnull + 30 + len(KS) * nseed + 6   # null + C-NEG + arms + plant/glv
    print("=" * 80)
    print(f"R-CONTIG FIRM BOUND vs RANDOM-LOCATION null  L={L} Rnull={Rnull} nseed={nseed} seed={seed}")
    print(f"BIG-O (Rule 2): ~{total_iv} real intervals x 2L modexp = {total_iv*2*L:,} modexp"
          f"  (each interval O(L); the null is the cost driver, not a cheap resample)")
    print("=" * 80)
    t0 = time.perf_counter()
    tb = time.perf_counter(); a = 3
    for _ in range(1000): a = pow((a + 7) % P_FIELD or 3, (P_FIELD - 1) // 3, P_FIELD)
    print(f"[bench] pow = {(time.perf_counter()-tb)/1000*1e6:.1f} us/modexp")

    # --- PRIMARY NULL: random-location intervals ---------------------------
    tn = time.perf_counter()
    null = {nm: [] for nm in NAMES}
    for _ in range(Rnull):
        H = hist_of_codes(interval_codes(rng.randrange(2, N_ORDER), L))
        for nm, v in zip(NAMES, stats_from_hist(H, L)): null[nm].append(v)
    for nm in NAMES: null[nm].sort()
    print(f"[null] {Rnull} random-location intervals in {time.perf_counter()-tn:.0f}s")
    for nm in NAMES:
        arr = null[nm]
        print(f"    {nm}: median={arr[len(arr)//2]:>10}  1st={arr[len(arr)//100]:>10}"
              f"  99th={arr[(99*len(arr))//100]:>10}")

    # --- C-GLV ------------------------------------------------------------
    S = []
    for _ in range(max(1, L // 3)):
        x = random_point(rng)[0]
        S += [x, (BETA * x) % P_FIELD, (BETA * BETA * x) % P_FIELD]
    eg = stats_from_hist(hist_of_codes(code_of(x) for x in S), len(S))
    print(f"[C-GLV] phi-closed E3={eg[1]} E6={eg[2]} -> {'PASS' if eg[1]==0 and eg[2]==0 else 'FAIL'}")
    assert eg[1] == 0 and eg[2] == 0

    # --- C-NEG: extra random-location intervals must rank ~uniform ---------
    R = len(null["E3"])
    cneg_hi = cneg_lo = 0
    NC = 30
    for _ in range(NC):
        H = hist_of_codes(interval_codes(rng.randrange(2, N_ORDER), L))
        for nm, v in zip(NAMES, stats_from_hist(H, L)):
            p = rank_upper(null[nm], v) / R
            if p <= 0.05: cneg_hi += 1
            if p >= 0.95: cneg_lo += 1
    tot = NC * len(NAMES)
    print(f"[C-NEG] {NC} intervals x{len(NAMES)} readouts: HI-tail(<=.05)={cneg_hi}/{tot}"
          f" LO-tail(>=.95)={cneg_lo}/{tot}  (each ~5% nominal) -> "
          f"{'CALIBRATED' if abs(cneg_hi/tot-0.05)<0.06 and abs(cneg_lo/tot-0.05)<0.06 else 'CHECK'}")

    # --- bound: analytical (valid now the null is correct) + C-PLANT confirm --
    import math
    v99 = null["E3"][(99 * R) // 100]
    eps_star = 2 * math.sqrt(v99) / L
    print(f"[bound] E3 null 99th = {v99}; analytical coherent cubic bound "
          f"eps* = 2*sqrt(V99)/L = {eps_star*100:.2f}%")
    print(f"[C-PLANT] confirm: inject cubic-class-0 fraction f into FRESH intervals -> E3 vs 99th:")
    eps_fire = None
    for f in (0.01, 0.02, 0.04, 0.07, 0.10, 0.15):
        H = hist_of_codes(plant_codes(interval_codes(rng.randrange(2, N_ORDER), L), f, rng))
        e3 = stats_from_hist(H, L)[1]
        excess = ((H[0] + H[3]) - L / 3) / (L / 3)   # excess vs expected class size L/3 (eps* units)
        fired = e3 > v99
        print(f"    f={f:5.3f}: class0-excess={excess*100:5.2f}%  E3={e3:>11}  {'FIRES' if fired else '--'}")
        if fired and eps_fire is None:
            eps_fire = excess
    print(f"    => C-PLANT fires at coherent excess ~ {eps_fire*100:.2f}% (brackets analytical eps*)"
          if eps_fire else "    => C-PLANT no fire up to 15% -- raise L")

    # --- ARMS: band-confined s0, nseed OOS, two-sided ---------------------
    print("=" * 80)
    print(f"BAND ARMS vs random-location null (two-sided; {nseed}-seed OOS; per-seed rank-p):")
    ta = time.perf_counter()
    candidates = []
    allp = {nm: [] for nm in NAMES}
    for k in KS:
        rows = {nm: [] for nm in NAMES}
        for si in range(nseed):
            s0 = rng.randrange(1 << (k - 1), 1 << k)
            for nm, v in zip(NAMES, stats_from_hist(hist_of_codes(interval_codes(s0, L)), L)):
                rows[nm].append(rank_upper(null[nm], v) / R)
        line = []
        for nm in NAMES:
            ps = rows[nm]
            allp[nm].extend(ps)
            tags = "".join(two_sided_tag(p) for p in ps)
            # candidate = same tail on all nseed
            hi_all = all(p <= 0.005 for p in ps)
            lo_all = all(p >= 0.995 for p in ps)
            mark = " <=CANDIDATE" if (hi_all or lo_all) else ""
            if hi_all or lo_all:
                candidates.append((k, nm, "HI" if hi_all else "LO"))
            line.append(f"{nm}[{tags}]{mark}")
        pmin = {nm: f"{min(rows[nm]):.3f}/{max(rows[nm]):.3f}" for nm in NAMES}
        print(f"  k={k:>3}: " + "  ".join(line))
        print(f"        p-range(min/max): " + "  ".join(f"{nm}={pmin[nm]}" for nm in NAMES))
    print(f"[arms] {len(KS)}x{nseed} band intervals in {time.perf_counter()-ta:.0f}s")
    # LEAN-CHECK (added retroactively): systematic sub-threshold lean per channel, not just tails
    print("[audit] mean arm pctile per channel (0.5=no lean; the R-CONTIG blind spot the tail-screen misses):")
    for nm in NAMES:
        mp = sum(1 - p for p in allp[nm]) / len(allp[nm])
        lo_n = sum(1 for p in allp[nm] if p >= 0.90); hi_n = sum(1 for p in allp[nm] if p <= 0.10)
        flag = "LEAN" if not (0.44 <= mp <= 0.56) else "flat"
        print(f"    {nm}: mean pctile={mp:.3f} [{flag}]  arm-low10%={lo_n}/{len(allp[nm])} arm-high10%={hi_n}/{len(allp[nm])}")

    print("=" * 80)
    print("VERDICT (Rule 5 -- a bound, never a closure):")
    if candidates:
        print(f"  CANDIDATE cells (same tail {nseed}/{nseed} seeds): {candidates}")
        print("  -> characterize via anomaly-drill (symmetry/eigenvector/subspace); do NOT name yet.")
    else:
        print(f"  No band cell screened same-tail on {nseed}/{nseed} seeds.")
        print(f"  => BOUNDED: band-confinement excludes a coherent cubic bias >= "
              f"{eps_star*100:.2f}% at L={L}" if eps_star else "  => BOUNDED (eps* > 5%)")
        print("  => band/location channel: no detectable effect (a bound; open below eps* and for")
        print("     location-independent effects, R-BAND, differences, other readouts, larger L).")
    print(f"TOTAL WALL TIME: {time.perf_counter()-t0:.0f}s")


if __name__ == "__main__":
    main()
