#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
chi2_diffset_definitive_v1.py -- settle the χ2 band-difference-set question by RUNNING it, not arguing.

The apparent 0.600 lean came from ONE reused arm-set. This draws N genuinely-independent band-random
arms (varied k and seed) and N fresh-uniform sets on secp256k1, M=400, and asks directly:
is the arm χ2 (E2) distribution shifted above the fresh-uniform distribution, or not?
  arm ≈ fresh (Mann-Whitney P~0.5, arm mean pctile ~0.5)  => NULL: the lean was a false positive.
  arm >> fresh (P>=0.65, arm mean pctile >=0.57)          => REAL: the 0.384 was the fluke, re-open.
Both sides are REAL point sets (no bootstrap, no pool); the only difference is band-confined scalars.

Usage: python3 chi2_diffset_definitive_v1.py [N] [M] [seed]
"""
import sys, time, bisect, random
from c2_grouplaw_diffset_curve_v1 import Curve, stats3, diffset_hist

KS = [40, 64, 96, 128, 160, 200]
NAMES = ("E2", "E3", "E6")


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 80
    M = int(sys.argv[2]) if len(sys.argv) > 2 else 400
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 90210
    cur = Curve("secp"); rng = random.Random(seed)
    print("=" * 78)
    print(f"χ2 DEFINITIVE: {N} independent band-random ARMS vs {N} fresh-uniform sets, secp M={M}")
    print("=" * 78)
    t0 = time.perf_counter()

    fresh = {nm: [] for nm in NAMES}
    for i in range(N):
        pts = [cur.rand_point(rng) for _ in range(M)]
        for nm, v in zip(NAMES, stats3(diffset_hist(cur, pts))): fresh[nm].append(v)
        if (i + 1) % 20 == 0: print(f"  [fresh] {i+1}/{N}  ({time.perf_counter()-t0:.0f}s)")
    fresh_sorted = {nm: sorted(fresh[nm]) for nm in NAMES}

    arm = {nm: [] for nm in NAMES}
    for i in range(N):
        k = KS[i % len(KS)]
        pts = [cur.mul(rng.randrange(1 << (k - 1), 1 << k), cur.G) for _ in range(M)]
        for nm, v in zip(NAMES, stats3(diffset_hist(cur, pts))): arm[nm].append(v)
        if (i + 1) % 20 == 0: print(f"  [arm]   {i+1}/{N}  ({time.perf_counter()-t0:.0f}s)")

    print("-" * 78)
    print(f"result (arm vs fresh-uniform, N={N} each):")
    for nm in NAMES:
        fs = fresh_sorted[nm]
        # arm mean pctile vs the fresh distribution
        mp = sum(bisect.bisect_left(fs, a) for a in arm[nm]) / (N * N)
        # Mann-Whitney P(arm > fresh)
        U = sum(N - bisect.bisect_right(fs, a) for a in arm[nm])
        Pgt = U / (N * N)
        amed = sorted(arm[nm])[N // 2]; fmed = fs[N // 2]
        verdict = ("SHIFTED-HIGH(real?)" if mp >= 0.57 else
                   "SHIFTED-LOW" if mp <= 0.43 else "NULL(no shift)")
        print(f"  {nm}: arm-median={amed:>10} fresh-median={fmed:>10}  arm-mean-pctile={mp:.3f}"
              f"  P(arm>fresh)={Pgt:.3f}  [{verdict}]")
    print("-" * 78)
    e2mp = sum(bisect.bisect_left(fresh_sorted['E2'], a) for a in arm['E2']) / (N * N)
    print("VERDICT (χ2/E2 — the finding's channel):")
    if 0.44 <= e2mp <= 0.56:
        print(f"  E2 arm-mean-pctile={e2mp:.3f} ∈ [0.44,0.56] => NULL. The 0.600 lean was a FALSE POSITIVE")
        print("  (a single reused arm-set); band-random difference-sets show no χ2 shift. Confirmed by RUN.")
    elif e2mp >= 0.57:
        print(f"  E2 arm-mean-pctile={e2mp:.3f} >= 0.57 => SHIFTED. The effect survives independent arms;")
        print("  the 0.384 curve-run was the fluke. RE-OPEN and characterize.")
    else:
        print(f"  E2 arm-mean-pctile={e2mp:.3f} — anti-shift; investigate direction.")
    print(f"TOTAL WALL TIME: {time.perf_counter()-t0:.0f}s")


if __name__ == "__main__":
    main()
