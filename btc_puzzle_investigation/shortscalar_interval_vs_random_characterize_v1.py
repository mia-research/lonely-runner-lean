#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
shortscalar_interval_vs_random_characterize_v1.py

The test I skipped: is the interval character sum GENUINELY more cancelled than
random points, or was Stage A's 5-25x low-tail a bootstrap/pool artifact?

Fair, artifact-immune comparison -- both sides are REAL point sets, no bootstrap:
  A = consecutive interval   { [s]G : s in [s0, s0+L) }
  B = fresh random point set { [r]G : r random }  (uniform group elements)
differing ONLY in scalar-consecutiveness.  Statistic: E2/E3/E6/D6 = |Sum chi|^2
(exact integer).  L-scaling {5000, 20000, 80000} -- a bootstrap artifact vanishes
without the bootstrap; a real interval effect persists and grows.

Guardrails (the three failure modes named):
 * NO null by design: B is the fairest matched null; if consecutiveness matters it shows.
 * NO dismissal by declaration: verdict = mechanical Mann-Whitney U + median ratio.
 * NO null by prose: POSITIVE CONTROLS (phi-closed -> E3=0; planted -> E3 high) must
   separate from B, proving the test can fire; a null only counts if they do and A doesn't.

Usage: python3 shortscalar_interval_vs_random_characterize_v1.py
"""
import sys
import time
import random
import math

from shortscalar_sum_stageA_v1 import (
    interval_codes, hist_of_codes, stats_from_hist, random_point, code_of,
    chi3_class, N_ORDER, BETA, P_FIELD,
)

NAMES = ("E2", "E3", "E6", "D6")
LADDER = [(5000, 40), (20000, 30), (80000, 20)]
if len(sys.argv) > 1 and sys.argv[1] == "smoke":
    LADDER = [(500, 10), (2000, 8)]
SEED = 20260802


def random_set_codes(L, rng):
    return [code_of(random_point(rng)[0]) for _ in range(L)]


def phi_closed_codes(L, rng):
    S = []
    for _ in range(max(1, L // 3)):
        x = random_point(rng)[0]
        S += [x, (BETA * x) % P_FIELD, (BETA * BETA * x) % P_FIELD]
    return [code_of(x) for x in S]


def planted_codes(L, rng, f=0.05):
    out = []
    for _ in range(L):
        if rng.random() < f:
            while True:
                x = random_point(rng)[0]
                if chi3_class(x) == 0:
                    out.append(code_of(x)); break
        else:
            out.append(code_of(random_point(rng)[0]))
    return out


def mann_whitney_lt(a, b):
    """U = #{(i,j): a_i < b_j}; returns U/(len(a)*len(b)) = P(a<b) and a z-score.
    P>0.5 => a systematically LOWER than b."""
    b_sorted = sorted(b)
    import bisect
    U = 0
    for x in a:
        U += bisect.bisect_left(b_sorted, x)   # # b strictly greater handled below
    # bisect_left gives # b < x; we want # b > x = len(b) - bisect_right
    # redo precisely:
    U = 0
    for x in a:
        U += len(b) - bisect.bisect_right(b_sorted, x)   # # b_j > x  => a_i < b_j
    n1, n2 = len(a), len(b)
    frac = U / (n1 * n2)
    mu = n1 * n2 / 2
    sd = math.sqrt(n1 * n2 * (n1 + n2 + 1) / 12)
    z = (U - mu) / sd if sd else 0.0
    return frac, z, U


def med(x):
    s = sorted(x); return s[len(s) // 2]


def main():
    rng = random.Random(SEED)
    print("=" * 84)
    print("INTERVAL vs REAL RANDOM POINT-SET  (no bootstrap; is the Stage A low-tail real?)")
    print(f"  ladder {LADDER}  seed {SEED}")
    print("  P(int<rand) ~0.5 => NO effect (Stage A gap was bootstrap artifact)")
    print("  P(int<rand) ->1  => intervals systematically MORE cancelled (REAL structure)")
    print("=" * 84)
    t0 = time.perf_counter()

    # ---- POSITIVE CONTROLS (prove the test can fire) ---------------------
    Lc = LADDER[0][0]
    tc = time.perf_counter()
    randB = [stats_from_hist(hist_of_codes(random_set_codes(Lc, rng)), Lc) for _ in range(30)]
    randB_E3 = [r[1] for r in randB]
    phi = stats_from_hist(hist_of_codes(phi_closed_codes(Lc, rng)), Lc)
    pl = stats_from_hist(hist_of_codes(planted_codes(Lc, rng, 0.05)), Lc)
    fphi, zphi, _ = mann_whitney_lt([phi[1]], randB_E3)
    fpl, zpl, _ = mann_whitney_lt([pl[1]], randB_E3)
    print(f"[power control, L={Lc}, {time.perf_counter()-tc:.0f}s]  random E3 median={med(randB_E3)}")
    print(f"   phi-closed  E3={phi[1]:>10}  P(phi<rand)={fphi:.3f}  {'SEPARATES-LOW' if fphi>0.9 else 'FAIL'}")
    print(f"   planted     E3={pl[1]:>10}  P(planted<rand)={fpl:.3f}  {'SEPARATES-HIGH' if fpl<0.1 else 'FAIL'}")
    print("   -> if both separate, the instrument distinguishes real differences (no null-by-design).")
    print("-" * 84)

    # ---- the actual comparison, per L ------------------------------------
    for L, N in LADDER:
        tL = time.perf_counter()
        A = [stats_from_hist(hist_of_codes(interval_codes(rng.randrange(2, N_ORDER), L)), L) for _ in range(N)]
        B = [stats_from_hist(hist_of_codes(random_set_codes(L, rng)), L) for _ in range(N)]
        print(f"L={L:>6}  N={N}  ({time.perf_counter()-tL:.0f}s)")
        for idx, nm in enumerate(NAMES):
            a = [r[idx] for r in A]; b = [r[idx] for r in B]
            frac, z, U = mann_whitney_lt(a, b)
            ma, mb = med(a), med(b)
            ratio = ma / mb if mb else float('inf')
            tag = ("REAL:int<rand" if frac > 0.70 else
                   "REAL:int>rand" if frac < 0.30 else "no-diff")
            print(f"   {nm}: int-med={ma:>11}  rand-med={mb:>11}  ratio={ratio:5.2f}"
                  f"  P(int<rand)={frac:.3f} z={z:+5.1f}  [{tag}]")
    print("=" * 84)
    print(f"TOTAL WALL TIME: {time.perf_counter()-t0:.0f}s")
    print("Read the artifact: ratio->1 & P~0.5 across L  => bootstrap artifact (dismissal EARNED).")
    print("                   ratio<1 & P->1 growing with L => REAL interval structure (characterize, do NOT dismiss).")


if __name__ == "__main__":
    main()
