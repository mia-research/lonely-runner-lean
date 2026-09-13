"""
Is a spine miss a property of the POINT SET or of the RUNNER?

k_eff in phi_reach_scale_v2 saturates near 2-3 while phi(n) runs to 12, which
says the phi shots are heavily correlated.  Two rival readings:

  (i)  the spine points are correlated with each other -- a point-set fact;
  (ii) a fixed fraction of runner-instances is blocked at every point in the
       whole window -- a runner fact, and no point set would rescue them.

The separator: take the instances the spine MISSES and sweep the entire window
on a fine exact grid.  Under (i) many of them are clear somewhere in the window.
Under (ii) almost none are.

Exact integer arithmetic; the window is [1/n, (n-1)/n]; zones are open so the
comparisons are non-strict.
"""
import random, sys
from math import gcd
from collections import Counter

sys.path.insert(0, __file__.rsplit('/', 1)[0])
from phi_reach_scale_v2 import (phi, spine_points, readings, clear_at_frac,
                                sample_profile)

GRID = 55440        # 2^4*3^2*5*7*11 -- divisible by every n tested

def window_clear_count(rs, n, D=GRID):
    lo, hi = -(-D // n), (n - 1) * D // n
    return sum(1 for c in range(lo, hi + 1) if clear_at_frac(rs, c, D, n))

def run(n, cap, M, seed):
    rng = random.Random(seed)
    sp = spine_points(n)
    miss = 0
    miss_but_window_clear = 0
    miss_widths = Counter()
    tot = 0
    for _ in range(M):
        v = sample_profile(n, cap, rng)
        for i in range(n):
            rs = readings(v, i, n)
            tot += 1
            if any(clear_at_frac(rs, p, n, n) for p in sp):
                continue
            miss += 1
            c = window_clear_count(rs, n)
            if c > 0:
                miss_but_window_clear += 1
                miss_widths[min(c, 9)] += 1
    return tot, miss, miss_but_window_clear, miss_widths

if __name__ == "__main__":
    M = int(sys.argv[1]) if len(sys.argv) > 1 else 150
    print(f"M = {M} profiles per n;  window swept on a 1/{GRID} exact grid")
    print()
    print(f"{'n':>3} {'phi':>4} {'inst':>6} {'spine miss':>11} {'of those, clear '
          'somewhere in window':>36}")
    print("-" * 60)
    for n in (8, 10, 11, 12, 13, 15, 16, 21):
        for mult in (10, 50):
            tot, miss, ok, _ = run(n, mult * n, M, seed=31 * n + mult)
            frac = ok / miss if miss else float('nan')
            print(f"{n:>3} {phi(n):>4} {tot:>6} {miss:>6} ({miss/tot:>6.3f}) "
                  f"{ok:>8} ({frac:>6.3f})   span {mult}n")
