"""
Does the GRID compensate as n grows?

The spine is the phi(n) coprime points p/n. The full grid is all n-1 points p/n, and it
grows linearly in n while phi(n) does not. The hypothesis under test:

    as n grows the full grid becomes a better sampler, compensating for the spine's
    declining performance relative to arbitrary window instants.

Measured per n, on the same object and criterion as phi_reach_scale_v2:

    spine     the phi(n) coprime points        (grows like phi(n))
    grid      ALL n-1 points p/n               (grows like n)
    ctrlB     phi(n) arbitrary window instants (grows like phi(n))
    ctrlB+    n-1  arbitrary window instants   (grows like n) -- the matched control,
              so that any grid gain is not just "more shots"

ctrlB+ is the control that decides it. If grid beats ctrlB+ and the margin widens with n,
the grid's ARITHMETIC is compensating. If grid tracks ctrlB+, the gain is only the count.
"""
import random, sys
from math import gcd
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from phi_reach_scale_v2 import (phi, spine_points, readings, clear_at_frac,
                                sample_profile, DEN, selfcheck)

def run(n, cap, M, seed):
    rng = random.Random(seed)
    sp = spine_points(n)
    k = len(sp)
    allp = list(range(1, n))
    tot = hspine = hgrid = hB = hBp = 0
    lo, hi = -(-DEN // n), (n - 1) * DEN // n
    for _ in range(M):
        v = sample_profile(n, cap, rng)
        for i in range(n):
            rs = readings(v, i, n)
            tot += 1
            if any(clear_at_frac(rs, p, n, n) for p in sp):
                hspine += 1
            if any(clear_at_frac(rs, p, n, n) for p in allp):
                hgrid += 1
            if any(clear_at_frac(rs, rng.randint(lo, hi), DEN, n) for _ in range(k)):
                hB += 1
            if any(clear_at_frac(rs, rng.randint(lo, hi), DEN, n) for _ in range(n - 1)):
                hBp += 1
    return tot, hspine, hgrid, hB, hBp

if __name__ == "__main__":
    M0 = int(sys.argv[1]) if len(sys.argv) > 1 else 1200
    selfcheck()
    print()
    NS = [8, 10, 12, 13, 16, 20, 24, 28, 32, 40, 48, 60]
    for mult in (10, 50):
        print(f"=== speeds drawn from [1, {mult}n] ===")
        print(f"{'n':>3} {'phi':>4} {'shots':>11} {'spine':>7} {'grid':>7} "
              f"{'ctrlB':>7} {'ctrlB+':>7} {'grid-ctrlB+':>12}")
        print("-" * 68)
        for n in NS:
            M = max(250, int(M0 * (24 * 24 * 8) / (n * n * max(phi(n), n - 1))))
            tot, hs, hg, hB, hBp = run(n, mult * n, M, seed=6151 * n + mult)
            print(f"{n:>3} {phi(n):>4} {f'{phi(n)} vs {n-1}':>11} {hs/tot:>7.4f} "
                  f"{hg/tot:>7.4f} {hB/tot:>7.4f} {hBp/tot:>7.4f} "
                  f"{(hg-hBp)/tot:>+12.4f}", flush=True)
        print()
