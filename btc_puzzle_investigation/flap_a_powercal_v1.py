#!/usr/bin/env python3
"""
flap_a_powercal_v1.py -- PC-dep-alpha of PREREG_flap_a_invariance_v1.md section 4.2.

The confirmatory run returned NULL on D_cen/M_cen/theta-bar.  The spec requires the EMPIRICAL
detection floor to be printed with any such null:

  "Sweep alpha in {2^-k : k=3..12}, h in {1, K/4, K}, 100 reps.  Report the smallest firing alpha
   (empirical power >= 0.8) and check it matches the analytic tau_min of section 5."

Plant (spec): independence BACKGROUND (a Null-P realization), then for a in A_plant force the image
label equal to the domain label on the first m = floor(alpha*n) indices.
Analytic: delta = 3*alpha/4, theta_plant ~ 4*alpha, tau^2 = (h/K)(1-h/K)(4*alpha)^2.

B is reduced to 999 for the sweep ONLY (min p = 1/1000 < alpha* = 1/60, so the decision threshold is
unaffected); disclosed as DEVIATION D4.  Usage: flap_a_powercal_v1.py [n] [B] [reps]
"""
import sys
import numpy as np
from flap_a_invariance_v1 import (sample_a, build_pool, labels, dev_vector, stats, fires,
                                  SEED_POOL, K, ALPHA_NUM, ALPHA_DEN)


def main():
    n_req = int(sys.argv[1]) if len(sys.argv) > 1 else 1000000
    B = int(sys.argv[2]) if len(sys.argv) > 2 else 999
    reps = int(sys.argv[3]) if len(sys.argv) > 3 else 100

    As = sample_a()
    Xs, X2s = build_pool(n_req, SEED_POOL)
    n = len(Xs)
    DOM, IMG = labels(As, Xs, X2s)
    print("# PC-dep-alpha  n=%d  B=%d  reps=%d  K=%d" % (n, B, reps, K))

    rng = np.random.default_rng(7770001)

    # ---- null ensemble for D_cen (the statistic under calibration)
    nullD = []
    for _ in range(B):
        perm = rng.permutation(n)
        d, _, _ = stats(dev_vector(DOM, IMG, perm))
        nullD.append(d)
    nullD.sort()
    print("# null ensemble built (B=%d)" % B)

    def rank_of(v):
        lo, hi = 0, len(nullD)
        while lo < hi:
            mid = (lo + hi) // 2
            if nullD[mid] < v:
                lo = mid + 1
            else:
                hi = mid
        return len(nullD) - lo          # count of null draws >= v

    print("\n  h      alpha        m        power(D_cen)   analytic tau=sqrt(h/K(1-h/K))*4a")
    results = {}
    for h in (K // 4, 1, K):
        A_plant = list(range(h))
        for k in range(3, 13):
            alpha_num, alpha_den = 1, 1 << k
            m = n // alpha_den
            if m < 1:
                continue
            hits = 0
            for _ in range(reps):
                perm = rng.permutation(n)
                J = IMG[:, perm].copy()               # independence background
                for ai in A_plant:
                    J[ai, :m] = DOM[ai, :m]           # forced agreement on first m indices
                d, _, _ = stats(dev_vector(DOM, J))
                if fires(rank_of(d), B):
                    hits += 1
            frac = h / K
            tau = (frac * (1 - frac)) ** 0.5 * 4.0 / alpha_den
            print("  %-6d 2^-%-2d  %-9d %3d/%-3d = %.2f   %.2e"
                  % (h, k, m, hits, reps, hits / reps, tau))
            results[(h, k)] = hits / reps
            if hits / reps < 0.8 and k > 3:
                break                                  # power is monotone decreasing in k
    print("\n# smallest firing alpha per h (empirical power >= 0.8):")
    for h in (K // 4, 1, K):
        ks = [k for (hh, k), pw in results.items() if hh == h and pw >= 0.8]
        if ks:
            k = max(ks)
            frac = h / K
            tau = (frac * (1 - frac)) ** 0.5 * 4.0 / (1 << k)
            print("   h=%-3d  alpha_min = 2^-%-2d = %.3e   => tau_min(empirical) = %.3e"
                  % (h, k, 1.0 / (1 << k), tau))
        else:
            print("   h=%-3d  no alpha in the swept range reached power 0.8" % h)
    print("POWERCAL_DONE")


if __name__ == '__main__':
    main()
