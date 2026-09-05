#!/usr/bin/env python3
"""incomplete_sum_2p128_firstorder_v1.py -- the first-order test on the object with no Weil bound.

OBJECT.   T(d0) = sum_{i<W} chi_2(x_{[d0+i]G})  on secp256k1, d0 at the 2^128 scale.
          Purely curve-native: no GLV, no lattice, no rounding, no covariate.
          In scope: tests how the CURVE converts a bounded integer neighbourhood into points.
          Nothing depends on how any d0 was selected -- the d0 are constructed here.

WHY THIS FIRST.  Every covariate test asks "does T correlate with X".  If T is distributed exactly
as an iid sum, every such correlation is bounded before you look.  If it is NOT, that is the finding
and no covariate was needed.  The regime is open precisely because complete-sum bounds are vacuous
for W << sqrt(p): the Weil/Hasse bound controls the sum over the WHOLE group, and Polya-Vinogradov
completion costs sqrt(p) log p ~ 2^128 * 256, which exceeds W by ~2^128.

MATCHED NULL (marginal-exact).  Pool every observed readout value across all intervals, shuffle the
pool globally, re-block into M intervals of width W, recompute T.  This preserves the empirical
marginal of chi_2(x) EXACTLY -- so a global bias in the readout cannot manufacture a result -- while
destroying any WITHIN-interval correlation.  Local structure is exactly what "the sequence is not
random here" means.

STATISTICS (pre-committed, all compared to the same null):
  S1  Var(T)                 -- within-interval correlation inflates or deflates it
  S2  max |T|                -- tail / caustic behaviour
  S3  mean(T)                -- systematic drift
  S4  lag-1 autocorrelation of the readout WITHIN intervals
CONTROLS:
  C-MARGINAL  the readout's global bias, reported (the null matches it by construction)
  C-PLANT     inject within-interval correlation and confirm every statistic that should fire, fires

Exact integer arithmetic in the signal path; float only in reported summary ratios.
"""

import random
import sys

P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
A, Bc = 0, 7
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8


def padd(Pt, Q):
    if Pt is None:
        return Q
    if Q is None:
        return Pt
    x1, y1 = Pt
    x2, y2 = Q
    if x1 == x2 and (y1 + y2) % P == 0:
        return None
    if Pt == Q:
        num, den = (3*x1*x1 + A) % P, (2*y1) % P
    else:
        num, den = (y2 - y1) % P, (x2 - x1) % P
    lm = num * pow(den, P - 2, P) % P
    x3 = (lm*lm - x1 - x2) % P
    return (x3, (lm*(x1 - x3) - y1) % P)


def pmul(d, Pt):
    R, Q = None, Pt
    while d:
        if d & 1:
            R = padd(R, Q)
        Q = padd(Q, Q)
        d >>= 1
    return R


def chi2(a):
    a %= P
    return 0 if a == 0 else (1 if pow(a, (P - 1)//2, P) == 1 else -1)


def gather(M, W, seed, lo, hi):
    """M intervals of width W, starting points drawn in [lo,hi).  Returns list of readout lists."""
    rng = random.Random(seed)
    G = (Gx, Gy)
    out = []
    for j in range(M):
        d0 = rng.randrange(lo, hi)
        cur = pmul(d0, G)
        row = []
        for _ in range(W):
            row.append(chi2(cur[0]))
            cur = padd(cur, G)
        out.append(row)
        if (j + 1) % 25 == 0:
            print("      ... %d/%d intervals" % (j + 1, M), flush=True)
    return out


def stats(rows):
    M, W = len(rows), len(rows[0])
    T = [sum(r) for r in rows]
    mean_num = sum(T)
    var_num = M*sum(t*t for t in T) - mean_num*mean_num       # M^2 * variance, exact integer
    mx = max(abs(t) for t in T)
    lag = sum(r[i]*r[i+1] for r in rows for i in range(W - 1))
    return T, mean_num, var_num, mx, lag


def null_draws(rows, R, seed):
    M, W = len(rows), len(rows[0])
    pool = [v for r in rows for v in r]
    rng = random.Random(seed)
    out = []
    for _ in range(R):
        rng.shuffle(pool)
        nr = [pool[i*W:(i+1)*W] for i in range(M)]
        out.append(stats(nr))
    return out


def report(label, rows, R=400, seed=999):
    M, W = len(rows), len(rows[0])
    T, mean_num, var_num, mx, lag = stats(rows)
    nd = null_draws(rows, R, seed)
    def pval(obs, idx, two_sided=True):
        vals = [d[idx] for d in nd]
        if two_sided:
            ge = sum(1 for v in vals if abs(v) >= abs(obs))
        else:
            ge = sum(1 for v in vals if v >= obs)
        return ge + 1, R + 1
    print("   %s  (M=%d intervals, W=%d)" % (label, M, W))
    print("      C-MARGINAL: readout balance +1 x %d, -1 x %d  (null matches this exactly)"
          % (sum(1 for r in rows for v in r if v == 1),
             sum(1 for r in rows for v in r if v == -1)))
    for nm, obs, idx, ts in (("S1 Var(T)  ", var_num, 2, False),
                             ("S2 max|T|  ", mx, 3, False),
                             ("S3 mean(T) ", mean_num, 1, True),
                             ("S4 lag-1   ", lag, 4, True)):
        a, b = pval(obs, idx, ts)
        flag = "  <-- fires" if a*20 <= b else ""
        print("      %s obs = %-22d exact perm p = %d/%d%s" % (nm, obs, a, b, flag))
    return T


if __name__ == "__main__":
    M = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    W = int(sys.argv[2]) if len(sys.argv) > 2 else 256
    print("=" * 92)
    print("INCOMPLETE CHARACTER SUM AT 2^128 -- FIRST-ORDER TEST")
    print("=" * 92)
    print("   gathering real intervals at the 2^128 scale (exact curve arithmetic)...", flush=True)
    rows = gather(M, W, seed=20260801, lo=2**127, hi=2**128)
    print()
    report("REAL DATA, d0 in [2^127, 2^128)", rows)

    print()
    print("   C-PLANT: same data, but each interval's second half forced to agree with its first")
    print("   value (a strong within-interval correlation). Every statistic sensitive to local")
    print("   structure must fire.")
    planted = []
    for r in rows:
        v = r[0]
        planted.append(r[:W//2] + [v]*(W - W//2))
    report("PLANTED", planted)
