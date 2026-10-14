"""ok_transit_periods_v1 — isolation PERIODS along a transit, in original time.

n = 8, individual isolation.  For each position of a one-runner transit and each
runner, record the actual isolation windows: how many, how long each is, and the
total, expressed in ORIGINAL time (the speeds as given), not in the reduced
configuration's stretched time.

Two traps this is built to avoid.

  1. Scaled time (WB_window_trajectories sec 0).  Reducing a configuration whose
     moved speed has denominator q stretches the period by ~q, so window counts
     and widths taken in reduced time are not comparable across positions.  Here
     the reduced solution is mapped back: original-time period P = L/g, and every
     window is scaled by P.

  2. Sampling resolution (TRANSIT_FRACTIONAL_v1 sec 1).  A uniform step of 1/k
     visits only denominators dividing k -- the small-denominator points, which
     are the local minima.  Here positions are the Farey fractions of order Q, so
     every denominator up to Q appears.

BSM throughout: boundary points and open-cell midpoints evaluated separately, so
isolated witnesses (gap exactly 1/n) survive.  Exact Fraction arithmetic.
"""
from fractions import Fraction as F
from math import gcd
from functools import reduce

N = 8

def reduce_config(speeds, i):
    """Integer constraint multipliers for runner i, and the original-time period."""
    ds = [abs(speeds[i] - v) for j, v in enumerate(speeds) if j != i]
    if any(d == 0 for d in ds):
        return None, None
    L = reduce(lambda a, b: a * b // gcd(a, b), [d.denominator for d in ds], 1)
    D = [int(d * L) for d in ds]
    g = reduce(gcd, D)
    return [d // g for d in D], F(L, g)      # multipliers, period P

def windows(mult):
    """Maximal components of {s in [0,1) : ||m s|| >= 1/N for all m}, exact."""
    pts = {F(0)}
    for m in mult:
        for k in range(m + 1):
            for x in (F(k, m) + F(1, N * m), F(k, m) - F(1, N * m)):
                if 0 <= x < 1:
                    pts.add(x)
    pts = sorted(pts)
    ok = lambda s: all(min((m * s) % 1, 1 - ((m * s) % 1)) >= F(1, N) for m in mult)
    segs = []
    for idx, a in enumerate(pts):
        if ok(a):
            segs.append((a, a))
        b = pts[idx + 1] if idx + 1 < len(pts) else F(1)
        if b > a and ok((a + b) / 2):
            segs.append((a, b))
    merged = []
    for s in segs:
        if merged and s[0] <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(merged[-1][1], s[1]))
        else:
            merged.append(s)
    return merged

def runner_record(speeds, i):
    mult, P = reduce_config(speeds, i)
    if mult is None:
        return None
    w = windows(mult)
    widths = [(b - a) * P for a, b in w]          # ORIGINAL time
    return {
        "period": P,
        "count": len(w),
        "total": sum(widths),                      # isolated time per period
        "density": sum(b - a for a, b in w),       # fraction of period
        "longest": max(widths) if widths else F(0),
        "shortest": min(widths) if widths else F(0),
        "first": w[0][0] * P if w else None,
    }

def farey(Q):
    """Farey fractions of order Q in [0,1]."""
    out = set()
    for q in range(1, Q + 1):
        for p in range(0, q + 1):
            out.add(F(p, q))
    return sorted(out)
