"""Owner: the isolation is displaced to somewhere else in the geometry.  At a pinch-off the landing component already
exists (pinchoff_v1: positive length at s* in 1,753 of 1,753), so the displacement is to another lonely place that the
geometry already holds.  Measure it: at every pinch-off s* of pinchoff_v1's 85 paths, list the lonely components of the
slowest runner with R = 8 d_min t in [1, 15] (exact, BSM: blocked set = union of open zones; clear set closed), and
record how many there are besides the pinching one, and which of them the isolation lands on (the next one after the
pinched instant, or a later one)."""
from fractions import Fraction as F
from math import floor, ceil
from pinchoff_v1 import targets, readings_at, study, EIGHTH

def components(ds, Rmax=15):
    """closed clear intervals of all readings within t in [1/(8 d_min), Rmax/(8 d_min)], exact"""
    t0, t1 = EIGHTH / ds[0], F(Rmax, 8) / ds[0]
    Z = []
    for d in ds:
        for k in range(floor(d * t0 - EIGHTH), ceil(d * t1 + EIGHTH) + 1):
            Z.append(((k - EIGHTH) / d, (k + EIGHTH) / d))
    Z.sort(); comps = []; cur = t0
    for lo, hi in Z:
        if hi <= cur: continue
        if lo >= cur:                       # clear on [cur, lo] (closed); touching open zones leave the point clear
            if lo <= t1: comps.append((cur, lo))
        cur = max(cur, hi)
        if cur > t1: break
    if cur <= t1: comps.append((cur, t1))
    R = lambda t: 8 * ds[0] * t
    return [(R(a), R(b)) for a, b in comps]

def run(args):
    name, V = args
    D1 = [F(v - V[0]) for v in V[1:]]; W = D1[-1]; D0 = [W * j / 7 for j in range(1, 8)]
    out = []
    for r in study(D0, D1):
        if r['kind'] != 'pinch': continue
        ds = readings_at(D0, D1, r['sstar'])
        C = components(ds)
        # the pinched component is the single point R*; the landing is R_land
        others = [c for c in C if not (c[0] == c[1] == r['Rstar'])]
        idx = next((i for i, c in enumerate(others) if c[0] <= r['Rland'] <= c[1]), None)
        after = [c for c in others if c[0] > r['Rstar']]
        first = bool(after) and after[0][0] <= r['Rland'] <= after[0][1]
        out.append((name, float(r['Rstar']), float(r['Rland']), len(others), len(after), first,
                    [(round(float(a), 3), round(float(b), 3)) for a, b in others[:6]]))
    return out

if __name__ == '__main__':
    from multiprocessing import Pool
    from collections import Counter
    with Pool() as pool:
        res = [x for part in pool.map(run, targets()) for x in part]
    print(f"pinch-offs {len(res)}")
    print(" lonely components in R in [1,15] besides the pinched point, at s*:", sorted(Counter(min(r[3], 20) for r in res).items()))
    print(" of which after the pinched instant:", sorted(Counter(min(r[4], 20) for r in res).items()))
    print(" the landing is the first component after the pinch:", sum(r[5] for r in res), "of", len(res))
    few = sorted(res, key=lambda r: r[4])[:12]
    for r in few:
        print(f"  {r[0]:24s} pinch at R {r[1]:.4f} -> R {r[2]:.4f}; components besides it {r[3]}, after it {r[4]}; first ones {r[6]}")
