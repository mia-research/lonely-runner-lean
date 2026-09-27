"""Every lonely component of the slowest runner, whole-number readings 1..24, over one period (0, 1] (whole numbers:
period 1, mirror s <-> 1 - s).  Exact, BSM: zones ((k - 1/8)/d, (k + 1/8)/d) open, the clear set closed.

Each component is an interval of positive length, or an isolated point.  An isolated point t0 is a PINCH: some runners
sit exactly at +1/8 (leaving) and some at -1/8 (entering).  SIMPLE pinch = exactly one runner on each edge and every
other runner strictly clear.  MULTI pinch = two or more runners on one edge (two runners at the same place at t0).

Question (A): is there a set whose every lonely instant is a multi pinch (no interval, no simple pinch)?
Also recorded: sets whose lonely set is finite (fragile, E75), and that each simple pinch's mirror 1 - t0 is again a
pinch of the same two runners with roles swapped."""
import itertools
from fractions import Fraction as F
from math import floor, ceil
from collections import Counter
from multiprocessing import Pool

E8 = F(1, 8)
def pos(x): return x - floor(x)

def components(T):
    """closed clear set of T on [0, 1], as a list of (a, b) with a <= b (b == a: isolated point)"""
    zones = []
    for d in T:
        for k in range(0, d + 1):
            lo, hi = (k - E8) / d, (k + E8) / d
            if hi > 0 and lo < 1: zones.append((max(lo, F(0)), min(hi, F(1))))
    zones.sort()
    comps = []; cur = F(0)          # 0 is inside d's zone around k = 0
    # merge open zones; gaps between (closed) are clear
    merged = []
    for lo, hi in zones:
        if merged and lo < merged[-1][1]: merged[-1][1] = max(merged[-1][1], hi)
        else: merged.append([lo, hi])
    for (a0, b0), (a1, b1) in zip(merged, merged[1:]):
        comps.append((b0, a1))      # b0 <= a1: closed gap (touching open zones leave the point itself clear)
    return comps

def edges(T, t):
    lead = [d for d in T if pos(d * t) == E8]; trail = [d for d in T if pos(d * t) == 1 - E8]
    return lead, trail

def study(T):
    comps = [c for c in components(T) if F(0) < c[0] <= F(1, 2)]   # (0, 1/2] suffices by the mirror
    kinds = Counter()
    for a, b in comps:
        if b > a: kinds['interval'] += 1
        else:
            lead, trail = edges(T, a)
            kinds['simple pinch' if len(lead) == 1 and len(trail) == 1 else 'multi pinch'] += 1
    return kinds

def chunk(first):
    c = Counter(); ex = []
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest; k = study(T)
        c['sets'] += 1
        if k['interval'] == 0: c['fragile (no interval in (0,1/2])'] += 1
        if k['interval'] == 0 and k['simple pinch'] == 0:
            c['every lonely instant a multi pinch'] += 1
            if len(ex) < 20: ex.append((T, dict(k)))
        if k['interval'] == 0 and k['simple pinch'] > 0 and len(ex) < 20: ex.append((T, dict(k)))
    return c, ex

if __name__ == '__main__':
    # positive control: the AP readings 1..7 are fragile, lonely only at 1/8, 3/8 (and mirrors), each a simple pinch
    print("control 1..7:", dict(study((1, 2, 3, 4, 5, 6, 7))))
    print("control 1,2,3,4,5,7,12:", dict(study((1, 2, 3, 4, 5, 7, 12))))
    with Pool() as pool: parts = pool.map(chunk, range(1, 19))
    c = Counter(); ex = []
    for a, x in parts: c.update(a); ex += x
    for k, v in c.items(): print(f"{k}: {v}")
    print("fragile sets (readings, component kinds in (0,1/2]):")
    for x in ex[:20]: print("  ", x)
