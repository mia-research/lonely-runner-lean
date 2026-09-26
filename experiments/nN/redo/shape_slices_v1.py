"""(b) measured on 2-D slices of the shape space through the AP.  Speeds c + cumulative gaps, all gaps 1 (the AP)
except two, each ranging over k/16, k = 1..128 (1/16 .. 8).  Exact.  For every shape and every runner: the cascade's
event t*, and its CONE = (flank rank, lap j, band M of every reading at the scale e/(8j+1)), where a reading r is
clear in band M iff 8M+1 <= r <= 8M+7 (Thm 6.12).  Measured per slice: number of distinct cones (per runner, total),
how many shapes the smallest cones hold, and how the count grows towards the edges (a gap -> 0: two runners merge;
a gap -> 8: an outlier).  Every runner is lonely at its event by construction; the object is the COUNT of cones."""
import sys
from fractions import Fraction as F
from math import floor
from collections import Counter, defaultdict

def nd(x): x = x % 1; return min(x, 1 - x)

def event(V, k):
    ds = [abs(v - V[k]) for j, v in enumerate(V) if j != k]
    t = F(1, 8 * min(ds))
    while True:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: return t
        t = max((F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way)

def cone(V, k, t):
    ranks = [i for i in range(8) if i != k and (abs(V[i] - V[k]) * t) % 1 == F(1, 8)]
    f = min(ranks); e = abs(V[f] - V[k]); j = floor(e * t)
    Ms = tuple(floor(((8 * j + 1) * abs(V[i] - V[k]) / e - 1) / 8) if i != k else None for i in range(8))
    return (f, j, Ms)

def run(slot_a, slot_b, label):
    vals = [F(i, 16) for i in range(1, 129)]
    labels = defaultdict(Counter); where = defaultdict(list)
    for ga in vals:
        for gb in vals:
            g = [F(1)] * 7; g[slot_a] = ga; g[slot_b] = gb
            V = [F(100)]
            for x in g: V.append(V[-1] + x)
            for k in range(8):
                c = cone(V, k, event(V, k))
                labels[k][c] += 1; where[(k, c)].append((ga, gb))
    print(f"\n== slice {label}: gaps {slot_a+1} and {slot_b+1} over 1/16..8, {len(vals)**2} shapes, every runner")
    tot = sum(len(labels[k]) for k in range(8))
    print(f"   distinct cones: total {tot};  per runner " + ", ".join(f"r{k}: {len(labels[k])}" for k in range(8)))
    sizes = sorted(n for k in range(8) for n in labels[k].values())
    print(f"   shapes per cone: smallest {sizes[:8]}, median {sizes[len(sizes)//2]}, largest {sizes[-1]}")
    print(f"   cones holding a single shape: {sum(1 for s in sizes if s == 1)}")
    js = Counter(c[1] for k in range(8) for c in labels[k])
    print(f"   laps j used: {dict(sorted(js.items()))}")
    # growth towards the edges: cones needed within bands of min(ga,gb)
    for lo, hi in [(F(1,16), F(1,8)), (F(1,8), F(1,4)), (F(1,4), F(1,2)), (F(1,2), F(2)), (F(2), F(4)), (F(4), F(8)+1)]:
        cs = {(k, c) for (k, c), pts in where.items() for (ga, gb) in pts if lo <= min(ga, gb) < hi}
        cs2 = {(k, c) for (k, c), pts in where.items() for (ga, gb) in pts if lo <= max(ga, gb) < hi}
        print(f"   smaller gap in [{float(lo):.4g}, {float(hi):.4g}): {len(cs)} cones;   larger gap there: {len(cs2)} cones")

if __name__ == '__main__':
    run(0, 1, "A (both gaps at one end)")
    run(3, 4, "B (the two middle gaps)")
