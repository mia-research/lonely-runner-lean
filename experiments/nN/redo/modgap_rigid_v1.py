"""modgap_rigid_v1 (2026-10-06): structure of the sets with no lonely instant at 1/7 (the 30 of modgap_neartight_v2.out and the 24 of modgap_neartight_v1.out).  For each such S and each d: T_d = S minus d; the
lonely set L_7(T_d) on one period [0, 1) as the exact list of components (cascade walk at 1/7 from 1/(7 d_min), component ends at the least exit, next start from the closers' next-lap edges; mirror
symmetry t -> 1 - t is not used).  Recorded: the number of components in [0, 1), how many are single points (width 0), and whether d is blocked (< 1/7) on every component (this is what 'S has no
1/7-lonely instant' means for d).  Then: the d for which L_7(T_d) is a finite set of points ('rigid six-set at 1/7'); for such d, the points as exact fractions.  Exact."""
import sys, itertools, math, collections, re
sys.path.insert(0, '.')
from fractions import Fraction as F
H = F(1, 7)
def cd(x):
    x = x - math.floor(x); return min(x, 1 - x)
def cascade7(T, t):
    while True:
        B = [x for x in T if cd(x * t) < H]
        if not B: return t
        t = max(F(7 * round(x * t) + 1, 7 * x) for x in B)
def comps7(T, limit=F(1)):
    t = cascade7(T, F(1, 7 * min(T))); out = []
    while t < limit:
        best = None
        for x in T:
            N = math.ceil(x * t - F(6, 7)); e = (N + F(6, 7)) / x
            if best is None or e < best[0]: best = (e, [x])
            elif e == best[0]: best[1].append(x)
        r, cl = best; out.append((t, r))
        Fs = [F(7 * (math.floor(x * r - F(6, 7)) + 1) + 1, 7 * x) for x in cl]
        t = cascade7(T, max(Fs))
    return out
def blocked_on(d, l, r):
    # d is < 1/7 from the integers on all of [l, r] iff [l, r] lies in one open window around an integer N
    N = round(d * l)
    return abs(d * l - N) < H and abs(d * r - N) < H and all(abs(d * x - N) < H for x in (l, r))
src = open('modgap_neartight_v2.out').read() + open('modgap_neartight_v1.out').read()
sets = sorted({tuple(map(int, m.group(1).split(','))) for m in re.finditer(r'primitive: \(([\d, ]+)\)', src)})
out = open('modgap_rigid_v1.out', 'w'); out.write(__doc__ + "\n")
for S in sets:
    line = []
    rigid_d = []
    for d in S:
        T = [x for x in S if x != d]; C = comps7(T)
        pts = sum(1 for l, r in C if l == r)
        allblocked = all(blocked_on(d, l, r) for l, r in C if l <= F(1))
        line.append((d, len(C), pts, allblocked))
        if C and pts == len(C): rigid_d.append(d)
    out.write("S=%s\n  per d: (d, #components in [0,1), #single points, d blocked on every component): %s\n  d with L_7(S minus d) finite: %s\n" % (S, line, rigid_d))
    for d in rigid_d:
        T = [x for x in S if x != d]
        out.write("    L_7(%s) in [0,1): %s\n" % (tuple(T), [str(l) for l, r in comps7(T)]))
out.close(); print(open('modgap_rigid_v1.out').read()[len(__doc__):][:7000])
