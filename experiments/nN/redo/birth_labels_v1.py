"""Owner: "test the cascade and find out" what "runners are always bound by their neighbours' speed" does to the
isolation.  Part 1: which runners open (birth) and close (pinch-off) the lonely stretches of the slowest runner along the
55 paths of lineage_v1 (grid 300; exact).  A stretch is opened by a zone exit of runner a and closed by a zone entry of
runner b; runners are indexed by speed rank (the slowest runner's readings keep the speed order, reading j = speed j+1).
Report the pair (a, b) of every birth and every pinch-off, whether a and b are neighbours in speed (|a - b| = 1), or the
subject's two circle neighbours (the next-slowest, reading 0, and the fastest, reading 6), and where in R it happens."""
import sys
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from lineage_v1 import stretches
from pinchoff_v1 import targets, readings_at

def events(args):
    name, V = args; N = 300
    D1 = [F(v - V[0]) for v in V[1:]]; W = D1[-1]; D0 = [W * j / 7 for j in range(1, 8)]
    prev = None; out = []
    for i in range(1, N + 1):
        S = stretches(readings_at(D0, D1, F(i, N)))
        if prev is not None:
            used = set()
            for (a, b, L, Rt) in S:
                m = [q for q, x in enumerate(prev) if (x[2] == L or x[3] == Rt) and q not in used]
                if m: used.add(m[0])
                elif L[0] != 'W' and Rt[0] != 'W': out.append(('birth', L[0], Rt[0], float(a)))
            for q, x in enumerate(prev):
                if q not in used and x[2][0] != 'W' and x[3][0] != 'W': out.append(('pinch', x[2][0], x[3][0], float(x[0])))
        prev = S
    return out

if __name__ == '__main__':
    T = [t for t in targets() if t[0].startswith('random') or 'W30' in t[0]]
    with Pool() as pool: ev = [e for part in pool.map(events, T) for e in part]
    for kind in ('birth', 'pinch'):
        E = [e for e in ev if e[0] == kind]
        diff = Counter(abs(e[1] - e[2]) for e in E)
        circ = sum(1 for e in E if {e[1], e[2]} == {0, 6})
        print(f"{kind}s {len(E)}: |a - b| in speed rank {sorted(diff.items())}; the subject's circle neighbours (0, 6): {circ}")
        print(f"   opened/closed by (exit a, entry b), most common: {Counter((e[1], e[2]) for e in E).most_common(10)}")
        print(f"   R where it happens: <7 {sum(e[3] < 7 for e in E)}, 7..9 {sum(7 <= e[3] <= 9 for e in E)}, >9 {sum(e[3] > 9 for e in E)}")
