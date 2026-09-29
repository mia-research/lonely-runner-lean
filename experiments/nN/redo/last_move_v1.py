"""E185 (2026-09-30): the window (B) at the target, read on the path route's last move.

Owner: "work on the window (B) on the path route making sure it is compliant to the framework, no density, no coverage,
boundaries and isolation events and cascade as the oracle".

From the Lean (PathRouteN.segment_lonely, DeformationN.lonely_along_path) and E116: on a move, the window holds exactly
when every lattice point on it is lonely (off the lattice OneFreeN places the event; at a lonely lattice point
move_one_strict / move_one_period keep nearby points lonely at its own instant or its mirror, inside its period).  The
target is a lattice point of the last move.  So (B) at the target is the target's own isolation event, seen from the
last move: six readings fixed, one reading (the mover) arriving.

In boundaries and events: the six fixed readings have their own clear set F at 1/8 (their isolation is native order
seven, at 1/7, so F has intervals with room).  The target's event t* (the cascade's landing on all seven) lies in one of
F's intervals.  Recorded exactly, for every set of seven readings in 1..24 and every choice of mover (the path route may
move the runners in any order, E115 O4):
  j        the index, in time order, of the F-interval holding t* (j = 1: the six's first clear interval);
  where    t* is F-interval's left end (a boundary of the six, the mover clear there) or the mover's opening inside it.
Derived check (R8's mechanism, reasoned): a mover faster than 7 x every fixed reading cannot fit the six's order-seven
interval inside one of its slots, so j = 1 for it.  Each F-interval with index < j lies inside one slot of the mover
(it is where the mover is in the way throughout); checked exactly for every such interval.
"""
import itertools, math
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from quantity_tests_v1 import cd, E8
from wave_incident_v1 import lonely_components
from place_incidents_v1 import cascade


def study(first):
    out = []
    for rest in itertools.combinations(range(first + 1, 25), 6):
        S = (first,) + rest
        ts, n = cascade(S)
        per = {}
        for mi, x in enumerate(S):
            six = [d for d in S if d != x]
            comps = [c for c in lonely_components(six, F(0), F(1) + ts) if c[1] > 0]
            idx = next(i for i, (a, b) in enumerate(comps) if a <= ts <= b)
            a, b = comps[idx]
            where = 'left end' if ts == a else ('mover opening' if (x * ts - math.floor(x * ts)) == E8 else 'other')
            swallowed_ok = all(math.floor(x * lo + F(1, 8)) == math.ceil(x * hi - F(1, 8)) and
                               cd(x * lo) < E8 and cd(x * hi) < E8 for lo, hi in comps[:idx])
            per[mi] = (idx + 1, where, swallowed_ok, x > 7 * max(six))
        out.append((S, ts, per))
    return out


if __name__ == '__main__':
    with Pool(8) as pool:
        rows = [r for part in pool.map(study, range(1, 19)) for r in part]
    out = open('last_move_v1.out', 'w'); out.write(__doc__ + "\n")
    out.write("sets: %d\n" % len(rows))
    fast = Counter(); fastj = Counter(); swallow_bad = 0; where_fast = Counter(); where_any = Counter()
    minj = Counter(); best_mover = Counter(); r8 = Counter()
    for S, ts, per in rows:
        j6, w6, ok6, big6 = per[6]
        fastj[j6] += 1; where_fast[w6] += 1
        swallow_bad += sum(1 for v in per.values() if not v[2])
        m = min(v[0] for v in per.values()); minj[m] += 1
        best_mover[tuple(mi for mi, v in per.items() if v[0] == 1)] += 0
        best_mover[min(mi for mi, v in per.items() if v[0] == m)] += 1
        for mi, v in per.items():
            if v[3]:
                r8[v[0] == 1] += 1
            where_any[v[1]] += 1
    out.write("mover = the fastest reading: j %s; where %s\n" % (dict(sorted(fastj.items())), dict(where_fast)))
    out.write("over all seven choices of mover, the least j per set: %s\n" % dict(sorted(minj.items())))
    out.write("the lowest-rank mover attaining the least j: %s\n" % dict(sorted((k, v) for k, v in best_mover.items() if isinstance(k, int))))
    out.write("where t* sits in its F-interval (all movers): %s\n" % dict(where_any))
    out.write("CHECK every F-interval before t*'s lies inside one slot of the mover: %d violations\n" % swallow_bad)
    out.write("CHECK mover > 7 x every fixed reading => j = 1: %s\n" % dict(r8))
    no1 = [(S, float(8 * S[0] * ts), {mi: v[0] for mi, v in per.items()}) for S, ts, per in rows if min(v[0] for v in per.values()) > 1]
    out.write("sets where no choice of mover gives j = 1: %d; first 20: %s\n" % (len(no1), no1[:20]))
    out.close()
    print(open('last_move_v1.out').read()[len(__doc__):])
