"""E187 (2026-09-30): the 971 sets of E185 run through the cascade -- why every mover swallows the six's first clear
interval, named in boundaries and events.

Owner: "yes run the 971 through the cascade".

Objects (all exact, all from the readings; no density, no coverage):
  t*            the cascade's landing on the seven (the oracle), from the bound 1/(8 d_min).
  near-miss     a closed interval I before t* on which six readings are clear and the seventh, m, is in the way
                throughout.  Every clear interval of the six (m removed) that ends before t* is one (derived: the seven are
                clear nowhere before t*, and m's in-the-way set is a union of disjoint open slots, so a connected closed
                interval where m is always in the way lies in ONE slot of m, lap k: (k - 1/8)/m < a <= b < (k + 1/8)/m).
  first near-miss of m   the six's first clear interval, when it ends before t* (E185: j(m) >= 2).
The 971 are exactly the sets where EVERY runner has a first near-miss before t* (E185: least j >= 2).  For each set:
  * each runner's first near-miss [a, b]: the reading opening it (phase 1/8 at a), the one closing it (phase 7/8 at b),
    m's lap k, and the two slacks m*a - (k - 1/8), (k + 1/8) - m*b (both > 0 by the derivation; checked);
  * the time order of the seven first near-misses, and every near-miss before t* (all runners, all intervals);
  * the cascade's moves from the bound: at each, the readings in the way and the setter(s); whether each first
    near-miss is VISITED by the cascade (some move time in it) or jumped;
  * t*'s boundaries: the host (opening at t*) and the closer (first closing after t*);
  * E174's place of t* (S0 a named view / S1 one separation from one / miss).
CHECKs (derived, must hold): every near-miss lies inside one slot of its blocker; the seven first near-misses are
pairwise disjoint (in one, m blocks and m' is clear; in the other, m' blocks); the cascade's landing equals the first
lonely instant of the seven (oracle check).
"""
import itertools, math, json
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from quantity_tests_v1 import cd, E8
from wave_incident_v1 import lonely_components
from place_incidents_v1 import cascade, move, place, boundaries


def frac(x):
    return x - math.floor(x)


def first_near_misses(S, ts):
    rec = {}
    for mi, x in enumerate(S):
        six = [d for d in S if d != x]
        comps = [c for c in lonely_components(six, F(0), ts) if c[1] > 0]
        before = [c for c in comps if c[1] < ts]
        rec[mi] = before
    return rec


def screen(first):
    out = []
    for rest in itertools.combinations(range(first + 1, 25), 6):
        S = (first,) + rest
        ts, n = cascade(S)
        nm = first_near_misses(S, ts)
        if all(nm[mi] for mi in range(7)):
            out.append(S)
    return out


def trace(S):
    t = F(1, 8 * S[0]); moves = []
    while True:
        way = [d for d in S if cd(d * t) < E8]
        nx, setters = move(S, t)
        if setters is None:
            return t, moves
        moves.append((t, tuple(way), tuple(setters), nx))
        t = nx


def analyse(S):
    ts, moves = trace(S)
    nm = first_near_misses(S, ts)
    first = {}
    ok_slot = True
    for mi, x in enumerate(S):
        a, b = nm[mi][0]
        k = math.floor(x * a + F(1, 2))
        s1, s2 = x * a - (k - E8), (k + E8) - x * b
        ok_slot &= (s1 > 0 and s2 > 0)
        opener = [d for d in S if d != x and frac(d * a) == E8]
        closer = [d for d in S if d != x and frac(d * b) == F(7, 8)]
        visited = [i for i, (t, way, st, nx) in enumerate(moves) if a <= t <= b]
        first[mi] = dict(a=a, b=b, k=k, s1=s1, s2=s2, opener=opener, closer=closer, visited=visited)
    order = sorted(range(7), key=lambda mi: first[mi]['a'])
    disjoint = all(first[p]['b'] < first[q]['a'] for p, q in zip(order, order[1:]))
    allnm = sorted((c[0], c[1], mi) for mi in range(7) for c in nm[mi])
    comps7 = [c for c in lonely_components(list(S), F(1, 8 * S[0]), ts + 2) if c[1] >= c[0]]
    oracle = bool(comps7) and comps7[0][0] == ts
    bd = boundaries(list(S), ts)
    return dict(S=S, ts=ts, R=8 * S[0] * ts, moves=moves, first=first, order=order, disjoint=disjoint,
                ok_slot=ok_slot, allnm=allnm, oracle=oracle, host=bd['host'], closer=bd['closer'],
                place=place(list(S), ts)[:2])


if __name__ == '__main__':
    with Pool(8) as pool:
        sets = [S for part in pool.map(screen, range(1, 19)) for S in part]
        recs = pool.map(analyse, sets)
    json.dump([r['S'] for r in recs], open('swallow_971_v1_sets.json', 'w'))
    o = open('swallow_971_v1.out', 'w'); o.write(__doc__ + "\n")
    w = lambda s: o.write(s + "\n")
    w("sets: %d" % len(recs))
    w("CHECK oracle (landing = first lonely instant): %d violations" % sum(not r['oracle'] for r in recs))
    w("CHECK every first near-miss inside one slot of its blocker: %d violations" % sum(not r['ok_slot'] for r in recs))
    w("CHECK the seven first near-misses pairwise disjoint: %d violations" % sum(not r['disjoint'] for r in recs))
    w("E174 place of t*: %s" % dict(Counter(r['place'] for r in recs)))
    w("d_min: %s" % dict(sorted(Counter(r['S'][0] for r in recs).items())))
    w("R* = 8 d_min t*: %s" % dict(Counter(str(r['R']) for r in recs).most_common(15)))
    w("moves from the bound: %s" % dict(sorted(Counter(len(r['moves']) for r in recs).items())))
    w("near-misses before t* (all runners, all intervals): %s" % dict(sorted(Counter(len(r['allnm']) for r in recs).items())))
    w("time order of the first near-misses, by rank of the blocker (top 12): %s" %
      Counter(tuple(r['order']) for r in recs).most_common(12))
    w("blocker's lap k in its first near-miss, by rank: %s" %
      {mi: dict(sorted(Counter(r['first'][mi]['k'] for r in recs).items())) for mi in range(7)})
    w("first near-misses visited by the cascade (a move time inside): %d of %d" %
      (sum(1 for r in recs for mi in range(7) if r['first'][mi]['visited']), 7 * len(recs)))
    w("sets where the cascade visits all seven first near-misses: %d" %
      sum(all(r['first'][mi]['visited'] for mi in range(7)) for r in recs))
    w("t* host rank: %s; closer rank: %s" % (dict(sorted(Counter(r['host'] for r in recs).items())),
                                             dict(sorted(Counter(r['closer'] for r in recs).items()))))
    w("\ntraces (first 12): readings; t*, R*; moves (t, in the way, setter); first near-misses in time order"
      " (blocker, lap k, [a, b], opener, closer, slacks, visited by move #)")
    for r in recs[:12]:
        w("\n%s  t* = %s  R* = %s  host %s closer %s  place %s" % (r['S'], r['ts'], r['R'], r['S'][r['host']],
                                                                   r['S'][r['closer']], r['place']))
        for t, way, st, nx in r['moves']:
            w("   move at %s: in the way %s, setter %s -> %s" % (t, way, st, nx))
        for mi in r['order']:
            f = r['first'][mi]
            w("   near-miss of %2d (lap %d): [%s, %s] opened by %s closed by %s, slacks %s, %s; visited %s" %
              (r['S'][mi], f['k'], f['a'], f['b'], f['opener'], f['closer'], f['s1'], f['s2'], f['visited']))
    o.close()
    print(open('swallow_971_v1.out').read()[len(__doc__):][:6000])
