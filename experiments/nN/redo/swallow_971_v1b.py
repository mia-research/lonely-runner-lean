"""E187b (2026-09-30): the 971 of E185, second pass -- the cascade's moves as a chain of near-misses, the blocker at
its own return, and the target's event at the host.

Reads swallow_971_v1_sets.json (the 971, written by swallow_971_v1.py).  Exact.  Records, per set:
  * single-blocker moves: moves of the cascade (from the bound) at which exactly ONE reading is in the way.  Derived:
    such a move time lies in a clear interval of the other six; either that interval stays inside the blocker's slot (a
    near-miss, visited) or the blocker's opening is the landing t*.  Checked: every single-blocker move before the last
    is inside a near-miss of its blocker; the last move's blocker opening is t*.
  * the blocker at its own return: for each first near-miss of a reading m >= the second slowest, on lap k, whether
    it contains k/m (m exactly at the subject).  There the six others' readings are (d k mod m)/m, so the six are clear
    at k/m exactly when every other d has (d k mod m)/m in [1/8, 7/8] -- a residue statement mod m; checked both ways.
  * the target's event at the host: hosts = readings opening at t* (phase 1/8).  Derived: with ONE host h, the six
    others are clear on [c, t*] with c inside h's slot (h entering its slot at a clear instant of the six would make
    the seven clear before t*).  Recorded: c, the reading(s) opening at c (the last opener), whether the cascade has a
    move at c, and h's lap.
  * E175's full place (S2: the stretch at a rung a/q, q <= 8) for the sets E174 missed.
"""
import json, math
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from quantity_tests_v1 import cd, E8
from wave_incident_v1 import lonely_components
from swallow_971_v1 import analyse, frac
from place_768_v1 import place_full


def second(S):
    r = analyse(S)
    ts, moves = r['ts'], r['moves']
    nm = {mi: [c for c in lonely_components([d for d in S if d != S[mi]], F(0), ts) if c[1] > 0 and c[1] < ts]
          for mi in range(7)}
    single = [(i, way[0]) for i, (t, way, st, nx) in enumerate(moves) if len(way) == 1]
    ok_chain = True
    for i, m in single:
        t, way, st, nx = moves[i]
        inside = any(a <= t <= b for a, b in nm[S.index(m)])
        ok_chain &= (inside or nx == ts)
    last_single = moves[-1][1] if moves else ()
    ret = []
    for mi in range(1, 7):
        m = S[mi]; f = r['first'][mi]; k = f['k']
        centre = F(k, m)
        contains = f['a'] <= centre <= f['b']
        residue = all(E8 <= F((d * k) % m, m) <= F(7, 8) for d in S if d != m)
        ret.append((mi, k, contains, residue))
    hosts = [d for d in S if frac(d * ts) == E8]
    host = None
    if len(hosts) == 1:
        h = hosts[0]
        comp = next(c for c in lonely_components([d for d in S if d != h], F(0), ts + 1) if c[0] <= ts <= c[1])
        c0 = comp[0]
        K = math.floor(h * ts)
        in_slot = (K - E8) / h < c0
        last_open = [d for d in S if d != h and frac(d * c0) == E8]
        host = dict(h=S.index(h), K=K, c=c0, in_slot=in_slot, last_open=[S.index(d) for d in last_open],
                    move_at_c=any(t == c0 for t, *_ in moves))
    pf = place_full(S) if r['place'][0] == 'miss' else r['place']
    return dict(S=S, n=len(moves), n_single=len(single), ok_chain=ok_chain, last_single=(len(last_single) == 1),
                ret=ret, hosts=len(hosts), host=host, pf=pf)


if __name__ == '__main__':
    sets = [tuple(S) for S in json.load(open('swallow_971_v1_sets.json'))]
    with Pool(8) as pool:
        recs = pool.map(second, sets)
    o = open('swallow_971_v1b.out', 'w'); o.write(__doc__ + "\n")
    w = lambda s: o.write(s + "\n")
    w("sets: %d" % len(recs))
    w("CHECK every single-blocker move is inside a near-miss of its blocker or exits to t*: %d violations" %
      sum(not r['ok_chain'] for r in recs))
    w("moves from the bound, all: %d; with exactly one reading in the way: %d" %
      (sum(r['n'] for r in recs), sum(r['n_single'] for r in recs)))
    w("sets where EVERY move has exactly one reading in the way (the cascade a chain of near-misses): %d" %
      sum(r['n'] == r['n_single'] for r in recs))
    w("sets whose last move has one reading in the way: %d" % sum(r['last_single'] for r in recs))
    rows = [x for r in recs for x in r['ret']]
    w("\nfirst near-misses of ranks 1..6: %d" % len(rows))
    w("  containing k/m (the blocker exactly at the subject): %d" % sum(x[2] for x in rows))
    w("CHECK contains k/m  <=>  residue statement mod m (every other d: (d k mod m)/m in [1/8, 7/8]): %d violations" %
      sum(1 for x in rows if x[2] != x[3]))
    w("  containing k/m, by lap k: %s" % dict(sorted(Counter(x[1] for x in rows if x[2]).items())))
    w("  not containing k/m, by lap k: %s" % dict(sorted(Counter(x[1] for x in rows if not x[2]).items())))
    w("\nhosts at t* (readings opening there): %s" % dict(sorted(Counter(r['hosts'] for r in recs).items())))
    H = [r for r in recs if r['host']]
    w("single host: %d; CHECK c inside the host's slot (derived): %d violations" %
      (len(H), sum(not r['host']['in_slot'] for r in H)))
    w("  host rank: %s" % dict(sorted(Counter(r['host']['h'] for r in H).items())))
    w("  host lap K: %s" % dict(sorted(Counter(r['host']['K'] for r in H).items())))
    w("  last opener at c (rank): %s" % dict(sorted(Counter(tuple(r['host']['last_open']) for r in H).items())))
    w("  cascade has a move at c: %d of %d" % (sum(r['host']['move_at_c'] for r in H), len(H)))
    w("\nplace of t*, E174 + E175 S2: %s" % dict(Counter((r['pf'][0], str(r['pf'][1])) for r in recs).most_common(20)))
    w("unplaced (E175's 768): %s" % [r['S'] for r in recs if r['pf'][0] == 'unplaced'][:30])
    o.close()
    print(open('swallow_971_v1b.out').read()[len(__doc__):])
