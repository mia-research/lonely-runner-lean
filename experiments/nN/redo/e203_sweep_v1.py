"""E203 (2026-09-30): why the sweep ends: designed in the cascade's own terms, then run.

Owner: "Thats ok, we want each step to move us closer.  We already have the cascade so figuring how how it is doing it is
important step towards why is it forced.  yes, design why the sweep ends first, then run it".

DESIGN (the cascade's chain, grouped by clusters; units R = 8 d_min t)
  Clusters.  On lap k a CLUSTER is a maximal run of consecutive readings with ratio below rho_k = (8k+1)/(8k-1) (lap 0
  read as rho_1, E145).  Forced by ordering (E142, E143; `SweepBridgeN`): a same-lap sweep can only go down through such a
  run, and it stops at the run's bottom.
  PASSAGE: consecutive moves whose setters lie in one lap-k cluster: the cluster going through the subject's slot, its
  members exiting in descending speed order (derived: faster members are further ahead).
  BRIDGE: two consecutive passages; at one cluster bottom's exit a reading of another cluster (or of the same cluster on
  another lap) is already in the slot.  Up (to a faster cluster) or down.
  THE END: the landing is a cluster bottom's exit at which no other cluster is partway through the slot (E143, forced):
  a gap between passages, bounded by a bottom's exit and the next top's entry: an isolation event in the owner's terms.
  So "why the sweep ends" is: why the passages stop linking.  Two things decide it and are recorded:
    (a) the BRIDGES: at each, how the next cluster came to be in the slot (its grid slot at the preceding instant and
        its deviation), and whether it was faster or slower;
    (b) REVISITS: whether a chain ever passes the same cluster on a later lap (a cluster obstructing twice).
  Frame checks (the checklist): the object is the cascade's chain, grouped; no statement about how much time the clusters
  cover (the other frame); revisits and passages are recorded, never bounded as an argument; no instant family; no first
  isolation; every exception listed.
RUN (exact).  Per chain: its passages (cluster members, lap, number of moves in it), its bridges (up/down, the next
cluster's slot at the bridging instant), revisits, and (derived checks) moves inside a passage go down in speed; the
landing is a cluster bottom's exit.  Populations as E201/E202, restricted to chains (at least one move).
"""
import sys, math, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from quantity_tests_v1 import cd, E8, next_opening
from e151_block_v1 import slow_part, trace


def rho(k):
    k = max(k, 1)
    return F(8 * k + 1, 8 * k - 1)


def cluster_of(S, s, k):
    X = sorted(S); i = X.index(s); lo = hi = i
    r = rho(k)
    while lo > 0 and F(X[lo], X[lo - 1]) < r:
        lo -= 1
    while hi < len(X) - 1 and F(X[hi + 1], X[hi]) < r:
        hi += 1
    return tuple(X[lo:hi + 1])


def eighth_slot(x):
    y = 8 * (x - math.floor(x))
    return math.floor(y)


def study(S):
    S = tuple(sorted(S)); d0 = S[0]
    ts, moves = trace(S)
    if not moves:
        return None
    P = slow_part(S)
    steps = []
    for t, way, st, nx in moves:
        s = min(st)                                   # the setter (ties: the slowest)
        k = round(s * nx - F(1, 8))                   # nx = (k + 1/8)/s
        steps.append(dict(t=t, s=s, k=k, cl=cluster_of(S, s, k), way=way, nx=nx))
    passages = []
    for st in steps:
        if passages and passages[-1]['cl'] == st['cl'] and passages[-1]['k'] == st['k']:
            passages[-1]['moves'].append(st)
        else:
            passages.append(dict(cl=st['cl'], k=st['k'], moves=[st]))
    desc_ok = all(all(a['s'] >= b['s'] for a, b in zip(p['moves'], p['moves'][1:])) for p in passages)
    last = passages[-1]
    bottom_ok = min(last['cl']) == last['moves'][-1]['s']
    bridges = []
    for p, q in zip(passages, passages[1:]):
        t_b = q['moves'][0]['t']                        # the bridging instant: the previous passage's last exit
        nxt = min(q['cl'])
        up = min(q['cl']) > min(p['cl'])
        slots = sorted({eighth_slot(d * p['moves'][-1]['t']) for d in q['cl']})
        bridges.append(dict(up=up, same_cluster=(q['cl'] == p['cl']), slots=tuple(slots)))
    seen = {}; revisits = 0
    for p in passages:
        if p['cl'] in seen and seen[p['cl']] != p['k']:
            revisits += 1
        seen.setdefault(p['cl'], p['k'])
    return dict(S=S, P=tuple(P), n_moves=len(moves), n_pass=len(passages), bridges=bridges, revisits=revisits,
                desc_ok=desc_ok, bottom_ok=bottom_ok, R=8 * d0 * ts,
                shape=[(len(p['cl']), p['k'], len(p['moves'])) for p in passages])


def chunk(first):
    return [r for r in (study((first,) + rest) for rest in itertools.combinations(range(first + 1, 25), 6)) if r]


def report(name, rows, w):
    rows = [r for r in rows if r]
    w("\n== %s: %d chains ==" % (name, len(rows)))
    w("  CHECK moves inside a passage go down in speed (derived): %d violations" % sum(not r['desc_ok'] for r in rows))
    w("  CHECK the landing is the last passage's cluster bottom's exit (E143, forced): %d violations" % sum(not r['bottom_ok'] for r in rows))
    w("  passages per chain: %s" % dict(sorted(Counter(r['n_pass'] for r in rows).items())))
    br = [b for r in rows for b in r['bridges']]
    w("  bridges: %d; up %d, down %d; to the same cluster on another lap %d" %
      (len(br), sum(b['up'] for b in br), sum(not b['up'] and not b['same_cluster'] for b in br), sum(b['same_cluster'] for b in br)))
    w("  chains with a revisit (a cluster passing on a second lap): %d" % sum(1 for r in rows if r['revisits']))
    w("  the next cluster's eighth-slots at the bridging instant (top 12): %s" % Counter(b['slots'] for b in br).most_common(12))
    w("  chain shapes (cluster size, lap, moves) most common: %s" % Counter(tuple(r['shape']) for r in rows).most_common(8))
    rv = [r for r in rows if r['revisits']]
    for r in rv[:15]:
        w("    revisit: %s P %s moves %d passages %s R* %s" % (r['S'], r['P'], r['n_moves'], r['shape'], r['R']))


if __name__ == '__main__':
    sys.path.insert(0, '.')
    from coverB_fine_v1 import late_shapes
    out = open('e203_sweep_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    rng = random.Random(13); cc1 = []
    while len(cc1) < 1000:
        T = tuple(sorted(rng.sample(range(1, 201), 7)))
        if T[-1] > 24 * T[0]:
            cc1.append(T)
    rng = random.Random(29); cc2 = []
    while len(cc2) < 1000:
        T = tuple(sorted(rng.sample(range(1, 5001), 7)))
        if T[-1] > 24 * T[0]:
            cc2.append(T)
    with Pool(8) as pool:
        report('every 7-set of readings in 1..24', [r for part in pool.map(chunk, range(1, 19)) for r in part], w)
        report('late fine band shapes', pool.map(study, late_shapes()), w)
        report('Case C, readings <= 200 (seed 13)', pool.map(study, cc1), w)
        report('Case C, readings <= 5,000 (seed 29)', pool.map(study, cc2), w)
    out.close()
    print(open('e203_sweep_v1.out').read()[len(__doc__):][:9000])
