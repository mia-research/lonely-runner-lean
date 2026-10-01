"""E228/E229 (2026-10-01): D3, the pinned pair at the grid instant.  Design: log E228.

Whole-number readings at the subject's own grid instant t0 = 1/8 (reading d at position d eighths), with a captured
reading (d = 0 mod 8), a leaving-edge reading (d = 1 mod 8) and an entering-edge reading (d = 7 mod 8): GridNudgeN's
pinned pair, with something captured so the pair law does not apply.  The cascade is run from t0 (it lands at the first
lonely instant at or after t0, A.1).  Checks (pass condition 0 failures): F-2 the first move is the slowest captured
reading's exit 1/8 + 1/(8c*); F-3 the landing is lambda/8 with lambda = (8K+1)/h for its setter h, and the first-lap
formula (h+1)/h (captured), (h+8)/h (E1), (h+9-r)/h (r = 2..7) plus 8j/h with j >= 0 whole; C1 the landing equals the
least clear point at or after t0 computed without the cascade.  Records: the landing's role (captured, E7, interior,
E1), j, the number of moves; every set with j > 0 listed.
"""
import sys, math, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
from quantity_tests_v1 import cd, E8, next_opening


def run_from(S, t):
    moves = []
    while True:
        way = [d for d in S if cd(d * t) < E8]
        if not way:
            return t, moves
        nx = max(next_opening(d, t) for d in way)
        st = [d for d in way if next_opening(d, t) == nx]
        moves.append((t, tuple(way), tuple(st), nx))
        t = nx


def wanted(S):
    r = {d % 8 for d in S}
    return 0 in r and 1 in r and 7 in r


def study(S):
    S = tuple(sorted(S)); t0 = F(1, 8)
    C = [d for d in S if d % 8 == 0]; cs = min(C)
    ts, moves = run_from(S, t0)
    chk = Counter()
    if set(moves[0][1]) != set(C) or moves[0][3] != t0 + F(1, 8 * cs):
        chk['F-2'] += 1
    h = min(moves[-1][2]); K = (8 * h * ts - 1) / 8
    lam = 8 * ts
    if K.denominator != 1 or lam != (8 * K + 1) / h:
        chk['F-3 opening'] += 1
    r = h % 8
    base = {0: F(h + 1, h), 1: F(h + 8, h)}.get(r, F(h + 9 - r, h))
    jj = (lam - base) * h / 8
    if jj.denominator != 1 or jj < 0:
        chk['F-3 first-lap formula'] += 1
    least = clear_set([F(d) for d in S], F(1), max(F(40), 8 * ts + 1))[0][0]
    if least != 8 * ts:
        chk['C1'] += 1
    role = {0: 'captured', 1: 'E1', 7: 'E7'}.get(r, 'interior r=%d' % r)
    first_move_lands = (len(moves) == 1)
    return dict(S=S, role=role, j=int(jj), moves=len(moves), chk=chk, first=first_move_lands,
                h_is_cstar=(h == cs), lam=lam)


def run(sets):
    return [study(S) for S in sets]


def report(name, rows, w):
    w("\n== %s: %d sets ==" % (name, len(rows)))
    ck = Counter()
    for r in rows:
        ck.update(r['chk'])
    w("  CHECKS (F-2, F-3, C1): %s" % (dict(ck) if ck else '0 failures'))
    w("  landing at the first move (the slowest captured reading's exit): %d" % sum(r['first'] for r in rows))
    w("  landing role (whose exit holds the isolation): %s" % dict(Counter(r['role'] for r in rows).most_common()))
    w("  extra laps j of the landing's setter: %s" % dict(sorted(Counter(r['j'] for r in rows).items())))
    w("  moves from the grid instant: %s" % dict(sorted(Counter(r['moves'] for r in rows).items())))
    jx = [r for r in rows if r['j'] > 0]
    w("  sets with j > 0 (%d), listed: %s" % (len(jx), [(r['S'], r['role'], r['j']) for r in jx[:40]]))


if __name__ == '__main__':
    out = open('d3_pinned_pair_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    p1 = [S for S in itertools.combinations(range(1, 25), 7) if wanted(S)]
    rng = random.Random(228); p2 = set()
    while len(p2) < 3000:
        S = tuple(sorted(rng.sample(range(1, 65), 7)))
        if wanted(S):
            p2.add(S)
    with Pool(8) as pool:
        for name, pop in (('every 7-set of readings <= 24 with the pinned pair and a captured reading', p1),
                          ('3,000 seeded such sets of readings <= 64', sorted(p2))):
            rows = [x for part in pool.map(run, [pop[i::64] for i in range(64)]) for x in part]
            report(name, rows, w)
    out.close()
    print(open('d3_pinned_pair_v1.out').read()[len(__doc__):])
